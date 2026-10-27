module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathPlane
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped commutatorElement

section Family

variable {W : Type*} [CommGroup W] {ι : Type*}

structure PlaneFamily (I : ι → Subgroup W) : Prop where
  exp_two : ∀ w : W, w * w = 1
  klein : ∀ i, IsKleinFour ↥(I i)
  indep : iSupIndep I
  sup_eq_top : ⨆ i, I i = ⊤

variable {I : ι → Subgroup W}

namespace PlaneFamily

variable (hF : PlaneFamily I)

include hF in
theorem card_I (i : ι) : Nat.card ↥(I i) = 4 := (hF.klein i).card_four

include hF in
theorem I_ne_bot (i : ι) : I i ≠ ⊥ := fun h => by
  have := hF.card_I i
  rw [h, Subgroup.card_bot] at this
  omega

include hF in
theorem injective : Function.Injective I := by
  intro i j hij
  by_contra hne
  have hd : Disjoint (I i) (I j) := hF.indep.pairwiseDisjoint hne
  rw [hij] at hd
  exact hF.I_ne_bot j (disjoint_self.mp hd)

theorem hcomm : Pairwise fun i j : ι => ∀ x y : W, x ∈ I i → y ∈ I j → Commute x y :=
  fun _ _ _ x y _ _ => Commute.all x y

variable [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def coordEquiv : (∀ i, ↥(I i)) ≃* W :=
  MulEquiv.ofBijective (Subgroup.noncommPiCoprod (H := I) hcomm)
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hF.indep, by
      rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]
      exact hF.sup_eq_top⟩

theorem coordEquiv_mulSingle (i : ι) (x : ↥(I i)) : hF.coordEquiv (Pi.mulSingle i x) = (x : W) :=
  Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i x

omit [DecidableEq ι] in
theorem coordEquiv_apply (u : ∀ i, ↥(I i)) : (hF.coordEquiv u : W) = ∏ i, (u i : W) := by
  show Subgroup.noncommPiCoprod (H := I) hcomm u = _
  rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]

@[expose] noncomputable def coord (i : ι) : W →* ↥(I i) :=
  (Pi.evalMonoidHom (fun i => ↥(I i)) i).comp hF.coordEquiv.symm.toMonoidHom

theorem coord_of_mem {j : ι} {c : W} (hc : c ∈ I j) (i : ι) :
    ((hF.coord i c : ↥(I i)) : W) = if i = j then c else 1 := by
  have h : hF.coordEquiv.symm c = Pi.mulSingle j ⟨c, hc⟩ := by
    rw [MulEquiv.symm_apply_eq, coordEquiv_mulSingle]
  show ((hF.coordEquiv.symm c) i : W) = _
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Pi.mulSingle_eq_of_ne hij]
    simp [hij]

omit [DecidableEq ι] in
theorem eq_prod_coord (c : W) : c = ∏ i, ((hF.coord i c : ↥(I i)) : W) := by
  have h := hF.coordEquiv_apply (hF.coordEquiv.symm c)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

omit [DecidableEq ι] in
theorem eq_of_coord_eq {c d : W} (h : ∀ i, hF.coord i c = hF.coord i d) : c = d := by
  rw [hF.eq_prod_coord c, hF.eq_prod_coord d]
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

end PlaneFamily

variable [Fintype ι] [DecidableEq ι]

open scoped Pointwise

@[expose] def permuting (I : ι → Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | (∀ i, ∃ j, g • I i = I j) ∧ ∀ i, ∃ j, g⁻¹ • I i = I j}
  one_mem' := ⟨fun i => ⟨i, one_smul _ _⟩, fun i => ⟨i, by simp⟩⟩
  mul_mem' := fun {g h} hg hh => ⟨fun i => by
      obtain ⟨j, hj⟩ := hh.1 i
      obtain ⟨k, hk⟩ := hg.1 j
      exact ⟨k, by rw [mul_smul, hj, hk]⟩,
    fun i => by
      obtain ⟨j, hj⟩ := hg.2 i
      obtain ⟨k, hk⟩ := hh.2 j
      exact ⟨k, by rw [mul_inv_rev, mul_smul, hj, hk]⟩⟩
  inv_mem' := fun {g} hg => ⟨hg.2, by simpa using hg.1⟩

omit [DecidableEq ι] in
theorem mem_permuting_iff (hF : PlaneFamily I) {g : MulAut W} :
    g ∈ permuting I ↔ ∀ i, ∃ j, g • I i = I j := by
  refine ⟨fun h => h.1, fun hg => ⟨hg, ?_⟩⟩
  choose σ hσ using hg
  have hinj : Function.Injective σ := by
    intro i j hij
    apply hF.injective
    have h1 : g • I i = g • I j := by rw [hσ i, hσ j, hij]
    exact smul_left_cancel g h1
  have hsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hinj
  intro i
  obtain ⟨i', hi'⟩ := hsurj i
  refine ⟨i', ?_⟩
  rw [inv_smul_eq_iff, hσ i', hi']

omit [DecidableEq ι] in
theorem exists_perm (hF : PlaneFamily I) {g : MulAut W} (hg : g ∈ permuting I) :
    ∃! σ : Equiv.Perm ι, ∀ i, g • I i = I (σ i) := by
  have hg' := (mem_permuting_iff hF).mp hg
  choose σ hσ using hg'
  have hinj : Function.Injective σ := by
    intro i j hij
    apply hF.injective
    have h1 : g • I i = g • I j := by rw [hσ i, hσ j, hij]
    exact smul_left_cancel g h1
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective σ hbij, fun i => hσ i, fun τ hτ => ?_⟩
  apply Equiv.ext
  intro i
  apply hF.injective
  rw [← hτ i, hσ i]
  rfl

@[expose] noncomputable def permHom (hF : PlaneFamily I) : ↥(permuting I) →* Equiv.Perm ι where
  toFun g := (exists_perm hF g.2).exists.choose
  map_one' := by
    refine ((exists_perm hF (one_mem (permuting I))).unique
      (exists_perm hF (one_mem (permuting I))).exists.choose_spec ?_)
    intro i
    exact one_smul _ _
  map_mul' g h := by
    refine (exists_perm hF (mul_mem g.2 h.2)).unique
      (exists_perm hF (mul_mem g.2 h.2)).exists.choose_spec ?_
    intro i
    have hg := (exists_perm hF g.2).exists.choose_spec
    have hh := (exists_perm hF h.2).exists.choose_spec
    show ((g : MulAut W) * (h : MulAut W)) • I i = _
    rw [mul_smul, hh i, hg]
    rfl

omit [DecidableEq ι] in
theorem permHom_spec (hF : PlaneFamily I) (g : ↥(permuting I)) (i : ι) :
    (g : MulAut W) • I i = I (permHom hF g i) :=
  (exists_perm hF g.2).exists.choose_spec i

omit [DecidableEq ι] in
theorem permHom_eq_iff (hF : PlaneFamily I) (g : ↥(permuting I)) (σ : Equiv.Perm ι) :
    permHom hF g = σ ↔ ∀ i, (g : MulAut W) • I i = I (σ i) := by
  constructor
  · rintro rfl
    exact permHom_spec hF g
  · intro h
    exact (exists_perm hF g.2).unique (permHom_spec hF g) h

@[expose] def baseGp (I : ι → Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ i, g • I i = I i}
  one_mem' := fun i => one_smul _ _
  mul_mem' := fun {g h} hg hh i => by rw [mul_smul, hh i, hg i]
  inv_mem' := fun {g} hg i => by rw [inv_smul_eq_iff, hg i]

omit [Fintype ι] [DecidableEq ι] in
theorem mem_baseGp {I : ι → Subgroup W} {g : MulAut W} : g ∈ baseGp I ↔ ∀ i, g • I i = I i :=
  Iff.rfl

omit [DecidableEq ι] in
theorem baseGp_le_permuting (hF : PlaneFamily I) : baseGp I ≤ permuting I := fun _ hg =>
  (mem_permuting_iff hF).mpr fun i => ⟨i, hg i⟩

omit [DecidableEq ι] in
theorem mem_baseGp_iff_permHom (hF : PlaneFamily I) {g : MulAut W} :
    g ∈ baseGp I ↔ ∃ h : g ∈ permuting I, permHom hF ⟨g, h⟩ = 1 := by
  constructor
  · intro hg
    refine ⟨baseGp_le_permuting hF hg, ?_⟩
    rw [permHom_eq_iff]
    intro i
    exact hg i
  · rintro ⟨h, h1⟩ i
    have := (permHom_eq_iff hF ⟨g, h⟩ 1).mp h1 i
    simpa using this

@[expose] noncomputable def wreathAut (hF : PlaneFamily I) (Pm : Subgroup (Equiv.Perm ι)) :
    Subgroup (MulAut W) :=
  (Pm.comap (permHom hF)).map (permuting I).subtype

omit [DecidableEq ι] in
theorem mem_wreathAut_iff (hF : PlaneFamily I) {Pm : Subgroup (Equiv.Perm ι)} {g : MulAut W} :
    g ∈ wreathAut hF Pm ↔ ∃ σ ∈ Pm, ∀ i, g • I i = I (σ i) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨permHom hF x, hx, permHom_spec hF x⟩
  · rintro ⟨σ, hσ, h⟩
    have hg : g ∈ permuting I := (mem_permuting_iff hF).mpr fun i => ⟨σ i, h i⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show permHom hF ⟨g, hg⟩ ∈ Pm
    rw [(permHom_eq_iff hF ⟨g, hg⟩ σ).mpr h]
    exact hσ

omit [DecidableEq ι] in
theorem baseGp_le_wreathAut (hF : PlaneFamily I) (Pm : Subgroup (Equiv.Perm ι)) :
    baseGp I ≤ wreathAut hF Pm := fun g hg =>
  (mem_wreathAut_iff hF).mpr ⟨1, one_mem _, fun i => by simpa using hg i⟩

omit [DecidableEq ι] in
theorem wreathAut_le_permuting (hF : PlaneFamily I) (Pm : Subgroup (Equiv.Perm ι)) :
    wreathAut hF Pm ≤ permuting I := fun g hg => by
  obtain ⟨σ, -, h⟩ := (mem_wreathAut_iff hF).mp hg
  exact (mem_permuting_iff hF).mpr fun i => ⟨σ i, h i⟩

theorem coord_perm (hF : PlaneFamily I) {g : MulAut W} {σ : Equiv.Perm ι}
    (hσ : ∀ i, g • I i = I (σ i)) (i : ι) (c : W) :
    ((hF.coord (σ i) (g c) : ↥(I (σ i))) : W) = g ((hF.coord i c : ↥(I i)) : W) := by
  have hmem : ∀ j, ∀ x ∈ I j, g x ∈ I (σ j) := fun j x hx => by
    rw [← hσ j]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hx, rfl⟩
  have hc : c ∈ ⨆ j, I j := by rw [hF.sup_eq_top]; exact Subgroup.mem_top c
  refine Subgroup.iSup_induction I hc (C := fun c =>
    ((hF.coord (σ i) (g c) : ↥(I (σ i))) : W) = g ((hF.coord i c : ↥(I i)) : W)) ?_ ?_ ?_
  · intro j x hx
    rw [hF.coord_of_mem hx i, hF.coord_of_mem (hmem j x hx) (σ i)]
    by_cases hij : i = j
    · subst hij
      simp
    · have : σ i ≠ σ j := fun h => hij (σ.injective h)
      simp [hij, this]
  · simp
  · intro x y hx hy
    simp only [map_mul, Subgroup.coe_mul, hx, hy]

omit [Fintype ι] [DecidableEq ι] in
theorem smul_mem_of_smul_eq {H : Subgroup W} {g : MulAut W} (h : g • H = H) {x : W} (hx : x ∈ H) :
    g x ∈ H := by
  rw [← h]
  exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hx, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem inv_smul_mem_of_smul_eq {H : Subgroup W} {g : MulAut W} (h : g • H = H) {x : W}
    (hx : x ∈ H) : g⁻¹ x ∈ H := by
  have h' : g⁻¹ • H = H := by rw [inv_smul_eq_iff, h]
  exact smul_mem_of_smul_eq h' hx

@[expose] def restrictAut (H : Subgroup W) (g : MulAut W) (h : g • H = H) : MulAut ↥H where
  toFun x := ⟨g x, smul_mem_of_smul_eq h x.2⟩
  invFun x := ⟨g⁻¹ x, inv_smul_mem_of_smul_eq h x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

omit [Fintype ι] [DecidableEq ι] in
theorem restrictAut_mul (H : Subgroup W) (g g' : MulAut W) (h : g • H = H) (h' : g' • H = H)
    (hm : (g * g') • H = H) :
    restrictAut H (g * g') hm = restrictAut H g h * restrictAut H g' h' := by
  ext x
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem restrictAut_one (H : Subgroup W) (h : (1 : MulAut W) • H = H) :
    restrictAut H 1 h = 1 := by
  ext x
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem restrictAut_eq_one_iff (H : Subgroup W) (g : MulAut W) (h : g • H = H) :
    restrictAut H g h = 1 ↔ ∀ x ∈ H, g x = x := by
  constructor
  · intro h1 x hx
    have := congrArg (fun a : MulAut ↥H => ((a ⟨x, hx⟩ : ↥H) : W)) h1
    exact this
  · intro h1
    ext x
    exact h1 x x.2

@[expose] def resPlane (I : ι → Subgroup W) (i : ι) : ↥(baseGp I) →* MulAut ↥(I i) where
  toFun g := restrictAut (I i) g (g.2 i)
  map_one' := restrictAut_one _ _
  map_mul' g g' := restrictAut_mul _ _ _ (g.2 i) (g'.2 i) _

omit [Fintype ι] [DecidableEq ι] in
theorem PlaneFamily.autEq_of_forall_plane (hF : PlaneFamily I) {g g' : MulAut W}
    (h : ∀ i, ∀ x ∈ I i, g x = g' x) : g = g' := by
  apply MulEquiv.ext
  intro c
  have hc : c ∈ ⨆ j, I j := by rw [hF.sup_eq_top]; exact Subgroup.mem_top c
  refine Subgroup.iSup_induction I hc (C := fun c => g c = g' c) ?_ ?_ ?_
  · exact h
  · simp
  · intro x y hx hy
    rw [map_mul, map_mul, hx, hy]

omit [Fintype ι] [DecidableEq ι] in
theorem resPlane_injective (hF : PlaneFamily I) :
    Function.Injective (MonoidHom.pi (resPlane I)) := by
  intro g g' h
  apply Subtype.ext
  apply hF.autEq_of_forall_plane
  intro i x hx
  have h1 : resPlane I i g = resPlane I i g' := congrFun h i
  have := congrArg (fun a : MulAut ↥(I i) => ((a ⟨x, hx⟩ : ↥(I i)) : W)) h1
  simpa [resPlane, restrictAut] using this

@[expose] noncomputable def PlaneFamily.blockAut (hF : PlaneFamily I) (β : ∀ i, MulAut ↥(I i)) :
    MulAut W :=
  hF.coordEquiv.symm.trans ((MulEquiv.piCongrRight β).trans hF.coordEquiv)

theorem PlaneFamily.blockAut_apply (hF : PlaneFamily I) (β : ∀ i, MulAut ↥(I i)) {j : ι} {x : W}
    (hx : x ∈ I j) : hF.blockAut β x = ((β j ⟨x, hx⟩ : ↥(I j)) : W) := by
  have h : hF.coordEquiv.symm x = Pi.mulSingle j ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq, hF.coordEquiv_mulSingle]
  show hF.coordEquiv ((MulEquiv.piCongrRight β) (hF.coordEquiv.symm x)) = _
  rw [h]
  have h2 : (MulEquiv.piCongrRight β) (Pi.mulSingle j (⟨x, hx⟩ : ↥(I j))) =
      (Pi.mulSingle j (β j ⟨x, hx⟩) : ∀ k, ↥(I k)) := by
    funext k
    show β k ((Pi.mulSingle j (⟨x, hx⟩ : ↥(I j)) : ∀ k, ↥(I k)) k) =
      (Pi.mulSingle j (β j ⟨x, hx⟩) : ∀ k, ↥(I k)) k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Pi.mulSingle_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk, map_one]
  rw [h2, hF.coordEquiv_mulSingle]

theorem PlaneFamily.blockAut_smul (hF : PlaneFamily I) (β : ∀ i, MulAut ↥(I i)) (i : ι) :
    hF.blockAut β • I i = I i := by
  ext z
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    show hF.blockAut β x ∈ I i
    rw [hF.blockAut_apply β hx]
    exact (β i ⟨x, hx⟩).2
  · intro hz
    obtain ⟨y, hy⟩ := (β i).surjective ⟨z, hz⟩
    refine ⟨(y : W), y.2, ?_⟩
    show hF.blockAut β (y : W) = z
    rw [hF.blockAut_apply β y.2]
    exact congrArg Subtype.val hy

theorem PlaneFamily.blockAut_mem (hF : PlaneFamily I) (β : ∀ i, MulAut ↥(I i)) :
    hF.blockAut β ∈ baseGp I := fun i => hF.blockAut_smul β i

theorem PlaneFamily.resPlane_blockAut (hF : PlaneFamily I) (β : ∀ i, MulAut ↥(I i)) (i : ι) :
    resPlane I i ⟨hF.blockAut β, hF.blockAut_mem β⟩ = β i := by
  ext x
  show hF.blockAut β x = _
  exact hF.blockAut_apply β x.2

theorem resPlane_surjective (hF : PlaneFamily I) : Function.Surjective (MonoidHom.pi (resPlane I)) :=
  fun β => ⟨⟨hF.blockAut β, hF.blockAut_mem β⟩, funext fun i => hF.resPlane_blockAut β i⟩

@[expose] noncomputable def blockEquiv (hF : PlaneFamily I) :
    ↥(baseGp I) ≃* (∀ i, MulAut ↥(I i)) :=
  MulEquiv.ofBijective (MonoidHom.pi (resPlane I)) ⟨resPlane_injective hF, resPlane_surjective hF⟩

end Family

end CFSG.QuasithinUnique.Setup.Wreath
