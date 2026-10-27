module

public import CFSG.LocalAnalysis.ComponentInitial.OddSymplecticSummand
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCentralizerTwo
public import CFSG.LocalAnalysis.ComponentInitial.CentralQuotientComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

abbrev spOp (g : sesqUnitaryGroup B) : Module.End K V :=
  ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)

@[expose] def centralizerSimEquiv (T : sesqUnitaryGroup B) :
    Subgroup.centralizer {T} ≃*
      similitudeCentralizer B (T : LinearMap.GeneralLinearGroup K V) where
  toFun x := ⟨((x : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V),
    (x : sesqUnitaryGroup B).2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2))⟩
  invFun g := ⟨⟨g, g.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem centralizerSimEquiv_coe (T : sesqUnitaryGroup B) (x : Subgroup.centralizer {T}) :
    ((centralizerSimEquiv T x : similitudeCentralizer B (T : LinearMap.GeneralLinearGroup K V)) :
      LinearMap.GeneralLinearGroup K V) =
      ((x : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) :=
  rfl

@[expose] def symplecticSummandSet (B : LinearMap.BilinForm K V) (A W : Submodule K V) :
    Set (sesqUnitaryGroup B) :=
  {g | (∀ w ∈ W, spOp g w = w) ∧ ∀ a ∈ A, spOp g a ∈ A}

section Components

variable [Finite K] {A : Type} [AddCommGroup A] [Module K A] [FiniteDimensional K A]

theorem eq_top_of_isComponent (hodd : Odd (Nat.card K)) {C : LinearMap.BilinForm K A}
    (hC : C.IsAlt) (hCnd : C.Nondegenerate) (hdim : 2 ≤ finrank K A)
    {L : Subgroup (sesqUnitaryGroup C)} (hL : CFSG.IsComponent L) : L = ⊤ := by
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  by_cases hex : finrank K A = 2 ∧ Nat.card K = 3
  · exfalso
    have h1 := CatalogueBAlternatingIsometry.plane_fieldThree_solvable C hC hCnd hex.1 hex.2
    have : Group.IsSolvable (sesqUnitaryGroup C) :=
      Group.isSolvable_of_surjective
        (f := (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv C).symm.toMonoidHom)
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv C).symm.surjective
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · have : Finite (sesqUnitaryGroup C) :=
      Finite.of_equiv _ (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv C).symm.toEquiv
    have hq := CatalogueBAlternatingIsometry.isometry_quasisimple C hC hCnd hdim hodd
      (not_and_or.mp hex)
    have hq' : CFSG.IsQuasisimple (⊤ : Subgroup (sesqUnitaryGroup C)) :=
      (isQuasisimple_congr (Subgroup.topEquiv.trans
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv C))).2 hq
    exact eq_of_isComponent_of_quasisimple hq' le_top hL

end Components

section Orth

variable (hB : B.IsAlt) {A W : Submodule K V} (hc : IsCompl A W)
  (horth : ∀ a ∈ A, ∀ w ∈ W, B a w = 0)

include hB horth in
theorem orthoSumForm_eq (x y : A × W) :
    orthoSumForm (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W) x y =
      B (Submodule.prodEquivOfIsCompl A W hc x) (Submodule.prodEquivOfIsCompl A W hc y) := by
  have h1 : B (x.2 : V) (y.1 : V) = 0 := by
    rw [← hB.neg_eq (y.1 : V) (x.2 : V), horth _ y.1.2 _ x.2.2, neg_zero]
  rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', orthoSumForm_apply,
    LinearMap.domRestrict₁₂_apply, LinearMap.domRestrict₁₂_apply]
  simp only [map_add, LinearMap.add_apply, horth _ x.1.2 _ y.2.2, h1]
  ring

include hB horth in
theorem glConj_mem_bilinIsometryGroup {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqUnitaryGroup B) :
    glConj (Submodule.prodEquivOfIsCompl A W hc) g ∈
      bilinIsometryGroup (orthoSumForm (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W)) := by
  intro x y
  rw [orthoSumForm_eq hB hc horth, orthoSumForm_eq hB hc horth, glConj_apply, glConj_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hg]

include hB horth in
theorem glConj_symm_oddSummandGL_mem {gA : LinearMap.GeneralLinearGroup K A}
    (hgA : gA ∈ bilinIsometryGroup (B.domRestrict₁₂ A A)) :
    ∃ hb : glConj (Submodule.prodEquivOfIsCompl A W hc).symm (oddSummandGL W gA) ∈
        sesqUnitaryGroup B,
      (⟨_, hb⟩ : sesqUnitaryGroup B) ∈ symplecticSummandSet B A W := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = Submodule.prodEquivOfIsCompl A W hc := ⟨_, rfl⟩
  rw [← hΨ]
  have happ : ∀ v, ((glConj Ψ.symm (oddSummandGL W gA) : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) v = Ψ ((oddSummandGL W gA : A × W →ₗ[K] A × W) (Ψ.symm v)) := fun v => by
    rw [glConj_apply, LinearEquiv.symm_symm]
  have hU : oddSummandGL W gA ∈
      bilinIsometryGroup (orthoSumForm (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W)) := by
    intro x y
    rw [oddSummandGL_apply, oddSummandGL_apply, orthoSumForm_apply, orthoSumForm_apply, hgA]
  have hb : glConj Ψ.symm (oddSummandGL W gA) ∈ sesqUnitaryGroup B := by
    intro x y
    rw [happ, happ, hΨ, ← orthoSumForm_eq hB hc horth, hU, orthoSumForm_eq hB hc horth,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine ⟨hb, fun w hw => ?_, fun a ha => ?_⟩
  · change ((glConj Ψ.symm (oddSummandGL W gA) : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) w = w
    rw [happ, hΨ, show (Submodule.prodEquivOfIsCompl A W hc).symm w = (0, ⟨w, hw⟩) from
      Submodule.prodEquivOfIsCompl_symm_apply_right A W hc ⟨w, hw⟩, oddSummandGL_apply, map_zero,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]
  · change ((glConj Ψ.symm (oddSummandGL W gA) : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) a ∈ A
    rw [happ, hΨ, show (Submodule.prodEquivOfIsCompl A W hc).symm a = (⟨a, ha⟩, 0) from
      Submodule.prodEquivOfIsCompl_symm_apply_left A W hc ⟨a, ha⟩, oddSummandGL_apply,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
    exact Submodule.coe_mem _

include hB hc horth in
theorem fix_of_le_centralizer_summand [Finite K] (hk : ringChar K ≠ 2) [FiniteDimensional K V]
    (hndA : (B.domRestrict₁₂ A A).Nondegenerate) (hndW : (B.domRestrict₁₂ W W).Nondegenerate)
    (hm : 2 ≤ finrank K A) {S : Subgroup (sesqUnitaryGroup B)}
    (hS : symplecticSummandSet B A W ⊆ S) {R : Subgroup (sesqUnitaryGroup B)}
    (hR : R ≤ Subgroup.centralizer (S : Set (sesqUnitaryGroup B))) (hRp : ⁅R, R⁆ = R) :
    ∀ g ∈ R, ∀ a ∈ A, spOp g a = a := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = Submodule.prodEquivOfIsCompl A W hc := ⟨_, rfl⟩
  have hAalt : (B.domRestrict₁₂ A A).IsAlt := fun x => hB x
  have hWalt : (B.domRestrict₁₂ W W).IsAlt := fun x => hB x
  obtain ⟨R', hR'⟩ : ∃ R' : Subgroup (LinearMap.GeneralLinearGroup K (A × W)),
      R' = (R.map (sesqUnitaryGroup B).subtype).map (glConj Ψ) := ⟨_, rfl⟩
  have hR'U : R' ≤ bilinIsometryGroup (orthoSumForm (B.domRestrict₁₂ A A)
      (B.domRestrict₁₂ W W)) ⊓ Subgroup.centralizer (symplecticSummand W
        (B.domRestrict₁₂ A A) : Set (LinearMap.GeneralLinearGroup K (A × W))) := by
    rw [hR']
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hΨ]
      exact glConj_mem_bilinIsometryGroup hB hc horth r.2
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨gA, hgA, rfl⟩
    obtain ⟨hb, hbS⟩ := glConj_symm_oddSummandGL_mem hB hc horth hgA
    have h1 := Subgroup.mem_centralizer_iff.mp (hR hr) _ (hS hbS)
    have h2 := congrArg (fun x : sesqUnitaryGroup B =>
      glConj Ψ ((x : LinearMap.GeneralLinearGroup K V))) h1
    simp only [Subgroup.coe_mul, map_mul] at h2
    have h3 : glConj Ψ (glConj Ψ.symm (oddSummandGL W gA)) = oddSummandGL W gA :=
      Units.ext (LinearMap.ext fun x => by
        rw [glConj_apply, glConj_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
          LinearEquiv.symm_apply_apply])
    rw [← hΨ, h3] at h2
    exact h2
  have hR'p : Group.IsPerfect R' :=
    Subgroup.isPerfect_iff.mpr (by rw [hR', ← Subgroup.map_commutator,
      ← Subgroup.map_commutator, hRp])
  have hfix := (natural_odd_symplectic_summand_centralizer hk hAalt hndA hWalt hndW hm).2.2.2
    R' hR'U hR'p
  intro g hg a ha
  have h1 := hfix _ (by rw [hR']; exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩) ⟨a, ha⟩
  rw [glConj_apply] at h1
  have h2 := congrArg Ψ h1
  rw [LinearEquiv.apply_symm_apply, hΨ, Submodule.coe_prodEquivOfIsCompl'] at h2
  simpa using h2

end Orth

theorem split_case {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    [FiniteDimensional K V] {r : ℕ} (hr : 1 ≤ r) (hdim : finrank K V = 2 * r) (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {T : sesqUnitaryGroup B} (hTns : ∀ c : K, spOp T ≠ c • 1)
    (hTT : spOp T * spOp T = 1) {l : K} (hl : l ^ 2 = 1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    (hfix : ∀ x ∈ L, ∀ w ∈ eigenMinus l (spOp T), spOp (x : sesqUnitaryGroup B) w = w) :
    eigenPlus l (spOp T) ≠ ⊥ ∧ eigenMinus l (spOp T) ≠ ⊥ ∧
      (∀ v ∈ eigenPlus l (spOp T), ∀ w ∈ eigenMinus l (spOp T), B v w = 0) ∧
      (B.domRestrict₁₂ (eigenPlus l (spOp T)) (eigenPlus l (spOp T))).Nondegenerate ∧
      (B.domRestrict₁₂ (eigenMinus l (spOp T)) (eigenMinus l (spOp T))).Nondegenerate ∧
      ((L.map (Subgroup.centralizer {T}).subtype : Subgroup (sesqUnitaryGroup B)) :
        Set (sesqUnitaryGroup B)) =
        symplecticSummandSet B (eigenPlus l (spOp T)) (eigenMinus l (spOp T)) ∧
      ∀ R : Subgroup (sesqUnitaryGroup B),
        R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
          Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)) →
        ⁅R, R⁆ = R → ∀ g ∈ R, ∀ a ∈ eigenPlus l (spOp T), spOp g a = a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hk : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨-, hsq, -⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK hr hdim
    hB hBnd (A := (T : LinearMap.GeneralLinearGroup K V)) hTns one_ne_zero
    (by rw [one_smul]; exact hTT) (μ := 1)
    (fun v w => by rw [one_mul]; exact mem_sesqUnitaryGroup.mp T.2 v w)
  obtain ⟨hP, hM, hpos, -⟩ := hsq l hl
  obtain ⟨horth, haltP, -, hndP, hndM, e, he⟩ := hpos (div_one 1)
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl
  have hTT' : spOp T * spOp T = (l ^ 2) • 1 := by rw [hl, one_smul]; exact hTT
  have hc : IsCompl (eigenPlus l (spOp T)) (eigenMinus l (spOp T)) :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hTT')
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup.centralizer {T} ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l (spOp T)) (eigenPlus l (spOp T))) ×
        sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l (spOp T)) (eigenMinus l (spOp T))),
      E' = (centralizerSimEquiv T).trans e := ⟨_, rfl⟩
  have heW : ∀ (g : Subgroup.centralizer {T}) (w : eigenMinus l (spOp T)),
      ((((E' g).2 : LinearMap.GeneralLinearGroup K (eigenMinus l (spOp T))) :
        Module.End K (eigenMinus l (spOp T))) w : V) = spOp (g : sesqUnitaryGroup B) w :=
    fun g w => by
      rw [hE']
      exact LinearMap.congr_fun (he (centralizerSimEquiv T g)).2 w
  have hsnd : ∀ x : Subgroup.centralizer {T}, (∀ w ∈ eigenMinus l (spOp T),
      spOp (x : sesqUnitaryGroup B) w = w) → (E' x).2 = 1 := fun x hx =>
    Subtype.ext (Units.ext (LinearMap.ext fun w => Subtype.ext (by
      rw [heW]
      exact hx w w.2)))
  set ρ := (MonoidHom.fst _ _).comp E'.toMonoidHom with hρ
  have hρs : Function.Surjective ρ := fun y => ⟨E'.symm (y, 1), by simp [hρ]⟩
  have hρinj : ∀ x ∈ L, ∀ y ∈ L, ρ x = ρ y → x = y := fun x hx y hy hxy =>
    E'.injective (Prod.ext hxy (by rw [hsnd x (hfix x hx), hsnd y (hfix y hy)]))
  have hL₁ : CFSG.IsComponent (L.map ρ) := by
    refine ⟨?_, hL.2.map hρs⟩
    have hbij : Function.Bijective (ρ.subgroupMap L) := by
      refine ⟨fun x y hxy => Subtype.ext (hρinj x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩
      exact ρ.subgroupMap_surjective L
    exact (isQuasisimple_congr (MulEquiv.ofBijective (ρ.subgroupMap L) hbij)).1 hL.1
  have hdimA : 2 ≤ finrank K (eigenPlus l (spOp T)) :=
    CatalogueBSymplecticB.two_le_finrank_of_ne_bot hP _ haltP hndP
  have hL₁eq : L.map ρ = ⊤ := eq_top_of_isComponent hodd haltP hndP hdimA hL₁
  have hset : ((L.map (Subgroup.centralizer {T}).subtype : Subgroup (sesqUnitaryGroup B)) :
      Set (sesqUnitaryGroup B)) =
        symplecticSummandSet B (eigenPlus l (spOp T)) (eigenMinus l (spOp T)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hfix x hx, fun a ha => mapsTo_eigenPlus_of_mem l (centralizerSimEquiv T x).2 ha⟩
    · rintro ⟨hgW, hgA⟩
      have hgT : g ∈ Subgroup.centralizer {T} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        refine Subtype.ext (Units.ext ?_)
        change spOp g * spOp T = spOp T * spOp g
        refine commute_of_mapsTo_eigen h2 hl0 hTT' (fun v hv => hgA v hv) fun v hv => ?_
        change spOp g v ∈ eigenMinus l (spOp T)
        rw [hgW v hv]
        exact hv
      obtain ⟨x, hx⟩ : ∃ x : Subgroup.centralizer {T}, (x : sesqUnitaryGroup B) = g :=
        ⟨⟨g, hgT⟩, rfl⟩
      have hxW : ∀ w ∈ eigenMinus l (spOp T), spOp (x : sesqUnitaryGroup B) w = w := by
        rw [hx]
        exact hgW
      have hρx : ρ x ∈ L.map ρ := by
        rw [hL₁eq]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hρx
      have hyx' : y = x := E'.injective (Prod.ext hyx (by rw [hsnd y (hfix y hy), hsnd x hxW]))
      refine ⟨y, hy, ?_⟩
      rw [hyx']
      exact hx
  refine ⟨hP, hM, horth, hndP, hndM, hset, fun R hR hRp => ?_⟩
  exact fix_of_le_centralizer_summand hB hc horth hk hndP hndM hdimA (by rw [← hset]) hR hRp

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic
