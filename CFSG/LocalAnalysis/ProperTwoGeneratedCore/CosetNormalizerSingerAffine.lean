module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAllDimensions
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerOrder168

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

universe u

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

variable (V) in
@[expose] def translationGroup : Subgroup (V ≃ᵃ[ZMod 2] V) :=
  (AffineEquiv.constVAddHom (ZMod 2) V).range

variable (V) in
@[expose] def zeroFixing : Subgroup (V ≃ᵃ[ZMod 2] V) where
  carrier := {g | g 0 = 0}
  mul_mem' {g h} hg hh := by
    change g (h 0) = 0
    rw [show h 0 = 0 from hh, show g 0 = 0 from hg]
  one_mem' := rfl
  inv_mem' {g} hg := by
    change g.symm 0 = 0
    rw [AffineEquiv.symm_apply_eq]
    exact (show g 0 = 0 from hg).symm

@[expose] def zeroStabilizer (Γ : Subgroup (V ≃ᵃ[ZMod 2] V)) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  (Γ ⊓ zeroFixing V).map AffineEquiv.linearHom

theorem mem_translationGroup {g : V ≃ᵃ[ZMod 2] V} :
    g ∈ translationGroup V ↔ ∃ w : V, AffineEquiv.constVAdd (ZMod 2) V w = g :=
  ⟨fun ⟨w, hw⟩ => ⟨w.toAdd, hw⟩, fun ⟨w, hw⟩ => ⟨Multiplicative.ofAdd w, hw⟩⟩

theorem mem_zeroFixing {g : V ≃ᵃ[ZMod 2] V} : g ∈ zeroFixing V ↔ g 0 = 0 :=
  Iff.rfl

theorem apply_eq_linear_add (g : V ≃ᵃ[ZMod 2] V) (v : V) : g v = g.linear v + g 0 := by
  have h := g.map_vadd 0 v
  rwa [vadd_eq_add, add_zero, vadd_eq_add] at h

theorem apply_eq_linear_of_apply_zero {g : V ≃ᵃ[ZMod 2] V} (hg : g 0 = 0) (v : V) :
    g v = g.linear v := by
  rw [apply_eq_linear_add, hg, add_zero]

theorem eq_toAffineEquiv_linear {g : V ≃ᵃ[ZMod 2] V} (hg : g 0 = 0) :
    g = g.linear.toAffineEquiv :=
  AffineEquiv.ext fun v => apply_eq_linear_of_apply_zero hg v

theorem mem_zeroStabilizer {Γ : Subgroup (V ≃ᵃ[ZMod 2] V)} {L : V ≃ₗ[ZMod 2] V} :
    L ∈ zeroStabilizer Γ ↔ L.toAffineEquiv ∈ Γ := by
  constructor
  · rintro ⟨g, ⟨hgΓ, hg0⟩, rfl⟩
    change g.linear.toAffineEquiv ∈ Γ
    rw [← eq_toAffineEquiv_linear hg0]
    exact hgΓ
  · intro hL
    exact ⟨L.toAffineEquiv, ⟨hL, map_zero L⟩, rfl⟩

theorem linear_eq_one_iff (g : V ≃ᵃ[ZMod 2] V) : g.linear = 1 ↔ g ∈ translationGroup V := by
  rw [mem_translationGroup]
  constructor
  · intro hg
    refine ⟨g 0, AffineEquiv.ext fun v => ?_⟩
    rw [AffineEquiv.constVAdd_apply, vadd_eq_add, apply_eq_linear_add g v, hg, add_comm]
    rfl
  · rintro ⟨w, rfl⟩
    rfl

theorem mul_constVAdd_mul_inv (g : V ≃ᵃ[ZMod 2] V) (w : V) :
    g * AffineEquiv.constVAdd (ZMod 2) V w * g⁻¹ =
      AffineEquiv.constVAdd (ZMod 2) V (g.linear w) := by
  refine AffineEquiv.ext fun v => ?_
  change g (w +ᵥ g.symm v) = g.linear w +ᵥ v
  rw [AffineEquiv.map_vadd, AffineEquiv.apply_symm_apply]

theorem mul_comm_of_mem_translationGroup {g h : V ≃ᵃ[ZMod 2] V} (hg : g ∈ translationGroup V)
    (hh : h ∈ translationGroup V) : g * h = h * g := by
  obtain ⟨w, rfl⟩ := mem_translationGroup.mp hg
  obtain ⟨w', rfl⟩ := mem_translationGroup.mp hh
  refine AffineEquiv.ext fun v => ?_
  change w +ᵥ (w' +ᵥ v) = w' +ᵥ (w +ᵥ v)
  simp only [vadd_eq_add]
  exact add_left_comm w w' v

section Coordinates

variable [FiniteDimensional (ZMod 2) V]

theorem exists_semilinear_coordinates {e : ℕ} (he : 1 ≤ e) (hV : finrank (ZMod 2) V = e)
    {Γ₀ T : Subgroup (V ≃ₗ[ZMod 2] V)} (hTΓ : T ≤ Γ₀) (hTn : (T.subgroupOf Γ₀).Normal)
    (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hreg : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ t ∈ T, t v = w) :
    ∃ ψ : V ≃ₗ[ZMod 2] GaloisField 2 e,
      (∀ g ∈ Γ₀, ∃ (c : (GaloisField 2 e)ˣ) (σ : GaloisField 2 e ≃+* GaloisField 2 e),
        ∀ v, ψ (g v) = c * σ (ψ v)) ∧
      (∀ g : V ≃ₗ[ZMod 2] V, g ∈ T ↔ ∃ c : (GaloisField 2 e)ˣ, ∀ v, ψ (g v) = c * ψ v) ∧
      (∃ d, d ∣ e ∧ Nat.card Γ₀ = Nat.card T * d) ∧ Group.IsSolvable Γ₀ := by
  classical
  set E := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V with hE
  set T' := T.comap E.toMonoidHom with hT'
  set U' := Γ₀.comap E.toMonoidHom with hU'
  have hTU' : T' ≤ U' := fun g hg => hTΓ hg
  have hTn' : (T'.subgroupOf U').Normal := by
    refine ⟨fun t ht u => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    have h := hTn.conj_mem ⟨E t, hTΓ ht⟩ (Subgroup.mem_subgroupOf.mpr ht) ⟨E u, u.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    change E (_ * _ * _) ∈ T
    rwa [map_mul, map_mul, map_inv]
  have hcomm' : ∀ g ∈ T', ∀ h ∈ T', g * h = h * g := fun g hg h hh =>
    E.injective (by rw [map_mul, map_mul]; exact hcomm _ hg _ hh)
  have hET : ∀ t ∈ T, E.symm t ∈ T' := fun t ht => by
    change E (E.symm t) ∈ T
    rwa [MulEquiv.apply_symm_apply]
  have hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ T', ∀ w ∈ W, (g : Module.End (ZMod 2) V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    refine Or.inr (eq_top_iff.mpr fun v _ => ?_)
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    by_cases hv : v = 0
    · rw [hv]
      exact W.zero_mem
    obtain ⟨t, ht, htw⟩ := hreg w v hw0 hv
    have h := hW (E.symm t) (hET t ht) w hwW
    rwa [← htw]
  obtain ⟨hF, hcardK, hev, -, hσapp, hker, -, -⟩ :=
    abelian_irreducible_normalizer_semilinear (p := 2) he hV hTU' hTn' hcomm' hirr
  set K := operatorAlgebra T' with hK
  set σh := operatorConjHom (conj_mem_of_subgroupOf_normal hTU' hTn') with hσh
  let _ : Field K := hF.toField
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; positivity)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField 2 e) := Fintype.ofFinite _
  have hcardG : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
  let θ : K ≃+* GaloisField 2 e := FiniteField.ringEquivOfCardEq
    (by rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardK, hcardG])
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨s, hs⟩ := exists_ne (0 : V)
  let ev : K →+ V :=
    { toFun := fun a => (a : Module.End (ZMod 2) V) s
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let evE : K ≃+ V := AddEquiv.ofBijective ev (hev s hs)
  let ψa : V ≃+ GaloisField 2 e := evE.symm.trans θ.toAddEquiv
  let ψ : V ≃ₗ[ZMod 2] GaloisField 2 e := ψa.toLinearEquiv (ZMod.map_smul ψa)
  have hψ : ∀ a : K, ψ ((a : Module.End (ZMod 2) V) s) = θ a := fun a => by
    change θ (evE.symm (evE a)) = θ a
    rw [AddEquiv.symm_apply_apply]
  have hψv : ∀ v : V, ((evE.symm v : K) : Module.End (ZMod 2) V) s = v := fun v =>
    evE.apply_symm_apply v
  have hev0 : ∀ a : K, (a : Module.End (ZMod 2) V) s = 0 → a = 0 := fun a h =>
    (hev s hs).1 (h.trans rfl)
  have hgs : ∀ g : V ≃ₗ[ZMod 2] V, g s ≠ 0 := fun g h =>
    hs (g.injective (h.trans g.map_zero.symm))
  have hTK : ∀ t ∈ T,
      ((E.symm t : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) ∈ K :=
    fun t ht => Algebra.subset_adjoin ⟨E.symm t, hET t ht, rfl⟩
  have hTmul : ∀ t (ht : t ∈ T) (v : V), ψ (t v) = θ ⟨_, hTK t ht⟩ * ψ v := by
    intro t ht v
    obtain ⟨a, rfl⟩ : ∃ a : K, (a : Module.End (ZMod 2) V) s = v := ⟨evE.symm v, hψv v⟩
    have h : t ((a : Module.End (ZMod 2) V) s) =
        (((⟨_, hTK t ht⟩ * a : K) : Module.End (ZMod 2) V) s) := rfl
    rw [h, hψ, hψ, map_mul]
  have hscalar : ∀ c : (GaloisField 2 e)ˣ, ∃ t ∈ T, ∀ v, ψ (t v) = c * ψ v := by
    intro c
    have ha : ((θ.symm c : K) : Module.End (ZMod 2) V) s ≠ 0 := fun h0 =>
      c.ne_zero (by rw [← θ.apply_symm_apply (c : GaloisField 2 e), hev0 _ h0, map_zero])
    obtain ⟨t, ht, hts⟩ := hreg s _ hs ha
    refine ⟨t, ht, fun v => ?_⟩
    have ht' : (⟨_, hTK t ht⟩ : K) = θ.symm c := (hev s hs).1 hts
    rw [hTmul t ht v, ht', θ.apply_symm_apply]
  have hTiff : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ T ↔
      ∃ c : (GaloisField 2 e)ˣ, ∀ v, ψ (g v) = c * ψ v := by
    intro g
    constructor
    · intro hg
      refine ⟨Units.mk0 (θ ⟨_, hTK g hg⟩) fun h0 => hgs g ?_, fun v => hTmul g hg v⟩
      have := congrArg (fun a : K => (a : Module.End (ZMod 2) V) s)
        ((map_eq_zero_iff θ θ.injective).mp h0)
      exact this
    · rintro ⟨c, hc⟩
      obtain ⟨t, ht, htc⟩ := hscalar c
      have hgt : g = t := LinearEquiv.ext fun v => ψ.injective ((hc v).trans (htc v).symm)
      rwa [hgt]
  have hU : ∀ g ∈ Γ₀, E.symm g ∈ U' := fun g hg => by
    change E (E.symm g) ∈ Γ₀
    rwa [MulEquiv.apply_symm_apply]
  have hsemi : ∀ g ∈ Γ₀, ∃ (c : (GaloisField 2 e)ˣ)
      (σ : GaloisField 2 e ≃+* GaloisField 2 e), ∀ v, ψ (g v) = c * σ (ψ v) := by
    intro g hg
    set u : U' := ⟨E.symm g, hU g hg⟩
    set b := evE.symm (g s)
    have hb : (b : Module.End (ZMod 2) V) s = g s := hψv (g s)
    refine ⟨Units.mk0 (θ b) fun h0 => hgs g ?_, θ.symm.trans ((σh u).trans θ), fun v => ?_⟩
    · rw [← hb, (map_eq_zero_iff θ θ.injective).mp h0]
      rfl
    obtain ⟨a, rfl⟩ : ∃ a : K, (a : Module.End (ZMod 2) V) s = v := ⟨evE.symm v, hψv v⟩
    have h1 := hσapp u a s
    change ψ (((u : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V)
      ((a : Module.End (ZMod 2) V) s)) = _
    rw [h1]
    have h2 : ((σh u a : K) : Module.End (ZMod 2) V) (g s) =
        ((σh u a * b : K) : Module.End (ZMod 2) V) s := by
      rw [← hb]
      rfl
    change ψ (((σh u a : K) : Module.End (ZMod 2) V) (g s)) = _
    rw [h2, hψ, hψ, Units.val_mk0, RingEquiv.trans_apply, RingEquiv.trans_apply,
      RingEquiv.symm_apply_apply, map_mul, mul_comm]
  have hkerσ : σh.ker = T'.subgroupOf U' := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have hu : ((u : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) ∈ K :=
        (hker u).mp h1
      obtain ⟨t, ht, hts⟩ := hreg s (((u : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V) s) hs (hgs (E u))
      have htu : (⟨_, hTK t ht⟩ : K) = ⟨_, hu⟩ := (hev s hs).1 hts
      have hu' : (u : LinearMap.GeneralLinearGroup (ZMod 2) V) = E.symm t :=
        Units.ext (congrArg Subtype.val htu).symm
      change E (u : LinearMap.GeneralLinearGroup (ZMod 2) V) ∈ T
      rw [hu', MulEquiv.apply_symm_apply]
      exact ht
    · intro hu
      exact (hker u).mpr (Algebra.subset_adjoin ⟨_, hu, rfl⟩)
  obtain ⟨φ, -, -, hφ, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_two he hcardK
  have hcardT' : Nat.card T' = Nat.card T := by
    have hmap : T'.map E.toMonoidHom = T := Subgroup.map_comap_eq_self_of_surjective E.surjective T
    rw [← hmap, Subgroup.card_map_of_injective E.injective]
  have hcardU' : Nat.card U' = Nat.card Γ₀ := by
    have hmap : U'.map E.toMonoidHom = Γ₀ :=
      Subgroup.map_comap_eq_self_of_surjective E.surjective Γ₀
    rw [← hmap, Subgroup.card_map_of_injective E.injective]
  refine ⟨ψ, hsemi, hTiff, ⟨Nat.card σh.range, ?_, ?_⟩, ?_⟩
  · rw [← hcardAut]
    exact Subgroup.card_subgroup_dvd_card _
  · have h1 := σh.ker.card_mul_index
    rw [Subgroup.index_ker, hkerσ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU').toEquiv,
      hcardT', hcardU'] at h1
    exact h1.symm
  · have : IsCyclic (RingAut K) := ⟨⟨φ, fun x => by
      have hx : x ∈ Subgroup.zpowers φ := hφ ▸ Subgroup.mem_top x
      exact Subgroup.mem_zpowers_iff.mp hx⟩⟩
    have : Group.IsSolvable (RingAut K) := Group.isSolvable_of_comm fun a b => by
      let _ := IsCyclic.commGroup (α := RingAut K)
      exact mul_comm a b
    have : Group.IsSolvable (T'.subgroupOf U') := Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subtype.ext (hcomm' _ a.2 _ b.2))
    have hU'solv : Group.IsSolvable U' := Group.isSolvable_of_ker_le_range
      (T'.subgroupOf U').subtype σh (by rw [hkerσ, Subgroup.range_subtype])
    let ι : Γ₀ →* U' :=
      { toFun := fun g => ⟨E.symm g, hU g g.2⟩
        map_one' := Subtype.ext (map_one E.symm)
        map_mul' := fun g h => Subtype.ext (map_mul E.symm (g : V ≃ₗ[ZMod 2] V) h) }
    exact Group.isSolvable_of_isSolvable_injective (f := ι) fun g h hgh =>
      Subtype.ext (E.symm.injective (congrArg Subtype.val hgh))

end Coordinates

theorem card_eq_card_mul_card_zeroStabilizer (Γ : Subgroup (V ≃ᵃ[ZMod 2] V))
    (htrans : ∀ v w : V, ∃ g ∈ Γ, g v = w) :
    Nat.card Γ = Nat.card V * Nat.card (zeroStabilizer Γ) := by
  let _ : MulAction Γ V :=
    { smul := fun g v => (g : V ≃ᵃ[ZMod 2] V) v
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have horbit : MulAction.orbit Γ (0 : V) = Set.univ :=
    Set.eq_univ_of_forall fun v => by
      obtain ⟨g, hg, hgv⟩ := htrans 0 v
      exact ⟨⟨g, hg⟩, hgv⟩
  have hstab : Nat.card (MulAction.stabilizer Γ (0 : V)) = Nat.card (zeroStabilizer Γ) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun g => ⟨((g : Γ) : V ≃ᵃ[ZMod 2] V).linear, ⟨(g : Γ), ⟨(g : Γ).2, g.2⟩, rfl⟩⟩) ⟨?_, ?_⟩)
    · intro g h hgh
      have hlin : ((g : Γ) : V ≃ᵃ[ZMod 2] V).linear = ((h : Γ) : V ≃ᵃ[ZMod 2] V).linear :=
        congrArg Subtype.val hgh
      refine Subtype.ext (Subtype.ext ?_)
      rw [eq_toAffineEquiv_linear (MulAction.mem_stabilizer_iff.mp g.2),
        eq_toAffineEquiv_linear (MulAction.mem_stabilizer_iff.mp h.2), hlin]
    · rintro ⟨_, ⟨g, ⟨hgΓ, hg0⟩, rfl⟩⟩
      exact ⟨⟨⟨g, hgΓ⟩, hg0⟩, rfl⟩
  have h := (MulAction.stabilizer Γ (0 : V)).card_mul_index
  rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, hstab] at h
  rw [← h, mul_comm]

theorem card_linearEquiv_zmod_two [FiniteDimensional (ZMod 2) V] {e : ℕ}
    (hV : finrank (ZMod 2) V = e) :
    Nat.card (V ≃ₗ[ZMod 2] V) = ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ)) := by
  let b : Basis (Fin e) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hV
  rw [← Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)).toEquiv,
    Matrix.card_GL_field, ZMod.card]

theorem false_of_card_le_prod {e d : ℕ} (he : 1 ≤ e) (he3 : e < 3) (hd : 0 < d)
    (h : 2 ^ e * (2 ^ e - 1) * d ≤ ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ))) : False := by
  interval_cases e <;> simp [Fin.prod_univ_succ] at h <;> omega

theorem card_GL_three_zmod_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
  norm_num

theorem isSimpleGroup_GL_three_zmod_two : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

theorem sq_eq_one_or_pow_three_eq_one_of_cubic {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
    {y : R} (h6 : y ^ 6 = 1) (c : ℕ → ZMod 2)
    (h : y ^ 3 + ∑ i ∈ Finset.range 3, algebraMap (ZMod 2) R (c i) * y ^ i = 0) :
    y ^ 2 = 1 ∨ y ^ 3 = 1 := by
  have h2 : (2 : R) = 0 := by
    rw [← one_add_one_eq_two, ← map_one (algebraMap (ZMod 2) R), ← map_add,
      show (1 + 1 : ZMod 2) = 0 from rfl, map_zero]
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    mul_one] at h
  rcases hc (c 0) with h0 | h0 <;> rcases hc (c 1) with h1 | h1 <;>
    rcases hc (c 2) with h2' | h2' <;>
    simp only [h0, h1, h2', map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] at h <;>
    grind

theorem orderOf_ne_six_GL_three_zmod_two (A : GL (Fin 3) (ZMod 2)) : orderOf A ≠ 6 := by
  intro hA
  set M := (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
  set y : Algebra.adjoin (ZMod 2) {M} := ⟨M, Algebra.self_mem_adjoin_singleton (ZMod 2) M⟩
  have hy : Polynomial.aeval y M.charpoly = 0 :=
    Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact Matrix.aeval_self_charpoly M)
  rw [(Matrix.charpoly_monic M).as_sum, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hy
  simp only [map_add, map_sum, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hy
  have hA6 : A ^ 6 = 1 := hA ▸ pow_orderOf_eq_one A
  have hy6 : y ^ 6 = 1 := Subtype.ext (by
    change M ^ 6 = 1
    rw [← Units.val_pow_eq_pow_val, hA6, Units.val_one])
  have hpow : ∀ n : ℕ, y ^ n = 1 → A ^ n = 1 := fun n h => Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact congrArg Subtype.val h)
  rcases sq_eq_one_or_pow_three_eq_one_of_cubic hy6 _ hy with h | h
  · have := orderOf_dvd_of_pow_eq_one (hpow 2 h)
    rw [hA] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one (hpow 3 h)
    rw [hA] at this
    norm_num at this

theorem exists_mul_ne_mul_GL_three_zmod_two : ∃ a b : GL (Fin 3) (ZMod 2), a * b ≠ b * a := by
  have := isSimpleGroup_GL_three_zmod_two
  by_contra h
  push Not at h
  let _ : CommGroup (GL (Fin 3) (ZMod 2)) := { mul_comm := h }
  have hp := IsSimpleGroup.prime_card (α := GL (Fin 3) (ZMod 2))
  rw [card_GL_three_zmod_two] at hp
  norm_num at hp

theorem le_normalizer_of_subgroupOf_normal {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hn : (H.subgroupOf K).Normal) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Subgroup.mem_subgroupOf.mp
      (hn.conj_mem ⟨h, hHK hh⟩ (Subgroup.mem_subgroupOf.mpr hh) ⟨g, hg⟩)
  · intro hh
    have := Subgroup.mem_subgroupOf.mp
      (hn.conj_mem ⟨g * h * g⁻¹, hHK hh⟩ (Subgroup.mem_subgroupOf.mpr hh) ⟨g⁻¹, K.inv_mem hg⟩)
    simpa [mul_assoc] using this

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo in
theorem binary_affine_normal_singer_solvable_or_projective_seven {e : ℕ} (he : 1 ≤ e)
    (hV : finrank (ZMod 2) V = e) (Γ : Subgroup (V ≃ᵃ[ZMod 2] V))
    (htrans : ∀ v w : V, ∃ g ∈ Γ, g v = w) (T : Subgroup (V ≃ₗ[ZMod 2] V))
    (hTΓ : T ≤ zeroStabilizer Γ) (hTn : (T.subgroupOf (zeroStabilizer Γ)).Normal)
    (hTcyc : IsCyclic T)
    (hTreg : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃! t : T, (t : V ≃ₗ[ZMod 2] V) v = w) :
    Xor
      (translationGroup V ≤ Γ ∧ Group.IsSolvable Γ ∧
        ∃ ψ : V ≃ₗ[ZMod 2] GaloisField 2 e,
          (∀ g ∈ zeroStabilizer Γ, ∃ (c : (GaloisField 2 e)ˣ)
            (σ : GaloisField 2 e ≃+* GaloisField 2 e), ∀ v, ψ (g v) = c * σ (ψ v)) ∧
          ∀ g : V ≃ₗ[ZMod 2] V, g ∈ T ↔ ∃ c : (GaloisField 2 e)ˣ, ∀ v, ψ (g v) = c * ψ v)
      (e = 3 ∧ Γ ⊓ translationGroup V = ⊥ ∧
        Function.Bijective (AffineEquiv.linearHom.comp Γ.subtype) ∧
        (∃ β : V ≃ Omega (ZMod 7),
          (fun g : V ≃ᵃ[ZMod 2] V => β.permCongr g.toEquiv) '' (Γ : Set (V ≃ᵃ[ZMod 2] V)) =
            (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))) ∧
        (coordinatePSLAction (ZMod 7)).range = coordinateG (ZMod 7)) := by
  classical
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  have hcardV : Nat.card V = 2 ^ e := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨s, hs⟩ := exists_ne (0 : V)
  have hgs : ∀ g : V ≃ₗ[ZMod 2] V, g s ≠ 0 := fun g h =>
    hs (g.injective (h.trans g.map_zero.symm))
  have hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g := by
    intro g hg h hh
    let _ := IsCyclic.commGroup (α := T)
    exact congrArg Subtype.val (mul_comm (⟨g, hg⟩ : T) ⟨h, hh⟩)
  have hreg : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ t ∈ T, t v = w := fun v w hv hw => by
    obtain ⟨t, ht, -⟩ := hTreg v w hv hw
    exact ⟨t, t.2, ht⟩
  obtain ⟨ψ, hsemi, hTiff, ⟨d, hde, hcardΓ₀⟩, hsolv₀⟩ :=
    exists_semilinear_coordinates he hV hTΓ hTn hcomm hreg
  have hcardT : Nat.card T = 2 ^ e - 1 := by
    have hbij : Function.Bijective fun t : T =>
        (⟨(t : V ≃ₗ[ZMod 2] V) s, hgs t⟩ : {v : V // ¬ v = 0}) := by
      refine ⟨fun t t' htt => ?_, fun v => ?_⟩
      · obtain ⟨t₀, -, huniq⟩ := hTreg s ((t : V ≃ₗ[ZMod 2] V) s) hs (hgs t)
        exact (huniq t rfl).trans (huniq t' (congrArg Subtype.val htt).symm).symm
      · obtain ⟨t, ht, -⟩ := hTreg s v hs v.2
        exact ⟨t, Subtype.ext ht⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
    have h1 := Nat.card_congr (Equiv.sumCompl fun v : V => v = 0)
    rw [Nat.card_sum, hcardV, Nat.card_unique] at h1
    omega
  have hcardΓ : Nat.card Γ = 2 ^ e * (2 ^ e - 1) * d := by
    rw [card_eq_card_mul_card_zeroStabilizer Γ htrans, hcardΓ₀, hcardT, hcardV, mul_assoc]
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hde (by omega)
  have hconj : ∀ t ∈ T, ∀ w : V, AffineEquiv.constVAdd (ZMod 2) V w ∈ Γ →
      AffineEquiv.constVAdd (ZMod 2) V (t w) ∈ Γ := by
    intro t ht w hw
    have htΓ : t.toAffineEquiv ∈ Γ := mem_zeroStabilizer.mp (hTΓ ht)
    have := Γ.mul_mem (Γ.mul_mem htΓ hw) (Γ.inv_mem htΓ)
    rwa [mul_constVAdd_mul_inv] at this
  by_cases hA : translationGroup V ≤ Γ
  ·
    have hlin : ∀ g ∈ Γ, g.linear ∈ zeroStabilizer Γ := by
      intro g hg
      have hτ : AffineEquiv.constVAdd (ZMod 2) V (-g 0) ∈ Γ :=
        hA (mem_translationGroup.mpr ⟨_, rfl⟩)
      refine ⟨AffineEquiv.constVAdd (ZMod 2) V (-g 0) * g, ⟨Γ.mul_mem hτ hg, ?_⟩, ?_⟩
      · change -g 0 +ᵥ g 0 = 0
        rw [vadd_eq_add, neg_add_cancel]
      · exact LinearEquiv.ext fun v => rfl
    let L' : Γ →* zeroStabilizer Γ :=
      (AffineEquiv.linearHom.comp Γ.subtype).codRestrict _ fun g => hlin g g.2
    have hkerA : ∀ g ∈ L'.ker, ((g : Γ) : V ≃ᵃ[ZMod 2] V) ∈ translationGroup V := by
      intro g hg
      refine (linear_eq_one_iff _).mp ?_
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      exact this
    have : Group.IsSolvable L'.ker := Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subtype.ext (mul_comm_of_mem_translationGroup (hkerA _ a.2) (hkerA _ b.2)))
    have hsolv : Group.IsSolvable Γ :=
      Group.isSolvable_of_ker_le_range L'.ker.subtype L' (by rw [Subgroup.range_subtype])
    refine Or.inl ⟨⟨hA, hsolv, ψ, hsemi, hTiff⟩, ?_⟩
    rintro ⟨-, hbot, -⟩
    have hmem : AffineEquiv.constVAdd (ZMod 2) V s ∈ Γ ⊓ translationGroup V :=
      ⟨hA (mem_translationGroup.mpr ⟨s, rfl⟩), mem_translationGroup.mpr ⟨s, rfl⟩⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h0 := congrArg (fun g : V ≃ᵃ[ZMod 2] V => g 0) hmem
    change s +ᵥ (0 : V) = 0 at h0
    rw [vadd_eq_add, add_zero] at h0
    exact hs h0
  have hbot : Γ ⊓ translationGroup V = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgΓ, hgA⟩
    obtain ⟨w, rfl⟩ := mem_translationGroup.mp hgA
    rw [Subgroup.mem_bot]
    by_cases hw : w = 0
    · rw [hw]
      exact AffineEquiv.constVAdd_zero _ _
    refine absurd (fun g hg => ?_) hA
    obtain ⟨v, rfl⟩ := mem_translationGroup.mp hg
    by_cases hv : v = 0
    · rw [hv, AffineEquiv.constVAdd_zero]
      exact Γ.one_mem
    obtain ⟨t, ht, htw⟩ := hreg w v hw hv
    rw [← htw]
    exact hconj t ht w hgΓ
  set L := AffineEquiv.linearHom.comp Γ.subtype with hL
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : (g : V ≃ᵃ[ZMod 2] V) ∈ Γ ⊓ translationGroup V :=
      ⟨g.2, (linear_eq_one_iff _).mp hg⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hΓ₀L : zeroStabilizer Γ ≤ L.range := by
    rintro _ ⟨g, ⟨hgΓ, -⟩, rfl⟩
    exact ⟨⟨g, hgΓ⟩, rfl⟩
  have hcardR : Nat.card L.range = Nat.card Γ :=
    (Nat.card_congr (MonoidHom.ofInjective hLinj).toEquiv).symm
  have he3 : e = 3 := by
    by_contra hne
    rcases Nat.lt_or_ge e 3 with hlt | hge
    · have hle : Nat.card Γ ≤ Nat.card (V ≃ₗ[ZMod 2] V) := Nat.card_le_card_of_injective L hLinj
      rw [card_linearEquiv_zmod_two hV, hcardΓ] at hle
      exact false_of_card_le_prod he hlt hd hle
    let cψ : (V ≃ₗ[ZMod 2] V) ≃* (GaloisField 2 e ≃ₗ[ZMod 2] GaloisField 2 e) :=
      { toFun := fun g => ψ.symm.trans (g.trans ψ)
        invFun := fun g => ψ.trans (g.trans ψ.symm)
        left_inv := fun g => LinearEquiv.ext fun v => by simp
        right_inv := fun g => LinearEquiv.ext fun v => by simp
        map_mul' := fun g h => LinearEquiv.ext fun v => by simp }
    refine not_exists_singer_overgroup_card_eq_of_four_le (by omega)
      (GaloisField.card 2 e (by omega)) hd hde ⟨L.range.map cψ.toMonoidHom, ?_, ?_⟩
    · rintro _ ⟨c, rfl⟩
      have hg : cψ.symm (CFSG.ShultStronglyClosedTI.Singer.scalarHom (ZMod 2) _ c) ∈ T :=
        (hTiff _).mpr ⟨c, fun v => by
          change ψ (ψ.symm (c * ψ v)) = c * ψ v
          rw [LinearEquiv.apply_symm_apply]⟩
      exact ⟨_, hΓ₀L (hTΓ hg), cψ.apply_symm_apply _⟩
    · rw [Subgroup.card_map_of_injective cψ.injective, hcardR, hcardΓ]
  subst he3
  have hT7 : Nat.card T = 7 := by
    rw [hcardT]
    norm_num
  let b : Basis (Fin 3) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hV
  let φ : GL (Fin 3) (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  have hcardGL : Nat.card (V ≃ₗ[ZMod 2] V) = 168 := by
    rw [← Nat.card_congr φ.toEquiv, card_GL_three_zmod_two]
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL_three_zmod_two
  have : IsSimpleGroup (V ≃ₗ[ZMod 2] V) := φ.symm.isSimpleGroup
  have hd3 : d = 3 := by
    have : d ≤ 3 := Nat.le_of_dvd (by norm_num) hde
    interval_cases d
    · exfalso
      have hidx : L.range.index = 3 := by
        have h := L.range.card_mul_index
        rw [hcardR, hcardΓ, hcardGL] at h
        norm_num at h
        omega
      have htop := CosetNormalizer.eq_top_of_index_lt_prime_dvd L.range (p := 7) Nat.prime_seven
        (by rw [hcardGL]; norm_num) (by rw [hidx]; norm_num)
      rw [htop, Subgroup.index_top] at hidx
      omega
    · norm_num at hde
    · rfl
  subst hd3
  have hRtop : L.range = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (by rw [hcardR, hcardΓ, hcardGL]; norm_num)
  have hbij : Function.Bijective L := ⟨hLinj, MonoidHom.range_eq_top.mp hRtop⟩
  set F : Γ ≃* GL (Fin 3) (ZMod 2) := (MulEquiv.ofBijective L hbij).trans φ.symm with hF
  obtain ⟨h8, -, ℓ, -, hrange, -⟩ :=
    CosetNormalizer.simple_order_168_without_six_projective_seven_recognition
      (GL (Fin 3) (ZMod 2)) exists_mul_ne_mul_GL_three_zmod_two card_GL_three_zmod_two
      orderOf_ne_six_GL_three_zmod_two
  have hfac : (Nat.card (GL (Fin 3) (ZMod 2))).factorization 7 = 1 := by
    rw [card_GL_three_zmod_two, show (168 : ℕ) = 7 * 24 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_seven,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardP : Nat.card (T.map φ.symm.toMonoidHom) = 7 ^ (Nat.card (GL (Fin 3) (ZMod 2))).factorization 7 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective, hT7, hfac, pow_one]
  set P₀ : Sylow 7 (GL (Fin 3) (ZMod 2)) := Sylow.ofCard _ hcardP with hP₀
  have hN : Subgroup.normalizer (P₀ : Set (GL (Fin 3) (ZMod 2))) =
      (zeroStabilizer Γ).map φ.symm.toMonoidHom := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.map_mono (le_normalizer_of_subgroupOf_normal hTΓ hTn)).trans
        (Subgroup.le_normalizer_map _)
    · have h1 := Sylow.card_eq_index_normalizer P₀
      rw [h8] at h1
      have h2 := (Subgroup.normalizer (P₀ : Set (GL (Fin 3) (ZMod 2)))).card_mul_index
      rw [← h1, card_GL_three_zmod_two] at h2
      rw [Subgroup.card_map_of_injective φ.symm.injective, hcardΓ₀, hT7]
      omega
  have hmemN : ∀ g : Γ, F g ∈ Subgroup.normalizer (P₀ : Set (GL (Fin 3) (ZMod 2))) ↔
      (g : V ≃ᵃ[ZMod 2] V) 0 = 0 := by
    intro g
    rw [hN]
    constructor
    · rintro ⟨_, ⟨g', ⟨hg'Γ, hg'0⟩, rfl⟩, hFg⟩
      obtain rfl : (⟨g', hg'Γ⟩ : Γ) = g := hLinj (φ.symm.injective hFg)
      exact hg'0
    · intro hg0
      exact ⟨L g, ⟨g, ⟨g.2, hg0⟩, rfl⟩, rfl⟩
  choose gv hgvΓ hgv0 using fun v : V => htrans 0 v
  let κ : V → Sylow 7 (GL (Fin 3) (ZMod 2)) := fun v => F ⟨gv v, hgvΓ v⟩ • P₀
  have hκ : ∀ g : Γ, κ ((g : V ≃ᵃ[ZMod 2] V) 0) = F g • P₀ := by
    intro g
    set k : Γ := g⁻¹ * ⟨gv ((g : V ≃ᵃ[ZMod 2] V) 0), hgvΓ _⟩ with hk
    have hk0 : (k : V ≃ᵃ[ZMod 2] V) 0 = 0 := by
      change (g : V ≃ᵃ[ZMod 2] V).symm (gv ((g : V ≃ᵃ[ZMod 2] V) 0) 0) = 0
      rw [hgv0, AffineEquiv.symm_apply_apply]
    have hkP := Sylow.smul_eq_iff_mem_normalizer.mpr ((hmemN k).mpr hk0)
    have hgk : (⟨gv ((g : V ≃ᵃ[ZMod 2] V) 0), hgvΓ _⟩ : Γ) = g * k := by
      rw [hk, mul_inv_cancel_left]
    change F ⟨gv ((g : V ≃ᵃ[ZMod 2] V) 0), hgvΓ _⟩ • P₀ = F g • P₀
    rw [hgk, map_mul, mul_smul, hkP]
  have hκeq : ∀ (g : Γ) (v : V), κ ((g : V ≃ᵃ[ZMod 2] V) v) = F g • κ v := by
    intro g v
    have hv : (g : V ≃ᵃ[ZMod 2] V) v = ((g * ⟨gv v, hgvΓ v⟩ : Γ) : V ≃ᵃ[ZMod 2] V) 0 := by
      change _ = (g : V ≃ᵃ[ZMod 2] V) (gv v 0)
      rw [hgv0]
    rw [hv, hκ, map_mul, mul_smul]
  have hκinj : Function.Injective κ := by
    intro v w hvw
    set gw : Γ := ⟨gv w, hgvΓ w⟩
    set gvv : Γ := ⟨gv v, hgvΓ v⟩
    have h1 : F (gw⁻¹ * gvv) • P₀ = P₀ := by
      rw [map_mul, mul_smul]
      change (F gw)⁻¹ • κ v = P₀
      rw [hvw]
      exact inv_smul_smul _ _
    have h2 := (hmemN _).mp (Sylow.smul_eq_iff_mem_normalizer.mp h1)
    change (gv w).symm (gv v 0) = 0 at h2
    rw [hgv0, AffineEquiv.symm_apply_eq, hgv0] at h2
    exact h2
  have hκsurj : Function.Surjective κ := by
    intro Q
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) P₀ Q
    obtain ⟨g, rfl⟩ := F.surjective x
    exact ⟨(g : V ≃ᵃ[ZMod 2] V) 0, by rw [hκ, hx]⟩
  let β : V ≃ Omega (ZMod 7) := (Equiv.ofBijective κ ⟨hκinj, hκsurj⟩).trans ℓ
  have hβ : ∀ g : Γ, β.permCongr (g : V ≃ᵃ[ZMod 2] V).toEquiv =
      ℓ.permCongr (MulAction.toPerm (F g)) := by
    intro g
    refine Equiv.ext fun x => ?_
    change ℓ (κ ((g : V ≃ᵃ[ZMod 2] V) ((Equiv.ofBijective κ ⟨hκinj, hκsurj⟩).symm
      (ℓ.symm x)))) = ℓ (F g • ℓ.symm x)
    rw [hκeq]
    congr 2
    exact (Equiv.ofBijective κ ⟨hκinj, hκsurj⟩).apply_symm_apply _
  refine Or.inr ⟨⟨rfl, hbot, hbij, ⟨β, ?_⟩, coordinatePSLAction_range_eq_G (ZMod 7)⟩,
    fun ⟨hA', _⟩ => hA hA'⟩
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    change β.permCongr g.toEquiv ∈ (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))
    rw [show β.permCongr g.toEquiv = _ from hβ ⟨g, hg⟩, SetLike.mem_coe, ← hrange]
    exact ⟨F ⟨g, hg⟩, rfl⟩
  · intro hσ
    rw [SetLike.mem_coe, ← hrange] at hσ
    obtain ⟨x, rfl⟩ := hσ
    obtain ⟨g, rfl⟩ := F.surjective x
    exact ⟨g, g.2, hβ g⟩

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
