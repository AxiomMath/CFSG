module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorField
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorLift
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponentQuadratic

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

section Lift

variable {k : Type*} [Field k] [Finite k] {m : ℕ}

theorem commutator_le_centralizer_of_le (hm : 3 ≤ m) (B : GL (Fin m) k)
    {G : Subgroup (GL (Fin m) k)}
    (hG : G ≤ (centralizer {conjAut m k B}).comap (conjAut m k)) :
    ⁅G, G⁆ ≤ centralizer {B} := by
  have hz : ∀ g : G, (g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹ ∈
      center (GL (Fin m) k) := by
    intro g
    have hc : conjAut m k g * conjAut m k B = conjAut m k B * conjAut m k g :=
      mem_centralizer_singleton_iff.mp (hG g.2)
    have h1 : conjAut m k ((g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    exact ker_conjAut_le_center hm h1
  let φ : G →* center (GL (Fin m) k) :=
    { toFun := fun g => ⟨_, hz g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        have hh := mem_center_iff.mp (hz h) (g : GL (Fin m) k)
        have hh' := mem_center_iff.mp (hz h)
          ((g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹)
        change (g : GL (Fin m) k) * h * B * ((g : GL (Fin m) k) * h)⁻¹ * B⁻¹ =
          (g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹ *
            ((h : GL (Fin m) k) * B * (h : GL (Fin m) k)⁻¹ * B⁻¹)
        calc (g : GL (Fin m) k) * h * B * ((g : GL (Fin m) k) * h)⁻¹ * B⁻¹ =
              (g : GL (Fin m) k) * ((h : GL (Fin m) k) * B * (h : GL (Fin m) k)⁻¹ * B⁻¹) *
                (B * (g : GL (Fin m) k)⁻¹ * B⁻¹) := by group
          _ = (h : GL (Fin m) k) * B * (h : GL (Fin m) k)⁻¹ * B⁻¹ * (g : GL (Fin m) k) *
                (B * (g : GL (Fin m) k)⁻¹ * B⁻¹) := by rw [hh]
          _ = (h : GL (Fin m) k) * B * (h : GL (Fin m) k)⁻¹ * B⁻¹ *
                ((g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹) := by group
          _ = _ := hh'.symm) }
  have hker : commutator G ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [← Subgroup.map_subtype_commutator]
  rintro _ ⟨g, hg, rfl⟩
  have h1 := congrArg Subtype.val (show φ g = 1 from hker hg)
  change (g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹ = 1 at h1
  rw [mem_centralizer_singleton_iff]
  change (g : GL (Fin m) k) * B = B * g
  calc (g : GL (Fin m) k) * B = (g : GL (Fin m) k) * B * (g : GL (Fin m) k)⁻¹ * B⁻¹ *
        (B * (g : GL (Fin m) k)) := by group
    _ = B * g := by rw [h1, one_mul]

theorem inner_component_lift (hm : 3 ≤ m) (B : GL (Fin m) k)
    {X : Subgroup (MulAut (projectiveSL m k))}
    (hX : CFSG.Assembly.IsComponentOf X
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {conjAut m k B})) :
    CFSG.Assembly.IsComponentOf ⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆ (centralizer {B}) ∧
      (⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆).map (conjAut m k) = X ∧
      ⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆ ≤
        (OuterAutomorphisms.inner (projectiveSL m k)).comap (conjAut m k) := by
  set c := conjAut m k with hc
  set H := OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {c B} with hH
  obtain ⟨hXh, hmap⟩ := component_lift hm (H := H) inf_le_left hX
  set Xh := ⁅X.comap c, X.comap c⁆ with hXhdef
  have hGc : H.comap c ≤ (centralizer {c B}).comap c := comap_mono inf_le_right
  have hXhC : Xh ≤ centralizer {B} :=
    (commutator_mono (comap_mono hX.1) (comap_mono hX.1)).trans
      (commutator_le_centralizer_of_le hm B hGc)
  have hXhI : Xh ≤ (OuterAutomorphisms.inner (projectiveSL m k)).comap c :=
    hXh.1.trans (comap_mono inf_le_left)
  refine ⟨?_, hmap, hXhI⟩
  have hCB : centralizer {B} ≤ (centralizer {c B}).comap c := by
    intro g hg
    rw [mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp hg]
  have hX₁ : CFSG.Assembly.IsComponentOf Xh
      ((OuterAutomorphisms.inner (projectiveSL m k)).comap c ⊓ centralizer {B}) := by
    refine isComponentOf_of_le hXh (le_inf hXhI hXhC) ?_
    intro g hg
    exact ⟨hg.1, hCB hg.2⟩
  have hnormal : ((OuterAutomorphisms.inner (projectiveSL m k)).comap c).Normal :=
    (OuterAutomorphisms.inner_normal (projectiveSL m k)).comap c
  refine ⟨hX₁.1.trans inf_le_right, assembly_isSubnormal_trans hX₁.2.1
    (CFSG.Assembly.IsSubnormal.step inf_le_right ?_ (CFSG.Assembly.IsSubnormal.refl _)), hX₁.2.2⟩
  rw [inf_subgroupOf_right]
  exact hnormal.subgroupOf _

end Lift

section SLTwo

variable {k : Type} [Field k]

theorem exists_two_involutions_of_pRank {H : Type*} [Group H] [Finite H]
    (h : 2 ≤ CFSG.pRank 2 H) :
    ∃ x y : H, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 := by
  classical
  set S := {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} with hS
  have hbot : IsElementaryAbelian 2 (⊥ : Subgroup H) :=
    { is_comm := ⟨fun a b => Subsingleton.elim _ _⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subsingleton.elim _ _ }
  have hne : S.Nonempty := ⟨0, ⊥, hbot, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card H, fun r hr => ?_⟩
    obtain ⟨A, -, hA⟩ := hr
    have h1 : 2 ^ r ≤ Nat.card H := hA ▸ Subgroup.card_le_card_group A
    exact (Nat.lt_two_pow_self).le.trans h1
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  have h4 : 4 ≤ Nat.card A := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ sSup S := Nat.pow_le_pow_right (by norm_num) h
  have hsq : ∀ a : A, a ^ 2 = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have h1 : 1 < ((Set.univ : Set A) \ {1}).ncard := by
    have hu : (Set.univ : Set A).ncard = Nat.card A := Set.ncard_univ A
    have := Set.ncard_sdiff_singleton_of_mem (s := (Set.univ : Set A)) (a := 1) (Set.mem_univ _)
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1
  refine ⟨a, b, fun h => ha.2 (OneMemClass.coe_eq_one.mp h),
    fun h => hb.2 (OneMemClass.coe_eq_one.mp h), fun h => hab (Subtype.ext h), ?_, ?_⟩
  · exact congrArg Subtype.val (hsq a)
  · exact congrArg Subtype.val (hsq b)

theorem not_rank_or_odd_center_of_sl_two [Finite k] (hk2 : ringChar k ≠ 2) {L : Type*} [Group L]
    [Finite L] (e : L ≃* SpecialLinearGroup (Fin 2) k) :
    ¬ (2 ≤ CFSG.pRank 2 L ∨ Odd (Nat.card (center L))) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hm1 : (-1 : SpecialLinearGroup (Fin 2) k) ≠ 1 := by
    intro h
    apply QuaternionMatrices.neg_one_ne_one_matrix hk2
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k)) h
    simpa using this
  have hex : ∀ z : L, z ≠ 1 → z ^ 2 = 1 → e z = -1 := by
    intro z hz hz2
    have hA := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (e z) (by rw [← map_pow, hz2, map_one])
      (fun h1 => hz (e.injective (by rw [h1, map_one])))
    apply Subtype.ext
    rw [hA]
    simp
  rintro (h | h)
  · obtain ⟨x, y, hx, hy, hxy, hx2, hy2⟩ := exists_two_involutions_of_pRank h
    exact hxy (e.injective ((hex x hx hx2).trans (hex y hy hy2).symm))
  ·
    have hz : e.symm (-1) ∈ center L := by
      rw [mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      simp
    have hz2 : e.symm (-1) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one]
      apply Subtype.ext
      simp [sq]
    have hz1 : e.symm (-1) ≠ 1 := fun h1 => hm1 (by
      have := congrArg e h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this)
    have hord : orderOf (⟨e.symm (-1), hz⟩ : center L) = 2 := by
      refine orderOf_eq_prime (Subtype.ext ?_) (fun h1 => hz1 (congrArg Subtype.val h1))
      exact hz2
    have hdvd : 2 ∣ Nat.card (center L) := hord ▸ orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hdvd)

end SLTwo

section Square

variable {k : Type} [Field k] [Finite k] {m : ℕ}

omit [Finite k] in
theorem mulEquiv_of_lift_injective {A : Type} [Group A] {L : Subgroup A}
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    {Xh : Subgroup (GL (Fin m) k)} (hmap : Xh.map (conjAut m k) = L.map ρ)
    (hXi : Function.Injective ((conjAut m k).comp Xh.subtype)) : Nonempty (L ≃* Xh) := by
  have hrange : ((conjAut m k).comp Xh.subtype).range = L.map ρ := by
    rw [MonoidHom.range_comp, range_subtype, hmap]
  exact ⟨(L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hrange).symm.trans
    (MonoidHom.ofInjective hXi).symm)⟩

theorem square_component_sl (hm : 3 ≤ m) (htwo : (2 : k) ≠ 0) {B : GL (Fin m) k} {c₀ : kˣ}
    (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) (c₀ ^ 2))
    (hB1 : ∀ c : kˣ, B ≠ GeneralLinearGroup.scalar (Fin m) c) {Xh : Subgroup (GL (Fin m) k)}
    (hXh : CFSG.Assembly.IsComponentOf Xh (centralizer {B})) :
    ∃ r : ℕ, 2 ≤ r ∧ Nonempty (Xh ≃* SpecialLinearGroup (Fin r) k) ∧
      Function.Injective ((conjAut m k).comp Xh.subtype) := by
  have hL' : CFSG.IsComponent (Xh.subgroupOf (centralizer {B})) :=
    (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
  have hcore : ∀ c : kˣ, B ^ 2 = GeneralLinearGroup.scalar (Fin m) (c ^ 2) →
      (∀ x ∈ Xh.subgroupOf (centralizer {B}), ∀ w ∈ (splitMatrixOperator B).eigenspace (-c.val),
        ((x : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ w = w) →
      ∃ r : ℕ, 2 ≤ r ∧ Nonempty (Xh ≃* SpecialLinearGroup (Fin r) k) ∧
        Function.Injective ((conjAut m k).comp Xh.subtype) := by
    intro c hsqc hfix
    have hcompl := squareScalar_eigenspaces_isCompl (splitMatrixOperator B) c.val c.ne_zero htwo
      (splitMatrixOperator_square B c hsqc)
    have hW : (splitMatrixOperator B).eigenspace (-c.val) ≠ ⊥ := by
      intro hW
      have htop : (splitMatrixOperator B).eigenspace c.val = ⊤ := by
        have := hcompl.sup_eq_top
        rwa [hW, sup_bot_eq] at this
      apply hB1 c
      apply Units.ext
      refine ProjectiveEigenspace.matrix_eq_of_mulVec_eq fun v => ?_
      have hv : v ∈ (splitMatrixOperator B).eigenspace c.val := htop ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      change (B : Matrix (Fin m) (Fin m) k) *ᵥ v = c.val • v at hv
      rw [hv, GeneralLinearGroup.coe_scalar]
      ext i
      simp [scalar_apply, mulVec_diagonal]
    have hA : (splitMatrixOperator B).eigenspace c.val ≠ ⊥ := by
      intro hA
      have htop : (splitMatrixOperator B).eigenspace (-c.val) = ⊤ := by
        have := hcompl.sup_eq_top
        rwa [hA, bot_sup_eq] at this
      have : Nontrivial (Xh.subgroupOf (centralizer {B})) :=
        CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
      obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Xh.subgroupOf (centralizer {B}))
      apply hx1
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      refine ProjectiveEigenspace.matrix_eq_of_mulVec_eq fun v => ?_
      rw [hfix x hx v (htop ▸ Submodule.mem_top)]
      simp
    obtain ⟨hmapsl, hr2⟩ := ProjectiveEigenspace.splitFst_map_eq htwo hsqc hL' hfix hA
    set r := positiveMatrixDimension B c.val
    refine ⟨r, hr2, ?_, ?_⟩
    ·
      set f := (ProjectiveEigenspace.splitFst htwo hsqc).comp
        (Xh.subgroupOf (centralizer {B})).subtype
      have hf : Function.Injective f := fun x y hxy =>
        Subtype.ext (ProjectiveEigenspace.splitFst_injOn htwo hsqc hfix x.2 y.2 hxy)
      have hfr : f.range = CatalogueBGeneralLinear.specialLinearRange r k := by
        rw [MonoidHom.range_comp, range_subtype, hmapsl]
      exact ⟨(subgroupOfEquivOfLe hXh.1).symm.trans ((MonoidHom.ofInjective hf).trans
        ((MulEquiv.subgroupCongr hfr).trans
          (CatalogueBGeneralLinear.rangeEquivSpecialLinear r k)))⟩
    ·
      rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨t, ht⟩ := (conjAut_eq_one_iff hm _).mp hx
      have hxW : ∀ w ∈ (splitMatrixOperator B).eigenspace (-c.val),
          (((x : GL (Fin m) k)) : Matrix (Fin m) (Fin m) k) *ᵥ w = w :=
        hfix ⟨x, hXh.1 x.2⟩ x.2
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      have h1 := hxW w hw
      change ((Xh.subtype x : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ w = w at h1
      rw [← ht, GeneralLinearGroup.coe_scalar] at h1
      have ht1 : t = 1 := by
        apply Units.ext
        have h3 : (t.val - 1) • w = 0 := by
          rw [sub_smul, one_smul]
          have : (scalar (Fin m) (t : k)) *ᵥ w = t.val • w := by
            ext i
            simp [scalar_apply, mulVec_diagonal]
          rw [← this, h1, sub_self]
        rw [Units.val_one, ← sub_eq_zero]
        exact (smul_eq_zero.mp h3).resolve_right hw0
      apply Subtype.ext
      change Xh.subtype x = 1
      rw [← ht, ht1, map_one]
  rcases ProjectiveEigenspace.fix_or_fix_of_isComponent htwo hsq hL' with h | h
  · exact hcore c₀ hsq h
  · refine hcore (-c₀) (by rw [neg_sq]; exact hsq) ?_
    intro x hx w hw
    have hw' : w ∈ (splitMatrixOperator B).eigenspace c₀.val := by
      simpa only [Units.val_neg, neg_neg] using hw
    exact h x hx w hw'

end Square

section Nonsquare

variable {k : Type} [Field k] [Finite k] {m : ℕ}

theorem nonsquare_component_sl (htwo : (2 : k) ≠ 0) {B : GL (Fin m) k} {μ : kˣ}
    [Fact (¬ IsSquare μ.val)] (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    {Xh : Subgroup (GL (Fin m) k)} (hXh : CFSG.Assembly.IsComponentOf Xh (centralizer {B})) :
    2 ≤ matrixDimension B μ hsq ∧
      (Xh.subgroupOf (centralizer {B})).map (matrixCentralizerQuadraticEquiv B μ hsq).toMonoidHom =
        CatalogueBGeneralLinear.specialLinearRange (matrixDimension B μ hsq) (extension μ.val) := by
  have hL' : CFSG.IsComponent (Xh.subgroupOf (centralizer {B})) :=
    (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
  have hm0 : Nonempty (Fin m) := by
    by_contra h0
    have : IsEmpty (Fin m) := not_nonempty_iff.mp h0
    have : Nontrivial (Xh.subgroupOf (centralizer {B})) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
    obtain ⟨x, hx1⟩ := exists_ne (1 : Xh.subgroupOf (centralizer {B}))
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i
    exact isEmptyElim i
  let _ := matrixModule B μ hsq
  have : Finite (extension μ.val) := quadraticExtension_finite μ.val
  set d := matrixDimension B μ hsq with hd
  have hd1 : 1 ≤ d := matrixDimension_pos B μ hsq
  have hL'' := isComponent_map_of_isComponent (matrixCentralizerQuadraticEquiv B μ hsq) hL'
  set L'' := (Xh.subgroupOf (centralizer {B})).map
    (matrixCentralizerQuadraticEquiv B μ hsq).toMonoidHom
  have : Group.IsPerfect L'' := hL''.1.1
  have : Nontrivial L'' := CFSG.LocalCores.isQuasisimple_nontrivial hL''.1
  have hcardE : Nat.card (extension μ.val) = Nat.card k ^ 2 := by
    let : Fintype k := Fintype.ofFinite k
    let : Fintype (extension μ.val) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
      extension_finrank]
  have hK3 := ProjectiveEigenspace.three_le_card_of_two_ne_zero htwo
  have hE9 : 9 ≤ Nat.card (extension μ.val) := by
    rw [hcardE]
    nlinarith
  have hsmall : ¬ (d = 1 ∨ d = 2 ∧
      (Nat.card (extension μ.val) = 2 ∨ Nat.card (extension μ.val) = 3)) := by
    rintro (h1 | ⟨-, h2 | h2⟩)
    · have : Group.IsSolvable (GL (Fin d) (extension μ.val)) :=
        CatalogueBGeneralLinear.generalLinear_small_solvable d (extension μ.val) (Or.inl h1)
      exact Group.IsPerfect.not_isSolvable L'' inferInstance
    · omega
    · omega
  obtain ⟨hd2, h22, h23⟩ :=
    CatalogueBGeneralLinear.retained_parameters d (extension μ.val) hd1 hsmall
  exact ⟨hd2, CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange d
    (extension μ.val) hd2 h22 h23 L'' hL''.2⟩

@[expose] def nonsquareCover {B : GL (Fin m) k} {μ : kˣ} [Fact (¬ IsSquare μ.val)]
    (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ) :
    SpecialLinearGroup (Fin (matrixDimension B μ hsq)) (extension μ.val) →* GL (Fin m) k :=
  (centralizer {B}).subtype.comp
    ((matrixCentralizerQuadraticEquiv B μ hsq).symm.toMonoidHom.comp SpecialLinearGroup.toGL)

omit [Finite k] in
theorem mem_center_of_nonsquareCover_scalar {B : GL (Fin m) k} {μ : kˣ}
    [Fact (¬ IsSquare μ.val)] (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ)
    {x : SpecialLinearGroup (Fin (matrixDimension B μ hsq)) (extension μ.val)} {t : kˣ}
    (ht : GeneralLinearGroup.scalar (Fin m) t = nonsquareCover hsq x) :
    x ∈ center (SpecialLinearGroup (Fin (matrixDimension B μ hsq)) (extension μ.val)) := by
  set e := matrixCentralizerQuadraticEquiv B μ hsq
  have h1 : e.symm (SpecialLinearGroup.toGL x) = ordinaryCentralizerScalar B t :=
    Subtype.ext ht.symm
  have h2 : SpecialLinearGroup.toGL x = GeneralLinearGroup.scalar _
      (Units.map (algebraMap k (extension μ.val)).toMonoidHom t) := by
    rw [← matrixCentralizerQuadraticEquiv_scalar B μ hsq t, ← h1, MulEquiv.apply_symm_apply]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨algebraMap k (extension μ.val) t, ?_, ?_⟩
  · have hdet := congrArg (fun g : GL (Fin (matrixDimension B μ hsq)) (extension μ.val) =>
      (g : Matrix (Fin (matrixDimension B μ hsq)) (Fin (matrixDimension B μ hsq))
        (extension μ.val)).det) h2
    have hx1 : (x : Matrix (Fin (matrixDimension B μ hsq)) (Fin (matrixDimension B μ hsq))
        (extension μ.val)).det = 1 := x.2
    simp only [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hx1] at hdet
    rw [Fintype.card_fin]
    exact hdet.symm
  · have := congrArg (fun g : GL (Fin (matrixDimension B μ hsq)) (extension μ.val) =>
      (g : Matrix (Fin (matrixDimension B μ hsq)) (Fin (matrixDimension B μ hsq))
        (extension μ.val))) h2
    simp only [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar] at this
    rw [this]
    simp

end Nonsquare

section InnerCase

variable {A : Type} [Group A] [Finite A] {a : A} {L : Subgroup A}

theorem statedClassicalModel_psl_two {k : Type} [Field k] [Finite k] {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e) (h2 : ℓ ^ e ≠ 2) (h3 : ℓ ^ e ≠ 3) :
    StatedClassicalModel (StatedProj (StatedSL 2 k)) .PSL 2 ℓ e :=
  ⟨⟨hℓ, he, le_rfl, fun h => h2 (by simpa using h), fun h => h3 (by simpa using h)⟩, k,
    inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩

theorem inner_case_reduction (ha : orderOf a = 2) {m ℓ e : ℕ} (hm : 4 ≤ m) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} (hρa : ρ a = conjAut m k B) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hrank : StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      2 ≤ CFSG.pRank 2 L ∨ Odd (Nat.card (center L))) :
    ∃ μ : kˣ, ¬ IsSquare μ.val ∧ B ^ 2 = GeneralLinearGroup.scalar (Fin m) μ ∧ m = 4 := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hm3 : 3 ≤ m := by omega
  have h2 : conjAut m k (B ^ 2) = 1 := by
    rw [map_pow, ← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hm3 _).mp h2
  have hB1 : ∀ c : kˣ, B ≠ GeneralLinearGroup.scalar (Fin m) c := by
    intro c hc
    have h1 : ρ a = 1 := by rw [hρa, hc, conjAut_scalar]
    rw [← map_one ρ] at h1
    rw [hinj h1, orderOf_one] at ha
    omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := inner_component_lift hm3 B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut m k), (L.map ρ).comap (conjAut m k)⁆ with hXhdef
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_commute_of_isQuasisimple hL₁.2.2
    set eρ := L.equivMapOfInjective ρ hinj
    refine ⟨eρ.symm x, eρ.symm y, fun hc => hxy ?_⟩
    have := congrArg eρ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  by_cases hμs : IsSquare μ.val
  ·
    exfalso
    obtain ⟨r₀, hr₀⟩ := hμs
    have hr0 : r₀ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr₀
      exact μ.ne_zero hr₀
    set c₀ : kˣ := Units.mk0 r₀ hr0
    have hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) (c₀ ^ 2) := by
      rw [← hμ]
      congr 1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr₀, sq]
    obtain ⟨r, hr2, ⟨eX⟩, hXi⟩ := square_component_sl hm3 htwo hsq hB1 hXh
    obtain ⟨eL⟩ := mulEquiv_of_lift_injective hinj hmap hXi
    set eLS := eL.trans eX
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    ·
      have hq3 : Nat.card k ≠ 3 := by
        intro h3
        have : Group.IsSolvable (GL (Fin 2) k) :=
          CatalogueBGeneralLinear.generalLinear_small_solvable 2 k (Or.inr ⟨rfl, Or.inr h3⟩)
        have : Group.IsSolvable (SpecialLinearGroup (Fin 2) k) :=
          Group.isSolvable_of_isSolvable_injective SpecialLinearGroup.toGL_injective
        have : Group.IsSolvable L :=
          Group.isSolvable_of_isSolvable_injective (f := eLS.toMonoidHom) eLS.injective
        have hq := hL₁.2.2
        have hL' : CFSG.Assembly.IsQuasisimple L :=
          (AssemblyBPredicates.isQuasisimple_iff_native L).2
            ((LocalAnalysis.ComponentInitial.isQuasisimple_congr
              (L.equivMapOfInjective ρ hinj)).2
              ((AssemblyBPredicates.isQuasisimple_iff_native _).1 hq))
        have : Group.IsPerfect L := ⟨hL'.1⟩
        have : Nontrivial L := by
          obtain ⟨x, y, hxy⟩ := hLnab
          exact nontrivial_of_ne (x * y) (y * x) hxy
        exact Group.IsPerfect.not_isSolvable L inferInstance
      have hq2 : Nat.card k ≠ 2 := by
        intro h
        apply htwo
        have := Fintype.ofFinite k
        have h0 := FiniteField.cast_card_eq_zero k
        rw [← Nat.card_eq_fintype_card, h] at h0
        exact_mod_cast h0
      have eQ : L ⧸ center L ≃* StatedProj (StatedSL 2 k) :=
        (QuotientGroup.congr (center L) (center (SpecialLinearGroup (Fin 2) k)) eLS
          (Subgroup.map_center_eq eLS)).trans
          (projectiveSpecialLinearGroupEquivStatedProj 2 k)
      have hX : StatedClassicalModel (L ⧸ center L) .PSL 2 ℓ e :=
        SectionRank.statedClassicalModel_of_mulEquiv eQ
          (statedClassicalModel_psl_two hℓ he hk (by rw [← hk]; exact hq2)
            (by rw [← hk]; exact hq3))
      obtain ⟨-, h7, h34⟩ :=
        UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hX
      rcases hsrc with h | h | h
      · exact not_rank_or_odd_center_of_sl_two hk2 eLS (hrank h)
      · exact not_nonempty_iff.mpr h7 h
      · exact h34 h
    ·
      have hker : eLS.symm.toMonoidHom.ker ≤ center (SpecialLinearGroup (Fin r) k) := by
        intro x hx
        have : x = 1 := eLS.symm.injective (by rw [map_one]; exact hx)
        rw [this]
        exact one_mem _
      exact false_of_not_small_source
        (not_small_source_of_sl_cover hr3 hℓ hℓ2 he hk eLS.symm.toMonoidHom hker) hp2 hsrc
  ·
    have : Fact (¬ IsSquare μ.val) := ⟨hμs⟩
    refine ⟨μ, hμs, hμ.symm, ?_⟩
    obtain ⟨hd2, hmapE⟩ := nonsquare_component_sl htwo hμ.symm hXh
    set d := matrixDimension B μ hμ.symm with hd
    have hmd : m = 2 * d := by
      have := matrixDimension_twice B μ hμ.symm
      rwa [Fintype.card_fin] at this
    by_contra hm4
    have hd3 : 3 ≤ d := by omega
    have : Finite (extension μ.val) := quadraticExtension_finite μ.val
    have hcardE : Nat.card (extension μ.val) = ℓ ^ (2 * e) := by
      let _ := matrixModule B μ hμ.symm
      let : Fintype k := Fintype.ofFinite k
      let : Fintype (extension μ.val) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k), extension_finrank,
        ← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
    set σ₀ := nonsquareCover hμ.symm with hσ₀
    have hσ₀X : ∀ x, σ₀ x ∈ Xh := by
      intro x
      have hx : SpecialLinearGroup.toGL x ∈ CatalogueBGeneralLinear.specialLinearRange d
          (extension μ.val) := ⟨x, rfl⟩
      rw [← hmapE] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : (matrixCentralizerQuadraticEquiv B μ hμ.symm).symm
          (SpecialLinearGroup.toGL x) = y := by
        rw [← hyx]
        exact MulEquiv.symm_apply_apply _ _
      change ((matrixCentralizerQuadraticEquiv B μ hμ.symm).symm (SpecialLinearGroup.toGL x) :
        GL (Fin m) k) ∈ Xh
      rw [this]
      exact hy
    have hσL : ∀ x, conjAut m k (σ₀ x) ∈ L.map ρ := by
      intro x
      rw [← hmap]
      exact ⟨σ₀ x, hσ₀X x, rfl⟩
    set σ : SpecialLinearGroup (Fin d) (extension μ.val) →* L :=
      (L.equivMapOfInjective ρ hinj).symm.toMonoidHom.comp
        (((conjAut m k).comp σ₀).codRestrict (L.map ρ) hσL) with hσdef
    have hker : σ.ker ≤ center (SpecialLinearGroup (Fin d) (extension μ.val)) := by
      intro x hx
      have h1 : conjAut m k (σ₀ x) = 1 := by
        have : (L.equivMapOfInjective ρ hinj).symm
            ((((conjAut m k).comp σ₀).codRestrict (L.map ρ) hσL) x) = 1 := hx
        rw [MulEquiv.map_eq_one_iff] at this
        exact congrArg Subtype.val this
      obtain ⟨t, ht⟩ := (conjAut_eq_one_iff hm3 _).mp h1
      exact mem_center_of_nonsquareCover_scalar hμ.symm ht
    exact false_of_not_small_source
      (not_small_source_of_sl_cover hd3 hℓ hℓ2 (by omega) hcardE σ hker) hp2 hsrc

end InnerCase

end CFSG.ComponentClassification.OddSelector
