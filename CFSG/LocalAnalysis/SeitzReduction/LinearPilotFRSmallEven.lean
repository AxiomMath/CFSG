module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallOdd
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.Quasithin (perfectCore map_perfectCore le_perfectCore_of_perfect)
open scoped commutatorElement

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

variable (K) in
@[expose] def coreRadicalP : Subgroup (projectiveSL n K) :=
  perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ⊓ P.radicalP K

theorem transvection_u_w_mem_commutator_leviOne {a b : Fin k} (hab : a ≠ b) (c : K) :
    SpecialLinearGroup.transvection (P.u_ne_w a b) c ∈ ⁅P.leviOne K, P.radical K⁆ := by
  have key : ⁅P.leviOneHom K (Matrix.SpecialLinearGroup.transvection hab 1),
      Matrix.SpecialLinearGroup.transvection (P.u_ne_w b b) c⁆ =
      Matrix.SpecialLinearGroup.transvection (P.u_ne_w a b) c := by
    rw [leviOneHom_transvection, commutatorElement_mul_left_of_commute
      (Matrix.SpecialLinearGroup.commute_transvection _ _ (P.u_ne_w b b).symm
        (P.w_injective.ne hab.symm) 1 c),
      Matrix.SpecialLinearGroup.commutatorElement_transvection _ _ (P.u_ne_w a b) 1 c, one_mul]
  rw [← key]
  exact Subgroup.commutator_mem_commutator ⟨_, rfl⟩
    (P.transvection_mem_radical _ (by rw [level_u, level_w]; omega) c)

variable [CharP K 2]

theorem proj_transvection_u_w_mem_coreRadicalP [Finite K] (hq : 4 ≤ Nat.card K)
    {a b : Fin k} (hab : a ≠ b) (c : K) :
    proj n K (SpecialLinearGroup.transvection (P.u_ne_w a b) c) ∈ P.coreRadicalP K := by
  refine ⟨commutator_leviOneP_radicalP_le hq P ?_, Subgroup.mem_map_of_mem _
    (P.transvection_mem_radical _ (by rw [level_u, level_w]; omega) c)⟩
  rw [leviOneP, radicalP, ← Subgroup.map_commutator]
  exact Subgroup.mem_map_of_mem _ (P.transvection_u_w_mem_commutator_leviOne hab c)

omit [CharP K 2] in
theorem map_core_le_normalizer_radicalP :
    (P.core K).map (proj n K) ≤ normalizer (P.radicalP K : Set (projectiveSL n K)) :=
  (Subgroup.map_mono ((P.core_le_centralizer.trans P.centralizer_le_parabolic).trans
    P.parabolic_le_normalizer_radical)).trans (Subgroup.le_normalizer_map _)

theorem le_radicalP_of_isPGroup_of_free_eq_empty' [Finite K] (hq : 4 ≤ Nat.card K)
    (hk : 0 < k) (hJ : P.free = ∅) {T : Subgroup (projectiveSL n K)} (hT : IsPGroup 2 T)
    (hTΛ : T ≤ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
    (hN : perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
      normalizer (T : Set (projectiveSL n K))) :
    T ≤ P.radicalP K := by
  have hΛcore := perfectCore_centralizer_elt_le_map_core (K := K) P
  have hTN : T ≤ normalizer (P.radicalP K : Set (projectiveSL n K)) :=
    hTΛ.trans (hΛcore.trans P.map_core_le_normalizer_radicalP)
  have hcore : (P.core K).map (proj n K) = P.radicalP K ⊔ P.leviOneP K := by
    rw [map_core_eq, blockSL_eq_bot_of_card_le_one (by rw [hJ]; simp), sup_bot_eq]
  set T₁ := P.radicalP K ⊔ T with hT₁
  have hT₁p : IsPGroup 2 T₁ := IsPGroup.to_sup_of_normal_left' P.isPGroup_radicalP hT hTN
  have hT₁Λ : T₁ ≤ (P.core K).map (proj n K) :=
    sup_le (Subgroup.map_mono P.radical_le_core) (hTΛ.trans hΛcore)
  have hN₁ : (P.core K).map (proj n K) ≤ normalizer (T₁ : Set (projectiveSL n K)) := by
    rw [hcore]
    refine sup_le (le_sup_left.trans le_normalizer) ?_
    have h1 : P.leviOneP K ≤ normalizer (P.radicalP K : Set (projectiveSL n K)) := by
      have h := P.levi_le_normalizer_radicalP (K := K)
      rw [blockSL_eq_bot_of_card_le_one (by rw [hJ]; simp), sup_bot_eq] at h
      exact h
    have h2 : P.leviOneP K ≤ normalizer (T : Set (projectiveSL n K)) :=
      (leviOneP_le_perfectCore hq P).trans hN
    exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  exact le_sup_right.trans (P.le_radicalP_of_isPGroup_of_free_eq_empty hq hk hJ hT₁p hT₁Λ hN₁)

theorem coreRadicalP_spec [Finite K] (hq : 4 ≤ Nat.card K) (hk : 0 < k) (hJ : P.free = ∅) :
    IsPGroup 2 (P.coreRadicalP K) ∧
      P.coreRadicalP K ≤ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ∧
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
        normalizer (P.coreRadicalP K : Set (projectiveSL n K)) ∧
      (∀ T : Subgroup (projectiveSL n K), IsPGroup 2 T →
        T ≤ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) →
        perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
          normalizer (T : Set (projectiveSL n K)) → T ≤ P.coreRadicalP K) ∧
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) =
        P.coreRadicalP K ⊔ P.leviOneP K ∧
      P.leviOneP K ≤ normalizer (P.coreRadicalP K : Set (projectiveSL n K)) ∧
      Disjoint (P.coreRadicalP K) (P.leviOneP K) := by
  set Λ := perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) with hΛdef
  have hΛcore := perfectCore_centralizer_elt_le_map_core (K := K) P
  have hcore : (P.core K).map (proj n K) = P.radicalP K ⊔ P.leviOneP K := by
    rw [map_core_eq, blockSL_eq_bot_of_card_le_one (by rw [hJ]; simp), sup_bot_eq]
  have hMΛ : P.leviOneP K ≤ Λ := leviOneP_le_perfectCore hq P
  have hΛN : Λ ≤ normalizer (P.coreRadicalP K : Set (projectiveSL n K)) :=
    (le_inf le_normalizer (hΛcore.trans P.map_core_le_normalizer_radicalP)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hMN : P.leviOneP K ≤ normalizer (P.radicalP K : Set (projectiveSL n K)) := by
    have h := P.levi_le_normalizer_radicalP (K := K)
    rw [blockSL_eq_bot_of_card_le_one (by rw [hJ]; simp), sup_bot_eq] at h
    exact h
  refine ⟨P.isPGroup_radicalP.to_le inf_le_right, inf_le_left, hΛN,
    fun T hT hTΛ hN => le_inf hTΛ (P.le_radicalP_of_isPGroup_of_free_eq_empty' hq hk hJ hT hTΛ hN),
    le_antisymm ?_ (sup_le inf_le_left hMΛ), hMΛ.trans hΛN,
    P.disjoint_radicalP.mono inf_le_right le_sup_left⟩
  intro x hx
  have hx' : x ∈ ((P.radicalP K ⊔ P.leviOneP K : Subgroup (projectiveSL n K)) :
      Set (projectiveSL n K)) := by
    rw [← hcore]
    exact hΛcore hx
  rw [coe_mul_of_right_le_normalizer_left _ _ hMN] at hx'
  obtain ⟨r, hr, m, hm, rfl⟩ := hx'
  have hrΛ : r ∈ Λ := by
    have : r = (r * m) * m⁻¹ := by group
    rw [this]
    exact Λ.mul_mem hx (Λ.inv_mem (hMΛ hm))
  exact Subgroup.mul_mem_sup ⟨hrΛ, hr⟩ hm

theorem blockTriangular_of_conjAut_of_free_eq_empty (hk : 2 ≤ k) (hJ : P.free = ∅)
    (B : GL (Fin n) K)
    (hB : ∀ a b : Fin k, a ≠ b → ∀ c : K,
      conjAut n K B (proj n K (SpecialLinearGroup.transvection (P.u_ne_w a b) c)) ∈
        P.radicalP K) :
    (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level := by
  intro i j hij
  have hlev : ∀ l, P.level l ≠ 1 := fun l h => by
    have := P.mem_free.2 h
    rw [hJ] at this
    exact Finset.notMem_empty l this
  have hi2 := P.level_le_two i
  have hj0 : P.level j = 0 := by have := hlev j; omega
  have hi : P.level i = 2 := by have := hlev i; omega
  obtain ⟨x, rfl⟩ := P.level_eq_two_iff.1 hi
  obtain ⟨y, rfl⟩ := P.level_eq_zero_iff.1 hj0
  obtain ⟨z, hzy⟩ : ∃ z : Fin k, z ≠ y := by
    by_cases h : y = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [h, Fin.ext_iff] at h'; simp at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  have hR := P.slConjugation_transvection_mem_radical B (P.u_ne_w y z) 1 (hB y z hzy.symm 1)
  have hzero : ∀ b : Fin n, ((B : Matrix (Fin n) (Fin n) K) *
      (single (P.u y) (P.w z) 1 : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (P.w x) b = 0 := fun b =>
    P.conj_single_apply_eq_zero B (P.u_ne_w y z) hR (a := P.w x) (b := b)
      (by rw [level_w]; exact P.level_le_two b)
  have h1 : (B : Matrix (Fin n) (Fin n) K) * (single (P.u y) (P.w z) 1 :
      Matrix (Fin n) (Fin n) K) =
      ((B : Matrix (Fin n) (Fin n) K) * (single (P.u y) (P.w z) 1 : Matrix (Fin n) (Fin n) K) *
        ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (B : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_assoc _ ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (P.w x)) (P.w z)
  rw [mul_single_apply_same, mul_one, mul_apply] at h2
  rw [h2]
  exact Finset.sum_eq_zero fun l _ => by rw [hzero l, zero_mul]

omit [CharP K 2] in
theorem map_mat (σ : K →+* K) : SpecialLinearGroup.map σ (P.mat K) = P.mat K := by
  ext i j
  change σ ((P.mat K : Matrix (Fin n) (Fin n) K) i j) = (P.mat K : Matrix (Fin n) (Fin n) K) i j
  rw [coe_mat, Matrix.add_apply, map_add, one_apply]
  simp only [nil, of_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem nil_outerSwap (i j : Fin n) :
    P.nil K ((P.outerSwap) j) ((P.outerSwap) i) = P.nil K i j := by
  have h : (∃ a, P.u a = (P.outerSwap) j ∧ P.w a = (P.outerSwap) i) ↔
      ∃ a, P.u a = i ∧ P.w a = j := by
    constructor
    · rintro ⟨a, h1, h2⟩
      refine ⟨a, ?_, ?_⟩
      · have := congrArg P.outerSwap h2
        rwa [outerSwap_w, outerSwap_outerSwap] at this
      · have := congrArg P.outerSwap h1
        rwa [outerSwap_u, outerSwap_outerSwap] at this
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨a, (P.outerSwap_w a).symm, (P.outerSwap_u a).symm⟩
  simp only [nil, of_apply, h]

omit [CharP K 2] in
theorem fieldAut_elt (σ : K ≃+* K) : fieldAut n K σ (P.elt K) = P.elt K := by
  rw [elt, fieldAut_proj, map_mat]

theorem graphTwist_elt (σ : K ≃+* K) :
    (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K) (P.elt K) = P.elt K := by
  rw [elt, MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, outerSwapGL_mul_mul_inv, inv_eq_of_mul_eq_one_right P.mat_mul_self]
  ext i j
  change σ ((P.mat K : Matrix (Fin n) (Fin n) K) ((P.outerSwap) j) ((P.outerSwap) i)) =
    (P.mat K : Matrix (Fin n) (Fin n) K) i j
  rw [coe_mat, Matrix.add_apply, Matrix.add_apply, map_add, nil_outerSwap, one_apply, one_apply]
  have hij : ((P.outerSwap) j = (P.outerSwap) i) ↔ (i = j) :=
    ⟨fun h => (P.outerSwap.injective h).symm, fun h => by rw [h]⟩
  simp only [hij, nil, of_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem map_perfectCore_eq_of_apply_elt [Finite K] (τ : MulAut (projectiveSL n K))
    (hτ : τ (P.elt K) = P.elt K) :
    (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map τ.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
  have hC : (centralizer ({P.elt K} : Set (projectiveSL n K))).map τ.toMonoidHom =
      centralizer ({P.elt K} : Set (projectiveSL n K)) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg τ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, hτ] at this
    · intro h
      apply τ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hτ]
      exact h
  rw [map_perfectCore, hC]

omit [CharP K 2] in
theorem leviOneHom_mem_scalars_iff (hJ : P.free = ∅) (a : SpecialLinearGroup (Fin k) K) :
    P.leviOneHom K a ∈ scalars n K ↔ a ∈ scalars k K := by
  have h2k : 2 * k ≤ n := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  have hn : n = 2 * k := by have := P.card_free; rw [hJ] at this; simp at this; omega
  have hout : ∀ i : Fin n, i ∈ P.outer := fun i => P.mem_outer_of_not_mem_free (by simp [hJ])
  constructor
  · rintro ⟨c, -, hc⟩
    have ha : (a : Matrix (Fin k) (Fin k) K) = scalar (Fin k) (c : K) := by
      rw [← P.submatrix_u_leviOneHom a, hc]
      ext x y
      simp [scalar_apply, diagonal_apply, P.u_injective.eq_iff]
    refine ⟨c, ?_, ha⟩
    have hdet := a.2
    rw [ha, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  · rintro ⟨c, hck, hc⟩
    refine ⟨c, by rw [hn, pow_mul', hck, one_pow], ?_⟩
    ext i j
    obtain ⟨s, rfl⟩ := P.mem_outer.1 (hout i)
    obtain ⟨t, rfl⟩ := P.mem_outer.1 (hout j)
    rw [leviOneHom_apply_supp, hc, scalar_apply, scalar_apply, diagonal_apply]
    simp only [P.supp_injective.eq_iff]
    rcases s with x | x <;> rcases t with y | y <;> simp [diagonal_apply]

variable (K) in
@[expose] noncomputable def toLeviOneP : SpecialLinearGroup (Fin k) K →* P.leviOneP K :=
  ((proj n K).comp (P.leviOneHom K)).codRestrict (P.leviOneP K) fun a =>
    ⟨P.leviOneHom K a, ⟨a, rfl⟩, rfl⟩

omit [CharP K 2] in
theorem toLeviOneP_surjective : Function.Surjective (P.toLeviOneP K) := by
  rintro ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩⟩
  exact ⟨a, rfl⟩

omit [CharP K 2] in
theorem ker_toLeviOneP (hJ : P.free = ∅) : (P.toLeviOneP K).ker = scalars k K := by
  ext a
  rw [MonoidHom.mem_ker, ← P.leviOneHom_mem_scalars_iff hJ, ← proj_eq_one_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

variable (K) in
@[expose] noncomputable def leviOnePEquivPSL (hJ : P.free = ∅) :
    projectiveSL k K ≃* P.leviOneP K :=
  (QuotientGroup.quotientMulEquivOfEq (P.ker_toLeviOneP (K := K) hJ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ P.toLeviOneP_surjective)

omit [CharP K 2] in
theorem coe_leviOnePEquivPSL (hJ : P.free = ∅) (a : SpecialLinearGroup (Fin k) K) :
    ((P.leviOnePEquivPSL K hJ (proj k K a) : P.leviOneP K) : projectiveSL n K) =
      proj n K (P.leviOneHom K a) :=
  rfl

end InvPlacement

section ProjFieldPart

variable {K : Type*} [Field K]

theorem projectiveSLTwoEquivSL_proj [CharP K 2] (g : SpecialLinearGroup (Fin 2) K) :
    LinearCover.projectiveSLTwoEquivSL K (proj 2 K g) = g :=
  rfl

theorem congr_projectiveSLTwoEquivSL_descendAut [CharP K 2]
    (θ : MulAut (SpecialLinearGroup (Fin 2) K)) :
    MulAut.congr (LinearCover.projectiveSLTwoEquivSL K) (descendAut 2 K θ) = θ := by
  refine MulEquiv.ext fun g => ?_
  show LinearCover.projectiveSLTwoEquivSL K
    (descendAut 2 K θ ((LinearCover.projectiveSLTwoEquivSL K).symm g)) = θ g
  have hg : (LinearCover.projectiveSLTwoEquivSL K).symm g = proj 2 K g := by
    rw [MulEquiv.symm_apply_eq, projectiveSLTwoEquivSL_proj]
  rw [hg, descendAut_proj, projectiveSLTwoEquivSL_proj]

theorem exists_projFieldPart [Finite K] [CharP K 2] {k : ℕ} (hk : 2 ≤ k) :
    ∃ F : MulAut (projectiveSL k K) →* (K ≃+* K),
      (∀ A : GL (Fin k) K, F (conjAut k K A) = 1) ∧
      (∀ σ : K ≃+* K, F (fieldAut k K σ) = σ) ∧ F (dualAut k K) = 1 := by
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · refine ⟨(sl2FieldPart K).comp
      (MulAut.congr (LinearCover.projectiveSLTwoEquivSL K)).toMonoidHom, fun A => ?_,
      fun σ => ?_, ?_⟩
    · change sl2FieldPart K (MulAut.congr (LinearCover.projectiveSLTwoEquivSL K)
        (descendAut 2 K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          2 K A))) = 1
      rw [congr_projectiveSLTwoEquivSL_descendAut, sl2FieldPart_slConjugation]
    · change sl2FieldPart K (MulAut.congr (LinearCover.projectiveSLTwoEquivSL K)
        (descendAut 2 K (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
          (Fin 2) K σ))) = σ
      rw [congr_projectiveSLTwoEquivSL_descendAut, sl2FieldPart_slFieldAut]
    · change sl2FieldPart K (MulAut.congr (LinearCover.projectiveSLTwoEquivSL K)
        (descendAut 2 K (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 2 K))) = 1
      rw [congr_projectiveSLTwoEquivSL_descendAut, sl2FieldPart_slGraphAut]
  · exact ⟨linearFieldPart K hk3, linearFieldPart_conjAut hk3, linearFieldPart_fieldAut hk3,
      linearFieldPart_dualAut hk3⟩

end ProjFieldPart

end CFSG.SeitzReduction.LinearPilot
