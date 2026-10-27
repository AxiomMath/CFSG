module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallSL2
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRestrictionField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.Quasithin (perfectCore map_perfectCore)

theorem subsingleton_specialLinearGroup_finset {n : ℕ} {K : Type*} [Field K]
    {I : Finset (Fin n)} (hI : I.card ≤ 1) : Subsingleton (SpecialLinearGroup I K) := by
  have := InvPlacement.subsingleton_specialLinearGroup_of_le_one (K := K) hI
  exact (reindexSpecialLinear (K := K) I.equivFin).toEquiv.subsingleton

theorem blockSpecialLinear_eq_bot_of_card_le_one {n : ℕ} {K : Type*} [Field K]
    {I : Finset (Fin n)} (hI : I.card ≤ 1) : blockSpecialLinear (K := K) I = ⊥ := by
  have := subsingleton_specialLinearGroup_finset (K := K) hI
  rw [← range_blockEmbed, eq_bot_iff]
  rintro _ ⟨A, rfl⟩
  rw [Subsingleton.elim A 1, map_one]
  exact one_mem _

theorem blockSL_eq_bot_of_card_le_one {n : ℕ} {K : Type*} [Field K] {I : Finset (Fin n)}
    (hI : I.card ≤ 1) : blockSL (K := K) I = ⊥ := by
  rw [blockSL, blockSpecialLinear_eq_bot_of_card_le_one hI, Subgroup.map_bot]

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

theorem radical_le_commutator_core_of_card_free_eq_one (hk : 2 ≤ k) (hJ : P.free.card = 1) :
    P.radical K ≤ ⁅P.core K, P.core K⁆ := by
  have hJne : P.free.Nonempty := Finset.card_pos.1 (by omega)
  have hRC : ⁅P.radical K, P.radical K⁆ ≤ ⁅P.core K, P.core K⁆ :=
    Subgroup.commutator_mono P.radical_le_core P.radical_le_core
  have hMR : ⁅P.leviOne K, P.radical K⁆ ≤ ⁅P.core K, P.core K⁆ :=
    Subgroup.commutator_mono P.leviOne_le_core P.radical_le_core
  refine P.radical_le_closure.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, j, hij, c, h, rfl⟩
  have hj2 := P.level_le_two j
  rcases (by omega : P.level i = 0 ∨ P.level i = 1) with hi | hi
  · obtain ⟨a, rfl⟩ := P.level_eq_zero_iff.1 hi
    rcases (by omega : P.level j = 1 ∨ P.level j = 2) with hj | hj
    · exact hMR (P.transvection_u_free_mem_commutator hk (P.mem_free.2 hj) a c)
    · obtain ⟨b, rfl⟩ := P.level_eq_two_iff.1 hj
      exact hRC (P.transvection_u_w_mem_commutator hJne a b c)
  · have hj' : P.level j = 2 := by omega
    obtain ⟨b, rfl⟩ := P.level_eq_two_iff.1 hj'
    exact hMR (P.transvection_free_w_mem_commutator hk (P.mem_free.2 hi) b c)

theorem commutator_core_of_card_free_eq_one [Group.IsPerfect (SpecialLinearGroup (Fin k) K)]
    (hk : 2 ≤ k) (hJ : P.free.card = 1) : ⁅P.core K, P.core K⁆ = P.core K := by
  refine le_antisymm (commutator_self_le' _) ?_
  refine sup_le (P.radical_le_commutator_core_of_card_free_eq_one hk hJ) (sup_le ?_ ?_)
  · have : Group.IsPerfect (P.leviOne K) := Group.IsPerfect.range _
    calc P.leviOne K = ⁅P.leviOne K, P.leviOne K⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅P.core K, P.core K⁆ := Subgroup.commutator_mono P.leviOne_le_core P.leviOne_le_core
  · rw [blockSpecialLinear_eq_bot_of_card_le_one (by omega)]
    exact bot_le

variable [CharP K 2]

theorem perfectCore_centralizer_elt_of_card_free_eq_one [Finite K] (hq : 4 ≤ Nat.card K)
    (hk : 2 ≤ k) (hJ : P.free.card = 1) :
    perfectCore (Subgroup.centralizer {P.elt K}) = P.radicalP K ⊔ P.leviOneP K := by
  have := isPerfect_specialLinearGroup_of_four_le hq (Fin k)
  have hmap : (P.core K).map (LinearFlag.proj n K) = P.radicalP K ⊔ P.leviOneP K := by
    rw [map_core_eq, blockSL_eq_bot_of_card_le_one (by omega), sup_bot_eq]
  rw [← hmap, P.centralizer_elt]
  refine perfectCore_eq_of_perfect_of_commutator_le (Subgroup.map_mono P.core_le_centralizer) ?_ ?_
  · rw [← Subgroup.map_commutator, P.commutator_core_of_card_free_eq_one hk hJ]
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono P.commutator_centralizer_le_core

theorem perfectCore_centralizer_elt_eq_map_core_of_card_free_eq_one [Finite K]
    (hq : 4 ≤ Nat.card K) (hk : 2 ≤ k) (hJ : P.free.card = 1) :
    perfectCore (Subgroup.centralizer {P.elt K}) = (P.core K).map (LinearFlag.proj n K) := by
  rw [P.perfectCore_centralizer_elt_of_card_free_eq_one hq hk hJ, map_core_eq,
    blockSL_eq_bot_of_card_le_one (by omega), sup_bot_eq]

theorem le_radicalP_of_isPGroup_of_card_free_eq_one [Finite K] (hq : 4 ≤ Nat.card K)
    (hk : 2 ≤ k) (hJ : P.free.card = 1) {T : Subgroup (projectiveSL n K)} (hT : IsPGroup 2 T)
    (hTΛ : T ≤ perfectCore (Subgroup.centralizer {P.elt K}))
    (hN : perfectCore (Subgroup.centralizer {P.elt K}) ≤
      Subgroup.normalizer (T : Set (projectiveSL n K))) :
    T ≤ P.radicalP K := by
  rw [P.perfectCore_centralizer_elt_eq_map_core_of_card_free_eq_one hq hk hJ] at hTΛ hN
  exact P.le_radicalP_of_isPGroup hq (Finset.card_pos.1 (by omega)) hT hTΛ hN

theorem radicalP_le_and_le_normalizer_of_card_free_eq_one [Finite K] (hq : 4 ≤ Nat.card K)
    (hk : 2 ≤ k) (hJ : P.free.card = 1) :
    P.radicalP K ≤ perfectCore (Subgroup.centralizer {P.elt K}) ∧
      perfectCore (Subgroup.centralizer {P.elt K}) ≤
        Subgroup.normalizer (P.radicalP K : Set (projectiveSL n K)) := by
  rw [P.perfectCore_centralizer_elt_of_card_free_eq_one hq hk hJ]
  refine ⟨le_sup_left, sup_le le_normalizer ?_⟩
  have h := P.levi_le_normalizer_radicalP (K := K)
  rw [blockSL_eq_bot_of_card_le_one (by omega), sup_bot_eq] at h
  exact h

theorem map_radicalP_eq_of_map_eq_of_card_free_eq_one [Finite K] (hq : 4 ≤ Nat.card K)
    (hk : 2 ≤ k) (hJ : P.free.card = 1) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K)))).map
      β.toMonoidHom = perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K)))) :
    (P.radicalP K).map β.toMonoidHom = P.radicalP K := by
  obtain ⟨hQΛ, hΛN⟩ := P.radicalP_le_and_le_normalizer_of_card_free_eq_one hq hk hJ
  have hle : (P.radicalP K).map β.toMonoidHom ≤ P.radicalP K := by
    refine P.le_radicalP_of_isPGroup_of_card_free_eq_one hq hk hJ
      (P.isPGroup_radicalP.map _) ?_ ?_
    · rw [← hβ]
      exact map_mono hQΛ
    · rw [← hβ]
      exact (map_mono hΛN).trans (le_normalizer_map _)
  exact eq_of_le_of_card_ge hle (card_map_of_injective β.injective).ge

end InvPlacement

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

theorem outerSwap_mem_outer_iff {i : Fin n} : (P.outerSwap) i ∈ P.outer ↔ i ∈ P.outer := by
  constructor
  · intro h
    by_contra hi
    exact P.not_mem_free_of_mem_outer h
      (P.outerSwap_mem_free_iff.2 (by_contra fun h' => hi (P.mem_outer_of_not_mem_free h')))
  · intro h
    by_contra hi
    exact P.not_mem_free_of_mem_outer h
      (P.outerSwap_mem_free_iff.1 (by_contra fun h' => hi (P.mem_outer_of_not_mem_free h')))

theorem map_leviOneHom (σ : K →+* K) (a : SpecialLinearGroup (Fin k) K) :
    SpecialLinearGroup.map σ (P.leviOneHom K a) =
      P.leviOneHom K (SpecialLinearGroup.map σ a) := by
  ext i j
  change σ ((P.leviOneHom K a : Matrix (Fin n) (Fin n) K) i j) =
    (P.leviOneHom K (SpecialLinearGroup.map σ a) : Matrix (Fin n) (Fin n) K) i j
  by_cases h : i ∈ P.outer ∧ j ∈ P.outer
  · obtain ⟨s, rfl⟩ := P.mem_outer.1 h.1
    obtain ⟨t, rfl⟩ := P.mem_outer.1 h.2
    rw [leviOneHom_apply_supp, leviOneHom_apply_supp]
    rcases s with x | x <;> rcases t with y | y <;> simp
  · rw [P.leviOneHom_apply_of_not_mem_outer _ (not_and_or.1 h),
      P.leviOneHom_apply_of_not_mem_outer _ (not_and_or.1 h)]
    by_cases hij : i = j
    · rw [hij, one_apply_eq, map_one]
    · rw [one_apply_ne hij, map_zero]

theorem twist_leviOneHom (σ : K →+* K) (b : SpecialLinearGroup (Fin k) K) :
    (((P.leviOneHom K b : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose.map
      σ).submatrix P.outerSwap P.outerSwap =
      ((P.leviOneHom K (SpecialLinearGroup.map σ b.transpose) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
  ext i j
  rw [submatrix_apply, map_apply, transpose_apply]
  by_cases h : i ∈ P.outer ∧ j ∈ P.outer
  · obtain ⟨s, rfl⟩ := P.mem_outer.1 h.1
    obtain ⟨t, rfl⟩ := P.mem_outer.1 h.2
    rw [outerSwap_supp, outerSwap_supp, leviOneHom_apply_supp, leviOneHom_apply_supp]
    rcases s with x | x <;> rcases t with y | y <;> simp [Matrix.SpecialLinearGroup.coe_transpose]
  · have h' : (P.outerSwap) j ∉ P.outer ∨ (P.outerSwap) i ∉ P.outer := by
      rcases not_and_or.1 h with h | h
      · exact Or.inr fun h' => h (P.outerSwap_mem_outer_iff.1 h')
      · exact Or.inl fun h' => h (P.outerSwap_mem_outer_iff.1 h')
    rw [P.leviOneHom_apply_of_not_mem_outer _ h',
      P.leviOneHom_apply_of_not_mem_outer _ (not_and_or.1 h)]
    by_cases hij : i = j
    · rw [hij, one_apply_eq, one_apply_eq, map_one]
    · rw [one_apply_ne (fun h => hij (P.outerSwap.injective h).symm), one_apply_ne hij, map_zero]

theorem fieldAut_proj_leviOneHom (σ : K ≃+* K) (a : SpecialLinearGroup (Fin k) K) :
    fieldAut n K σ (proj n K (P.leviOneHom K a)) =
      proj n K (P.leviOneHom K (SpecialLinearGroup.map σ.toRingHom a)) := by
  rw [fieldAut_proj, map_leviOneHom]

theorem graphTwist_proj_leviOneHom (σ : K ≃+* K) (a : SpecialLinearGroup (Fin k) K) :
    (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K)
        (proj n K (P.leviOneHom K a)) =
      proj n K (P.leviOneHom K (SpecialLinearGroup.map σ.toRingHom (a⁻¹).transpose)) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, outerSwapGL_mul_mul_inv, ← map_inv]
  exact P.twist_leviOneHom σ.toRingHom a⁻¹

theorem proj_comp_leviOneHom_injective (hJ : P.free.Nonempty) :
    Function.Injective ((proj n K).comp (P.leviOneHom K)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at ha
  obtain ⟨c, -, hc⟩ := ha
  obtain ⟨l, hl⟩ := hJ
  have h1 := congrFun (congrFun hc l) l
  rw [P.leviOneHom_apply_of_not_mem_outer _ (Or.inl fun h => P.not_mem_free_of_mem_outer h hl),
    one_apply_eq, scalar_apply, diagonal_apply_eq] at h1
  have hlevi : P.leviOneHom K a = 1 := by
    ext i j
    rw [hc, ← h1, scalar_apply, diagonal_one]
    rfl
  exact P.leviOneHom_injective (by rw [hlevi, map_one])

theorem leviOneP_eq_range : P.leviOneP K = ((proj n K).comp (P.leviOneHom K)).range := by
  rw [MonoidHom.range_comp]
  rfl

variable (K) in
@[expose] noncomputable def leviOnePEquiv (hJ : P.free.Nonempty) :
    SpecialLinearGroup (Fin k) K ≃* P.leviOneP K :=
  (MonoidHom.ofInjective (P.proj_comp_leviOneHom_injective (K := K) hJ)).trans
    (MulEquiv.subgroupCongr P.leviOneP_eq_range.symm)

theorem coe_leviOnePEquiv (hJ : P.free.Nonempty) (a : SpecialLinearGroup (Fin k) K) :
    ((P.leviOnePEquiv K hJ a : P.leviOneP K) : projectiveSL n K) = proj n K (P.leviOneHom K a) :=
  rfl

section RC

variable [Finite K] [CharP K 2]

theorem mulAutHom_congr_eq_of_twist_levi (hq : 4 ≤ Nat.card K) (hk : 2 ≤ k)
    (hJ : P.free.card = 1) (F : MulAut (SpecialLinearGroup (Fin k) K) →* (K ≃+* K))
    (hF : ∀ A : GL (Fin k) K, F (slConjugation k K A) = 1) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K)))).map
      β.toMonoidHom = perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (P.leviOneP K))
    (hβbar : ∀ s : P.leviOneP K,
      ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K)
    (κ : P.leviOneP K ≃* SpecialLinearGroup (Fin k) K)
    (B : GL (Fin n) K) (τ : MulAut (projectiveSL n K))
    (τk : MulAut (SpecialLinearGroup (Fin k) K))
    (hβτ : β = conjAut n K B * τ) (hτQ : ∀ x ∈ P.radicalP K, τ x ∈ P.radicalP K)
    (hτS : ∀ a : SpecialLinearGroup (Fin k) K,
      τ (proj n K (P.leviOneHom K a)) = proj n K (P.leviOneHom K (τk a))) :
    F (MulAut.congr κ βbar) = F τk := by
  have hJne : P.free.Nonempty := Finset.card_pos.1 (by omega)
  have hk0 : 0 < k := by omega
  have hβQ : (P.radicalP K).map β.toMonoidHom = P.radicalP K :=
    P.map_radicalP_eq_of_map_eq_of_card_free_eq_one hq hk hJ β hβ
  have hτQ' : (P.radicalP K).map τ.toMonoidHom = P.radicalP K := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective τ.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hτQ x hx
  have hβmem : ∀ x ∈ P.radicalP K, β x ∈ P.radicalP K := fun x hx => by
    rw [← hβQ]
    exact ⟨x, hx, rfl⟩
  have hβinv : ∀ x ∈ P.radicalP K, β⁻¹ x ∈ P.radicalP K := fun x hx => by
    rw [← hβQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hτinv : ∀ x ∈ P.radicalP K, τ⁻¹ x ∈ P.radicalP K := fun x hx => by
    rw [← hτQ'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hcB : conjAut n K B = β * τ⁻¹ := by rw [hβτ, mul_inv_cancel_right]
  have hB1 : ∀ x ∈ P.radicalP K, conjAut n K B x ∈ P.radicalP K := fun x hx => by
    rw [hcB, MulAut.mul_apply]
    exact hβmem _ (hτinv x hx)
  have hB2 : ∀ x ∈ P.radicalP K, conjAut n K B⁻¹ x ∈ P.radicalP K := fun x hx => by
    rw [map_inv, hcB, _root_.mul_inv_rev, inv_inv, MulAut.mul_apply]
    exact hτQ _ (hβinv x hx)
  have hBt := P.blockTriangular_of_conjAut hk0 B hB1 hB2
  have hBi : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular P.level := by
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hBt
  set Bu : Matrix (Fin k) (Fin k) K := (B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u with hBu
  set Bu' : Matrix (Fin k) (Fin k) K :=
    ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u with hBu'
  have hBB' : Bu * Bu' = 1 := by
    rw [hBu, hBu', ← P.submatrix_mul_u hBt hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      submatrix_one _ P.u_injective]
  have hB'B : Bu' * Bu = 1 := by
    rw [hBu, hBu', ← P.submatrix_mul_u hBi hBt, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      submatrix_one _ P.u_injective]
  set B'' : GL (Fin k) K := ⟨Bu, Bu', hBB', hB'B⟩ with hB''
  set γ₁ : MulAut (SpecialLinearGroup (Fin k) K) := slConjugation k K B'' * τk with hγ₁
  set κ₀ := P.leviOnePEquiv K hJne with hκ₀
  set ψ : MulAut (P.leviOneP K) := MulAut.congr κ₀ γ₁ with hψdef
  have hψx : ∀ a, ψ (κ₀ a) = κ₀ (γ₁ a) := fun a => by
    show κ₀ (γ₁ (κ₀.symm (κ₀ a))) = κ₀ (γ₁ a)
    rw [MulEquiv.symm_apply_apply]
  have hΛC : perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
      (Subgroup.centralizer {P.mat K}).map (proj n K) := by
    rw [← P.centralizer_elt]
    exact CFSG.Quasithin.perfectCore_le _
  have hψ : ∀ s : P.leviOneP K,
      ((ψ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K := by
    intro s
    obtain ⟨a, rfl⟩ := κ₀.surjective s
    rw [hψx, hκ₀, P.coe_leviOnePEquiv, P.coe_leviOnePEquiv]
    set L := P.leviOneHom K (τk a) with hL
    set X := slConjugation n K B L with hX
    have hβa : β (proj n K (P.leviOneHom K a)) = proj n K X := by
      rw [hβτ, MulAut.mul_apply, hτS, conjAut_proj]
    have hXΛ : proj n K X ∈ perfectCore (Subgroup.centralizer ({P.elt K} :
        Set (projectiveSL n K))) := by
      rw [← hβa, ← hβ]
      exact ⟨_, leviOneP_le_perfectCore hq P ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨x', hx'C, hx'X⟩ := hΛC hXΛ
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 hx'X)
    have hXx' : (X : Matrix (Fin n) (Fin n) K) = (x' : Matrix (Fin n) (Fin n) K) *
        scalar (Fin n) (c : K) := by
      rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have hx'uw := (P.mem_centralizer_mat_iff.1 hx'C).2
    have hXuw : ∀ x y, (X : Matrix (Fin n) (Fin n) K) (P.w x) (P.w y) =
        (X : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) := fun x y => by
      rw [hXx', scalar_apply, mul_diagonal, mul_diagonal, hx'uw]
    have hLt : (L : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
      P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag _)
    have hXmat : (X : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) *
        ((L : Matrix (Fin n) (Fin n) K) * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hX, coe_slConjugation, Matrix.mul_assoc]
    have hXt : X ∈ P.parabolic K := by
      change (X : Matrix (Fin n) (Fin n) K).BlockTriangular P.level
      rw [hXmat]
      exact hBt.mul (hLt.mul hBi)
    have hXu : (X : Matrix (Fin n) (Fin n) K).submatrix P.u P.u =
        Bu * (τk a : Matrix (Fin k) (Fin k) K) * Bu' := by
      rw [hXmat, P.submatrix_mul_u hBt (hLt.mul hBi), P.submatrix_mul_u hLt hBi,
        P.submatrix_u_leviOneHom, Matrix.mul_assoc]
    have hXJ : (X : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
        (Subtype.val : P.free → Fin n) = 1 := by
      rw [hXmat, P.submatrix_mul_free hBt (hLt.mul hBi), P.submatrix_mul_free hLt hBi,
        P.submatrix_free_leviOneHom, Matrix.one_mul, ← P.submatrix_mul_free hBt hBi,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, submatrix_one _ Subtype.val_injective]
    set N := P.leviOneHom K (slConjugation k K B'' (τk a)) with hN
    have hNt : N ∈ P.parabolic K := P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag _)
    have hNu : ∀ x y, (N : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) =
        (Bu * (τk a : Matrix (Fin k) (Fin k) K) * Bu') x y := fun x y => by
      rw [hN, leviOneHom_apply_u_u, coe_slConjugation]
      rfl
    have hNw : ∀ x y, (N : Matrix (Fin n) (Fin n) K) (P.w x) (P.w y) =
        (N : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) := fun x y => by
      rw [hN, leviOneHom_apply_w_w, leviOneHom_apply_u_u]
    have hmem : N⁻¹ * X ∈ P.radical K := by
      refine P.inv_mul_mem_radical_of_eq hXt hNt fun i j hij => ?_
      have hi2 := P.level_le_two i
      rcases (by omega : P.level i = 0 ∨ P.level i = 1 ∨ P.level i = 2) with h0 | h1 | h2
      · obtain ⟨x, rfl⟩ := P.level_eq_zero_iff.1 h0
        obtain ⟨y, rfl⟩ := P.level_eq_zero_iff.1 (hij.symm.trans h0)
        rw [hNu, ← hXu]
        rfl
      · have hiJ := P.mem_free.2 h1
        have hjJ := P.mem_free.2 (hij.symm.trans h1)
        have hX1 := congrFun (congrFun hXJ ⟨i, hiJ⟩) ⟨j, hjJ⟩
        rw [submatrix_apply] at hX1
        rw [hX1, hN, P.leviOneHom_apply_of_not_mem_outer _
          (Or.inl fun h => P.not_mem_free_of_mem_outer h hiJ)]
        by_cases hij' : i = j
        · subst hij'
          rw [one_apply_eq, one_apply_eq]
        · rw [one_apply_ne (fun h => hij' (congrArg Subtype.val h)), one_apply_ne hij']
      · obtain ⟨x, rfl⟩ := P.level_eq_two_iff.1 h2
        obtain ⟨y, rfl⟩ := P.level_eq_two_iff.1 (hij.symm.trans h2)
        rw [hXuw, hNw, hNu, ← hXu]
        rfl
    rw [hβa, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  have hdisj : Disjoint (P.radicalP K) (P.leviOneP K) :=
    P.disjoint_radicalP.mono_right le_sup_left
  have hβbarψ : βbar = ψ := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    have hmem : ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ *
        ((ψ s : P.leviOneP K) : projectiveSL n K) ∈ P.radicalP K := by
      have h : ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ *
          ((ψ s : P.leviOneP K) : projectiveSL n K) =
          (((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s) *
            (((ψ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s)⁻¹ := by group
      rw [h]
      exact mul_mem (hβbar s) (inv_mem (hψ s))
    have hmemS : ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ *
        ((ψ s : P.leviOneP K) : projectiveSL n K) ∈ P.leviOneP K :=
      mul_mem (inv_mem (βbar s).2) (ψ s).2
    exact inv_mul_eq_one.1 (Subgroup.disjoint_def.1 hdisj hmem hmemS)
  rw [hβbarψ, ← mulAutHom_congr_eq_of_intertwine F (fun a b => ringEquiv_mul_comm _ _)
    (MulEquiv.refl _) κ κ₀ γ₁ ψ hψx]
  have hrefl : MulAut.congr (MulEquiv.refl (SpecialLinearGroup (Fin k) K)) γ₁ = γ₁ := by
    ext x
    rfl
  rw [hrefl, hγ₁, map_mul, hF, one_mul]

end RC

end InvPlacement

end CFSG.SeitzReduction.LinearPilot

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.Quasithin (perfectCore map_perfectCore)

theorem exists_mulAutHom_fieldPart {k : ℕ} {K : Type*} [Field K] [Finite K] (hk : 2 ≤ k) :
    ∃ F : MulAut (SpecialLinearGroup (Fin k) K) →* (K ≃+* K),
      (∀ A : GL (Fin k) K, F (slConjugation k K A) = 1) ∧
      (∀ σ : K ≃+* K, F (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin k) K σ) = σ) ∧
      F (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut k K) = 1 := by
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · exact ⟨sl2FieldPart K, sl2FieldPart_slConjugation K, sl2FieldPart_slFieldAut K,
      sl2FieldPart_slGraphAut K⟩
  · exact ⟨slFieldPart hk3, slFieldPart_slConjugation hk3, slFieldPart_slFieldAut hk3,
      slFieldPart_slGraphAut hk3⟩

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem mulAutHom_congr_eq_linearFieldPart_levi (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    (hk : 2 ≤ k) (hJ : P.free.card = 1) (F : MulAut (SpecialLinearGroup (Fin k) K) →* (K ≃+* K))
    (hF : ∀ A : GL (Fin k) K, F (slConjugation k K A) = 1)
    (hFσ : ∀ σ : K ≃+* K, F (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
      (Fin k) K σ) = σ)
    (hFδ : F (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut k K) = 1)
    (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K)))).map
      β.toMonoidHom = perfectCore (Subgroup.centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (P.leviOneP K))
    (hβbar : ∀ s : P.leviOneP K,
      ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K)
    (κ : P.leviOneP K ≃* SpecialLinearGroup (Fin k) K) :
    F (MulAut.congr κ βbar) = linearFieldPart K hn β := by
  obtain ⟨σ, A, e, he, hβeq⟩ := ProjectivePlane.exists_standard_form K n hn β
  rw [hβeq, linearFieldPart_eq hn he]
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · rw [P.mulAutHom_congr_eq_of_twist_levi hq hk hJ F hF β hβ βbar hβbar κ A (fieldAut n K σ)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin k) K σ)
      (by rw [hβeq, pow_zero, mul_one]) (fun x hx => P.fieldAut_mem_radicalP σ hx)
      (fun a => by rw [P.fieldAut_proj_leviOneHom]; rfl), hFσ]
  · rw [P.mulAutHom_congr_eq_of_twist_levi hq hk hJ F hF β hβ βbar hβbar κ
      (A * (P.outerSwapGL K)⁻¹) (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin k) K σ *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut k K)
      (by rw [hβeq, pow_one, map_mul, map_inv]; group)
      (fun x hx => P.graphTwist_mem_radicalP σ hx)
      (fun a => by rw [P.graphTwist_proj_leviOneHom]; rfl), map_mul, hFσ, hFδ, mul_one]

end InvPlacement

section Coordinates

variable {G : Type*} [Group G] [Finite G] {n k k' : ℕ} {K : Type*} [Field K] [Finite K]
  [CharP K 2] {φ φ' : projectiveSL n K →* G}

omit [Finite G] in
theorem map_radicalP_eq_of_card_free_eq_one (hq : 4 ≤ Nat.card K) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P : InvPlacement n k) (P' : InvPlacement n k')
    (hk : 2 ≤ k) (hk' : 2 ≤ k') (hJ : P.free.card = 1) (hJ' : P'.free.card = 1)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    (P'.radicalP K).map φ' = (P.radicalP K).map φ := by
  obtain ⟨hQΛ, hΛN⟩ := P.radicalP_le_and_le_normalizer_of_card_free_eq_one hq hk hJ
  obtain ⟨hQ'Λ, hΛN'⟩ := P'.radicalP_le_and_le_normalizer_of_card_free_eq_one hq hk' hJ'
  have heq : P'.radicalP K = ((P.radicalP K).map φ).comap φ' := by
    apply le_antisymm
    · exact le_comap_map_of_forall hφ hΛ
        (fun T hT h1 h2 => P.le_radicalP_of_isPGroup_of_card_free_eq_one hq hk hJ hT h1 h2)
        P'.isPGroup_radicalP hQ'Λ hΛN'
    · exact P'.le_radicalP_of_isPGroup_of_card_free_eq_one hq hk' hJ'
        (isPGroup_comap_map hφ' P.isPGroup_radicalP) (comap_map_le hφ' hΛ hQΛ)
        (le_normalizer_comap_map hΛ hΛN)
  rw [heq, map_comap_map_eq hΛ hQΛ]

end Coordinates

end CFSG.SeitzReduction.LinearPilot
