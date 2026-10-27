module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.Assembly.LowTwoRank

namespace OrthogonalTwoPart

variable {K : Type} [Field K] {m : ℕ}

section Block

variable (ρ : Type) [DecidableEq ρ]

@[expose] def hyperbolicBlock (A : GL (Fin m) K) :
    Matrix ((Fin m ⊕ Fin m) ⊕ ρ) ((Fin m ⊕ Fin m) ⊕ ρ) K :=
  fromBlocks (fromBlocks (A : Matrix (Fin m) (Fin m) K) 0 0
    ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ) 0 0 1

theorem hyperbolicBlock_one : hyperbolicBlock ρ (1 : GL (Fin m) K) = 1 := by
  simp [hyperbolicBlock, fromBlocks_one]

variable [Fintype ρ]

theorem hyperbolicBlock_mul (A B : GL (Fin m) K) :
    hyperbolicBlock ρ (A * B) = hyperbolicBlock ρ A * hyperbolicBlock ρ B := by
  simp [hyperbolicBlock, fromBlocks_multiply, _root_.mul_inv_rev, transpose_mul]

theorem hyperbolicBlock_mulVec_xx (A : GL (Fin m) K) (w : (Fin m ⊕ Fin m) ⊕ ρ → K) (i : Fin m) :
    (hyperbolicBlock ρ A *ᵥ w) (.inl (.inl i)) =
      ((A : Matrix (Fin m) (Fin m) K) *ᵥ fun j => w (.inl (.inl j))) i := by
  simp [hyperbolicBlock, fromBlocks_mulVec, Function.comp_def]

theorem hyperbolicBlock_mulVec_yy (A : GL (Fin m) K) (w : (Fin m ⊕ Fin m) ⊕ ρ → K) (i : Fin m) :
    (hyperbolicBlock ρ A *ᵥ w) (.inl (.inr i)) =
      (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ fun j => w (.inl (.inr j))) i := by
  simp [hyperbolicBlock, fromBlocks_mulVec, Function.comp_def]

theorem hyperbolicBlock_mulVec_rest (A : GL (Fin m) K) (w : (Fin m ⊕ Fin m) ⊕ ρ → K) (r : ρ) :
    (hyperbolicBlock ρ A *ᵥ w) (.inr r) = w (.inr r) := by
  simp [hyperbolicBlock, fromBlocks_mulVec, Function.comp_def]

end Block

variable {ρ ι : Type} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def hyperbolicHom (e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι) :
    GL (Fin m) K →* GL ι K :=
  MonoidHom.toHomUnits
    { toFun := fun A => (hyperbolicBlock ρ A).submatrix e.symm e.symm
      map_one' := by rw [hyperbolicBlock_one, submatrix_one_equiv]
      map_mul' := fun A B => by rw [hyperbolicBlock_mul, submatrix_mul_equiv] }

theorem coe_hyperbolicHom (e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι) (A : GL (Fin m) K) :
    (hyperbolicHom e A : Matrix ι ι K) = (hyperbolicBlock ρ A).submatrix e.symm e.symm :=
  rfl

theorem hyperbolicHom_mulVec_apply (e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι) (A : GL (Fin m) K)
    (v : ι → K) (x : (Fin m ⊕ Fin m) ⊕ ρ) :
    ((hyperbolicHom e A : Matrix ι ι K) *ᵥ v) (e x) = (hyperbolicBlock ρ A *ᵥ (v ∘ e)) x := by
  rw [coe_hyperbolicHom, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_apply,
    Equiv.symm_apply_apply]

@[expose] def IsHyperbolicSplit (e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι) (Q : (ι → K) → K)
    (R : (ρ → K) → K) : Prop :=
  ∀ v, Q v = ∑ i, v (e (.inl (.inl i))) * v (e (.inl (.inr i))) + R (fun r => v (e (.inr r)))

theorem isometry_hyperbolicHom {e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι} {Q : (ι → K) → K}
    {R : (ρ → K) → K} (hQ : IsHyperbolicSplit e Q R) (A : GL (Fin m) K) (v : ι → K) :
    Q ((hyperbolicHom e A : Matrix ι ι K) *ᵥ v) = Q v := by
  rw [hQ, hQ]
  simp only [hyperbolicHom_mulVec_apply, hyperbolicBlock_mulVec_xx, hyperbolicBlock_mulVec_yy,
    hyperbolicBlock_mulVec_rest, Function.comp_apply]
  congr 1
  change ((A : Matrix (Fin m) (Fin m) K) *ᵥ _) ⬝ᵥ
      (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ _) = _ ⬝ᵥ _
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, A.inv_mul, one_mulVec]

theorem range_le_statedOmega (hm : 3 ≤ m) {e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι} {Q : (ι → K) → K}
    {R : (ρ → K) → K} (hQ : IsHyperbolicSplit e Q R) :
    ((hyperbolicHom e).comp (SpecialLinearGroup.toGL (n := Fin m) (R := K))).range ≤
      StatedOmega Q := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) hm
  set φ := (hyperbolicHom e).comp (SpecialLinearGroup.toGL (n := Fin m) (R := K))
  have hP : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hle : φ.range ≤
      Subgroup.closure {B : GL ι K | ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v} := by
    rintro _ ⟨A, rfl⟩
    exact Subgroup.subset_closure (isometry_hyperbolicHom hQ _)
  calc φ.range = ⁅φ.range, φ.range⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ StatedOmega Q := Subgroup.commutator_mono hle hle

theorem exists_scalar_of_hyperbolicHom_mem (hm : 1 ≤ m) {e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι}
    {A : GL (Fin m) K} (h : hyperbolicHom e A ∈ StatedScalars ι K) :
    ∃ u : K, u * u = 1 ∧ (A : Matrix (Fin m) (Fin m) K) = scalar (Fin m) u := by
  obtain ⟨u, hu⟩ := h
  have hM := congrArg (fun B : GL ι K => (B : Matrix ι ι K)) hu
  simp only [GeneralLinearGroup.coe_scalar, coe_hyperbolicHom] at hM
  have hentry : ∀ x y, hyperbolicBlock ρ A x y = scalar ι (u : K) (e x) (e y) := by
    intro x y
    rw [hM, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hA : (A : Matrix (Fin m) (Fin m) K) = scalar (Fin m) (u : K) := by
    ext i j
    have := hentry (.inl (.inl i)) (.inl (.inl j))
    simp only [hyperbolicBlock, fromBlocks_apply₁₁, scalar_apply, diagonal_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at this
    simp [this, scalar_apply, diagonal_apply]
  have hAinv : ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = scalar (Fin m) (u : K) := by
    ext i j
    have := hentry (.inl (.inr j)) (.inl (.inr i))
    simp only [hyperbolicBlock, fromBlocks_apply₁₁, fromBlocks_apply₂₂, transpose_apply,
      scalar_apply, diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
      Sum.inr.injEq] at this
    simp only [this, scalar_apply, diagonal_apply, eq_comm]
  refine ⟨u, ?_, hA⟩
  have h1 := A.mul_inv
  rw [hA, hAinv, ← map_mul] at h1
  have h00 := congrFun (congrFun h1 ⟨0, hm⟩) ⟨0, hm⟩
  simpa [scalar_apply] using h00

theorem exists_hom_statedProj (hm : 3 ≤ m) {e : (Fin m ⊕ Fin m) ⊕ ρ ≃ ι} {Q : (ι → K) → K}
    {R : (ρ → K) → K} (hQ : IsHyperbolicSplit e Q R) :
    ∃ ψ : SpecialLinearGroup (Fin m) K →* StatedProj (StatedOmega Q), ∀ A, ψ A = 1 →
      ∃ u : K, u * u = 1 ∧ (A : Matrix (Fin m) (Fin m) K) = scalar (Fin m) u := by
  set φ := (hyperbolicHom e).comp (SpecialLinearGroup.toGL (n := Fin m) (R := K))
  have hφ : ∀ A, φ A ∈ StatedOmega Q := fun A => range_le_statedOmega hm hQ ⟨A, rfl⟩
  refine ⟨(QuotientGroup.mk' _).comp (φ.codRestrict _ hφ), fun A hA => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply] at hA
  exact exists_scalar_of_hyperbolicHom_mem (by omega) hA

theorem injective_of_three {G : Type*} [Group G] (ψ : SpecialLinearGroup (Fin 3) K →* G)
    (hψ : ∀ A, ψ A = 1 →
      ∃ u : K, u * u = 1 ∧ (A : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) u) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨u, hu, hAu⟩ := hψ A hA
  have hdet : u ^ 3 = 1 := by
    have h := A.det_coe
    rw [hAu, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hu1 : u = 1 := by
    calc u = u * (u * u) := by rw [hu, mul_one]
      _ = u ^ 3 := by ring
      _ = 1 := hdet
  ext i j
  rw [hAu, hu1, map_one]
  rfl

theorem card_dvd_two_mul_of_four [Finite K] {G : Type*} [Group G]
    (ψ : SpecialLinearGroup (Fin 4) K →* G)
    (hψ : ∀ A, ψ A = 1 →
      ∃ u : K, u * u = 1 ∧ (A : Matrix (Fin 4) (Fin 4) K) = scalar (Fin 4) u) :
    Nat.card (SpecialLinearGroup (Fin 4) K) ∣ 2 * Nat.card G := by
  classical
  have hker : Nat.card ψ.ker ≤ 2 := by
    refine (Nat.card_le_card_of_injective (fun A : ψ.ker =>
      decide (((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = 1))
      fun A B hAB => ?_).trans (by simp)
    obtain ⟨u, hu, hAu⟩ := hψ A (MonoidHom.mem_ker.mp A.2)
    obtain ⟨w, hw, hBw⟩ := hψ B (MonoidHom.mem_ker.mp B.2)
    have hA0 : ((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = u := by
      rw [hAu, scalar_apply, diagonal_apply_eq]
    have hB0 : ((B : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = w := by
      rw [hBw, scalar_apply, diagonal_apply_eq]
    have hiff : u = 1 ↔ w = 1 := by
      have := decide_eq_decide.mp hAB
      rwa [hA0, hB0] at this
    have huw : u = w := by
      rcases mul_self_eq_one_iff.mp hu with rfl | rfl <;>
        rcases mul_self_eq_one_iff.mp hw with h | h
      · exact h.symm
      · exact (hiff.mp rfl).symm
      · exact (hiff.mpr h).trans h.symm
      · exact h.symm
    exact Subtype.ext (Subtype.ext (hAu.trans (huw ▸ hBw.symm)))
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hdvd : Nat.card ψ.ker ∣ 2 := by
    interval_cases h : Nat.card ψ.ker <;> norm_num
  rw [← Subgroup.card_ker_mul_card_range ψ]
  exact Nat.mul_dvd_mul hdvd (Subgroup.card_subgroup_dvd_card _)

@[expose] def plusEquiv (m k : ℕ) :
    (Fin m ⊕ Fin m) ⊕ (Fin k ⊕ Fin k) ≃ Fin (m + k) ⊕ Fin (m + k) :=
  (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

@[simp] theorem plusEquiv_inl_inl (k : ℕ) (i : Fin m) :
    plusEquiv m k (.inl (.inl i)) = .inl (Fin.castAdd k i) := rfl

@[simp] theorem plusEquiv_inl_inr (k : ℕ) (i : Fin m) :
    plusEquiv m k (.inl (.inr i)) = .inr (Fin.castAdd k i) := rfl

@[simp] theorem plusEquiv_inr_inl (k : ℕ) (j : Fin k) :
    plusEquiv m k (.inr (.inl j)) = .inl (Fin.natAdd m j) := rfl

@[simp] theorem plusEquiv_inr_inr (k : ℕ) (j : Fin k) :
    plusEquiv m k (.inr (.inr j)) = .inr (Fin.natAdd m j) := rfl

theorem isHyperbolicSplit_plus (m k : ℕ) :
    IsHyperbolicSplit (plusEquiv m k) (StatedQuadPlus (m + k) K) (StatedQuadPlus k K) := by
  intro v
  simp only [StatedQuadPlus, plusEquiv_inl_inl, plusEquiv_inl_inr, plusEquiv_inr_inl,
    plusEquiv_inr_inr, Fin.sum_univ_add]

@[expose] def triEquiv (m k : ℕ) (γ : Type) :
    (Fin m ⊕ Fin m) ⊕ ((Fin k ⊕ Fin k) ⊕ γ) ≃ Fin (m + k) ⊕ Fin (m + k) ⊕ γ :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr (plusEquiv m k) (Equiv.refl γ)).trans (Equiv.sumAssoc _ _ _))

@[simp] theorem triEquiv_inl_inl (k : ℕ) (γ : Type) (i : Fin m) :
    triEquiv m k γ (.inl (.inl i)) = .inl (Fin.castAdd k i) := rfl

@[simp] theorem triEquiv_inl_inr (k : ℕ) (γ : Type) (i : Fin m) :
    triEquiv m k γ (.inl (.inr i)) = .inr (.inl (Fin.castAdd k i)) := rfl

@[simp] theorem triEquiv_inr_inl_inl (k : ℕ) (γ : Type) (j : Fin k) :
    triEquiv m k γ (.inr (.inl (.inl j))) = .inl (Fin.natAdd m j) := rfl

@[simp] theorem triEquiv_inr_inl_inr (k : ℕ) (γ : Type) (j : Fin k) :
    triEquiv m k γ (.inr (.inl (.inr j))) = .inr (.inl (Fin.natAdd m j)) := rfl

@[simp] theorem triEquiv_inr_inr (k : ℕ) (γ : Type) (g : γ) :
    triEquiv m k γ (.inr (.inr g)) = .inr (.inr g) := rfl

@[expose] def triQuad (N : ℕ) {γ : Type} (S : (γ → K) → K) (v : Fin N ⊕ Fin N ⊕ γ → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + S (fun g => v (.inr (.inr g)))

theorem isHyperbolicSplit_tri (m k : ℕ) {γ : Type} (S : (γ → K) → K) :
    IsHyperbolicSplit (triEquiv m k γ) (triQuad (m + k) S)
      (fun w => StatedQuadPlus k K (fun z => w (.inl z)) + S (fun g => w (.inr g))) := by
  intro v
  simp only [triQuad, StatedQuadPlus, triEquiv_inl_inl, triEquiv_inl_inr, triEquiv_inr_inl_inl,
    triEquiv_inr_inl_inr, triEquiv_inr_inr, Fin.sum_univ_add]
  ring

theorem statedQuadOdd_eq (n : ℕ) :
    StatedQuadOdd n K = triQuad n (fun w : Unit → K => w () ^ 2) :=
  rfl

theorem statedQuadMinus_eq (n : ℕ) (b c : K) :
    StatedQuadMinus n K b c =
      triQuad (n - 1) (fun w : Fin 2 → K => w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2) := by
  funext v
  simp only [StatedQuadMinus, triQuad]
  ring

theorem card_SL_three_dvd_tri {N : ℕ} (hN : 3 ≤ N) {γ : Type} [Fintype γ] [DecidableEq γ]
    (S : (γ → K) → K) :
    Nat.card (SpecialLinearGroup (Fin 3) K) ∣
      Nat.card (StatedProj (StatedOmega (triQuad N S))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨ψ, hψ⟩ := exists_hom_statedProj le_rfl (isHyperbolicSplit_tri 3 k (K := K) S)
  exact Subgroup.card_dvd_of_injective ψ (injective_of_three ψ hψ)

theorem card_SL_three_dvd_plus {N : ℕ} (hN : 3 ≤ N) :
    Nat.card (SpecialLinearGroup (Fin 3) K) ∣
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus N K))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨ψ, hψ⟩ := exists_hom_statedProj le_rfl (isHyperbolicSplit_plus 3 k (K := K))
  exact Subgroup.card_dvd_of_injective ψ (injective_of_three ψ hψ)

theorem card_SL_four_dvd_plus [Finite K] {N : ℕ} (hN : 4 ≤ N) :
    Nat.card (SpecialLinearGroup (Fin 4) K) ∣
      2 * Nat.card (StatedProj (StatedOmega (StatedQuadPlus N K))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨ψ, hψ⟩ := exists_hom_statedProj (by norm_num) (isHyperbolicSplit_plus 4 k (K := K))
  exact card_dvd_two_mul_of_four ψ hψ

theorem ordProj_two_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    ordProj[2] a ≤ ordProj[2] b :=
  Nat.le_of_dvd (Nat.ordProj_pos _ _) (Nat.ordProj_dvd_ordProj_of_dvd hb h 2)

theorem two_le_ordProj_two {a : ℕ} (ha : a ≠ 0) (h : 2 ∣ a) : 2 ≤ ordProj[2] a := by
  have := ordProj_two_le_of_dvd ha h
  rwa [Nat.prime_two.factorization_self, pow_one] at this

theorem card_SL_three [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  rw [LinearFlag.card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair (by norm_num)]

theorem card_SL_four [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 4) K) =
      Nat.card K ^ 6 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1)) := by
  rw [LinearFlag.card_SL_eq (by norm_num), show Finset.Icc 2 4 = {2, 3, 4} by decide,
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num), mul_assoc]

theorem three_le_and_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    3 ≤ p ^ f ∧ Odd (p ^ f) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine ⟨le_trans hp3 ?_, (hp.odd_of_ne_two hp2).pow⟩
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem two_adic_bounds_three {p f N : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hN : N ≠ 0)
    (h : (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ∣ N) :
    (p = 2 → (p ^ f) ^ 3 ≤ ordProj[2] N) ∧ (p ≠ 2 → 16 * ordProj[2] f ≤ ordProj[2] N) := by
  refine ⟨fun hp2 => ?_, fun hp2 => ?_⟩
  · subst hp2
    have h1 : 2 ^ (f * 3) ∣ N := by
      rw [pow_mul]
      exact (Dvd.intro _ rfl).trans h
    calc (2 ^ f) ^ 3 = 2 ^ (f * 3) := (pow_mul 2 f 3).symm
      _ ≤ ordProj[2] N := Nat.pow_le_pow_right (by norm_num)
          ((Nat.prime_two.pow_dvd_iff_le_factorization hN).mp h1)
  · obtain ⟨hq3, hodd⟩ := three_le_and_odd hp hp2 hf
    set q := p ^ f with hq
    have h2ne : q ^ 2 - 1 ≠ 0 := by
      have : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
      omega
    have h3ne : q ^ 3 - 1 ≠ 0 := by
      have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
      omega
    have h3 : 2 ≤ ordProj[2] (q ^ 3 - 1) :=
      two_le_ordProj_two h3ne (Nat.Odd.sub_odd hodd.pow odd_one).two_dvd
    have h1 : (q ^ 2 - 1) * (q ^ 3 - 1) ∣ N := (Dvd.intro_left _ rfl).trans h
    calc 16 * ordProj[2] f = 8 * ordProj[2] f * 2 := by ring
      _ ≤ ordProj[2] (q ^ 2 - 1) * ordProj[2] (q ^ 3 - 1) :=
          Nat.mul_le_mul (eight_mul_ordProj_two_le hp hp2 hf) h3
      _ = ordProj[2] ((q ^ 2 - 1) * (q ^ 3 - 1)) := (Nat.ordProj_mul 2 h2ne h3ne).symm
      _ ≤ ordProj[2] N := ordProj_two_le_of_dvd hN h1

theorem two_adic_bound_four {p f N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hN : N ≠ 0)
    (h : (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) ∣ 2 * N) :
    128 * (ordProj[2] f) ^ 2 ≤ ordProj[2] N := by
  obtain ⟨hq3, hodd⟩ := three_le_and_odd hp hp2 hf
  have hB := eight_mul_ordProj_two_le hp hp2 hf
  set q := p ^ f with hq
  have h2le : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
  have h2ne : q ^ 2 - 1 ≠ 0 := by omega
  have h3ne : q ^ 3 - 1 ≠ 0 := by
    have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
    omega
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    zify [(by omega : 1 ≤ q ^ 2), (by omega : 1 ≤ q ^ 4)]
    ring
  have h4ne : q ^ 4 - 1 ≠ 0 := by
    rw [h4]
    exact mul_ne_zero h2ne (by omega)
  have h3 : 2 ≤ ordProj[2] (q ^ 3 - 1) :=
    two_le_ordProj_two h3ne (Nat.Odd.sub_odd hodd.pow odd_one).two_dvd
  have hplus : 2 ≤ ordProj[2] (q ^ 2 + 1) :=
    two_le_ordProj_two (by omega) hodd.pow.add_one.two_dvd
  have hq4 : 2 * ordProj[2] (q ^ 2 - 1) ≤ ordProj[2] (q ^ 4 - 1) := by
    rw [h4, Nat.ordProj_mul 2 h2ne (by omega), mul_comm 2]
    exact Nat.mul_le_mul_left _ hplus
  have h1 : (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) ∣ 2 * N := (Dvd.intro_left _ rfl).trans h
  have hle := ordProj_two_le_of_dvd (by omega) h1
  rw [Nat.ordProj_mul 2 (mul_ne_zero h2ne h3ne) h4ne, Nat.ordProj_mul 2 h2ne h3ne,
    Nat.ordProj_mul 2 two_ne_zero hN, Nat.prime_two.factorization_self, pow_one] at hle
  set B := ordProj[2] (q ^ 2 - 1)
  have hB2 : 4 * B ^ 2 ≤ B * ordProj[2] (q ^ 3 - 1) * ordProj[2] (q ^ 4 - 1) := by
    calc 4 * B ^ 2 = B * 2 * (2 * B) := by ring
      _ ≤ B * ordProj[2] (q ^ 3 - 1) * ordProj[2] (q ^ 4 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) hq4
  have hF : 64 * (ordProj[2] f) ^ 2 ≤ B ^ 2 := by
    calc 64 * (ordProj[2] f) ^ 2 = (8 * ordProj[2] f) ^ 2 := by ring
      _ ≤ B ^ 2 := Nat.pow_le_pow_left hB 2
  omega

end OrthogonalTwoPart

open OrthogonalTwoPart

theorem orthogonal_model_linear_subgroup_two_part_lower_bound {T : Type} [Group T]
    {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hT : StatedClassicalModel T t n p f) :
    (p = 2 → (p ^ f) ^ 3 ≤ ordProj[2] (Nat.card T)) ∧
      (p ≠ 2 → 16 * ordProj[2] f ≤ ordProj[2] (Nat.card T)) ∧
      (p ≠ 2 → t = .POmegaPlus → 128 * (ordProj[2] f) ^ 2 ≤ ordProj[2] (Nat.card T)) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hT
    rw [Nat.card_congr φ.toEquiv]
    have hN : Nat.card (StatedProj (StatedOmega (StatedQuadOdd n K))) ≠ 0 := Nat.card_pos.ne'
    have h := card_SL_three_dvd_tri hn (fun w : Unit → K => w () ^ 2)
    rw [← statedQuadOdd_eq, card_SL_three, hK] at h
    exact ⟨(two_adic_bounds_three hp hf hN h).1, (two_adic_bounds_three hp hf hN h).2,
      fun _ h => nomatch h⟩
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨φ⟩⟩ := hT
    rw [Nat.card_congr φ.toEquiv]
    have hN : Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K))) ≠ 0 := Nat.card_pos.ne'
    have h3 := card_SL_three_dvd_plus (K := K) (by omega : 3 ≤ n)
    rw [card_SL_three, hK] at h3
    have h4 := card_SL_four_dvd_plus (K := K) hn
    rw [card_SL_four, hK] at h4
    exact ⟨(two_adic_bounds_three hp hf hN h3).1, (two_adic_bounds_three hp hf hN h3).2,
      fun hp2 _ => two_adic_bound_four hp hp2 hf hN h4⟩
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, -, ⟨φ⟩⟩ := hT
    rw [Nat.card_congr φ.toEquiv]
    have hN : Nat.card (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≠ 0 :=
      Nat.card_pos.ne'
    have h := card_SL_three_dvd_tri (by omega : 3 ≤ n - 1)
      (fun w : Fin 2 → K => w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2)
    rw [← statedQuadMinus_eq, card_SL_three, hK] at h
    exact ⟨(two_adic_bounds_three hp hf hN h).1, (two_adic_bounds_three hp hf hN h).2,
      fun _ h => nomatch h⟩

end CFSG.LocalAnalysis.ComponentInitial
