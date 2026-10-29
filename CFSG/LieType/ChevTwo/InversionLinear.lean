module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.LieType.ChevTwo

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace Inversion

variable {K : Type} [Field K]

@[expose] noncomputable def blockEmb (k : ℕ) :
    Matrix (Fin 3) (Fin 3) K →* Matrix (Fin (3 + k)) (Fin (3 + k)) K where
  toFun A := Matrix.reindexAlgEquiv K K finSumFinEquiv (Matrix.fromBlocks A 0 0 1)
  map_one' := by
    rw [Matrix.fromBlocks_one]
    exact map_one _
  map_mul' A B := by
    rw [← map_mul]
    congr 1
    simp [Matrix.fromBlocks_multiply]

theorem blockEmb_apply (k : ℕ) (A : Matrix (Fin 3) (Fin 3) K) :
    blockEmb k A = Matrix.reindexAlgEquiv K K finSumFinEquiv (Matrix.fromBlocks A 0 0 1) := rfl

theorem det_blockEmb (k : ℕ) (A : Matrix (Fin 3) (Fin 3) K) : (blockEmb k A).det = A.det := by
  rw [blockEmb_apply, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]

theorem transpose_blockEmb (k : ℕ) (A : Matrix (Fin 3) (Fin 3) K) :
    (blockEmb k A)ᵀ = blockEmb k Aᵀ := by
  simp only [blockEmb_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one]

theorem map_blockEmb (k : ℕ) (f : K →+* K) (A : Matrix (Fin 3) (Fin 3) K) :
    (blockEmb k A).map f = blockEmb k (A.map f) := by
  simp only [blockEmb_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  have h0 : ∀ {m n : Type} [Fintype m] [Fintype n], (0 : Matrix m n K).map f = 0 :=
    fun {m n} _ _ => Matrix.map_zero _ (map_zero f)
  have h1 : ∀ {n : Type} [Fintype n] [DecidableEq n], (1 : Matrix n n K).map f = 1 :=
    fun {n} _ _ => Matrix.map_one _ (map_zero f) (map_one f)
  rw [h0, h0, h1]

theorem blockEmb_apply_castAdd (k : ℕ) (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    blockEmb k A (Fin.castAdd k i) (Fin.castAdd k j) = A i j := by
  simp [blockEmb_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

@[expose] def x7 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 1, 1; 1, 1, 0]

theorem x7_pow : x7 ^ 7 = 1 := by decide
theorem x7_symm : x7ᵀ = x7 := by decide
theorem x7_det : x7.det = 1 := by decide

variable [CharP K 2]

@[expose] noncomputable def ι₂ (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

@[expose] noncomputable def m7 (K : Type) [Field K] [CharP K 2] : Matrix (Fin 3) (Fin 3) K :=
  (ι₂ K).mapMatrix x7

theorem m7_pow : m7 K ^ 7 = 1 := by
  rw [m7, ← map_pow, x7_pow, map_one]

theorem m7_det : (m7 K).det = 1 := by
  rw [m7, ← RingHom.map_det, x7_det, map_one]

theorem m7_symm : (m7 K)ᵀ = m7 K := by
  rw [m7, RingHom.mapMatrix_apply, ← Matrix.transpose_map, x7_symm]

theorem m7_map (σ : K ≃+* K) : (m7 K).map σ = m7 K := by
  have h : σ.toRingHom.comp (ι₂ K) = ι₂ K := RingHom.ext_zmod _ _
  rw [m7, RingHom.mapMatrix_apply, Matrix.map_map]
  exact congrArg (fun f : ZMod 2 →+* K => x7.map f) h

noncomputable def sl7 (k : ℕ) : SpecialLinearGroup (Fin (3 + k)) K :=
  ⟨blockEmb k (m7 K), by rw [det_blockEmb, m7_det]⟩

theorem sl7_pow (k : ℕ) : (sl7 k : SpecialLinearGroup (Fin (3 + k)) K) ^ 7 = 1 := by
  have h0 : (blockEmb k (m7 K)) ^ 7 = (1 : Matrix (Fin (3 + k)) (Fin (3 + k)) K) := by
    rw [← map_pow, m7_pow, map_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact h0

theorem sl7_symm (k : ℕ) :
    (↑(sl7 k : SpecialLinearGroup (Fin (3 + k)) K) : Matrix (Fin (3 + k)) (Fin (3 + k)) K)ᵀ =
    ↑(sl7 k : SpecialLinearGroup (Fin (3 + k)) K) := by
  change (blockEmb k (m7 K))ᵀ = blockEmb k (m7 K)
  rw [transpose_blockEmb, m7_symm]

theorem sl7_map (k : ℕ) (σ : K ≃+* K) :
    (↑(sl7 k : SpecialLinearGroup (Fin (3 + k)) K) :
      Matrix (Fin (3 + k)) (Fin (3 + k)) K).map σ =
    ↑(sl7 k : SpecialLinearGroup (Fin (3 + k)) K) := by
  change (blockEmb k (m7 K)).map σ = blockEmb k (m7 K)
  exact (map_blockEmb k (σ : K →+* K) (m7 K)).trans (congrArg (blockEmb k) (m7_map σ))

theorem sl7_not_scalar (k : ℕ) : sl7 k ∉ scalars (3 + k) K := by
  rintro ⟨c, -, hc⟩
  have := congrArg (fun M : Matrix (Fin (3 + k)) (Fin (3 + k)) K =>
    M (Fin.castAdd k 0) (Fin.castAdd k 2)) hc
  simp only [sl7] at this
  rw [blockEmb_apply_castAdd] at this
  simp [m7, x7, ι₂, Matrix.scalar_apply, Matrix.diagonal_apply] at this

section Main

variable [Finite K]

theorem not_two_dvd_gcd (n : ℕ) : ¬ 2 ∣ Nat.gcd n (Nat.card K - 1) := by
  intro h
  have h2 : 2 ∣ Nat.card K - 1 := h.trans (Nat.gcd_dvd_right _ _)
  have := Fintype.ofFinite K
  obtain ⟨f, hp, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have h2K : 2 ∣ Nat.card K := by rw [hK]; exact dvd_pow_self 2 (by omega)
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  omega

theorem card_eq_two_pow : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hp, hf⟩ := FiniteField.card K 2
  exact ⟨f, f.pos, by rw [← Nat.card_eq_fintype_card] at hf; exact hf⟩

theorem involution_unique {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {σ ρ : K ≃+* K}
    (hσ : σ ≠ 1) (hσσ : σ * σ = 1) (hρ : ρ ≠ 1) (hρρ : ρ * ρ = 1) : σ = ρ := by
  have h1 := (even_and_eq_pow_of_involution_prime Nat.prime_two hf hK hσ hσσ).2
  have h2 := (even_and_eq_pow_of_involution_prime Nat.prime_two hf hK hρ hρρ).2
  exact RingEquiv.ext fun x => (h1 x).trans (h2 x).symm

theorem fieldAut_dualAut_apply_symm {n : ℕ} (σ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K)
    (hT : g.1ᵀ = g.1) (hσ : g.1.map σ = g.1) :
    (fieldAut n K σ * dualAut n K) (proj n K g) = (proj n K g)⁻¹ := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj, ← map_inv]
  congr 1
  have h1 : (adjugate g.1)ᵀ = adjugate g.1 := by rw [Matrix.adjugate_transpose, hT]
  have h2 : σ.toRingHom.mapMatrix (adjugate g.1) = adjugate g.1 := by
    rw [RingHom.map_adjugate]
    congr 1
  apply Subtype.ext
  change σ.toRingHom.mapMatrix ((adjugate g.1)ᵀ) = adjugate g.1
  rw [h1, h2]

theorem exists_two_ne_one {G : Type*} [Group G] (A : Subgroup G) (hcard : Nat.card A = 4) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ b ∈ A, b ≠ 1 ∧ a ≠ b := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype A := Fintype.ofFinite A
  have h3 : 2 < Fintype.card A := by rw [Fintype.card_eq_nat_card]; omega
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp h3
  by_cases hx1 : (x : G) = 1
  · refine ⟨y, y.2, fun h => hxy ?_, z, z.2, fun h => hxz ?_, fun h => hyz (Subtype.ext h)⟩
    · exact Subtype.ext (hx1.trans h.symm)
    · exact Subtype.ext (hx1.trans h.symm)
  · by_cases hy1 : (y : G) = 1
    · exact ⟨x, x.2, hx1, z, z.2, fun h => hyz (Subtype.ext (hy1.trans h.symm)),
        fun h => hxz (Subtype.ext h)⟩
    · exact ⟨x, x.2, hx1, y, y.2, hy1, fun h => hxy (Subtype.ext h)⟩

end Main

end Inversion

open Inversion

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem linear_klein_inverts {N : ℕ} (hN : 3 ≤ N)
    (A : Subgroup (MulAut (LinearFlag.projectiveSL N K))) (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 4) (hAI : A ⊓ inner (LinearFlag.projectiveSL N K) = ⊥) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ x : LinearFlag.projectiveSL N K,
      Odd (orderOf x) ∧ 5 < orderOf x ∧ a x = x⁻¹ := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, N = 3 + k := ⟨N - 3, by omega⟩
  obtain ⟨f, hf1, hK⟩ := card_eq_two_pow (K := K)
  have htr := standard_automorphism_transport (K := K) (n := 3 + k)
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hN
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  have hAInn : ∀ x ∈ A, x ∈ inner (projectiveSL (3 + k) K) → x = 1 := fun x hx hxi => by
    have : x ∈ A ⊓ inner (projectiveSL (3 + k) K) := ⟨hx, hxi⟩
    rw [hAI] at this
    exact this
  have hD : ∀ x ∈ A, x ∈ linearAutGroup (3 + k) K → x = 1 := fun x hx hxD =>
    hAInn x hx (CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two hN
      (not_two_dvd_gcd _) x hxD 1 (by rw [pow_one, pow_two, hsq x hx]; exact one_mem _))
  have trich : ∀ x ∈ A, x ≠ 1 →
      (∃ (B : GL (Fin (3 + k)) K) (σ : K ≃+* K), σ ≠ 1 ∧
          x = conjAut (3 + k) K B * fieldAut (3 + k) K σ * dualAut (3 + k) K) ∨
      (∃ (B : GL (Fin (3 + k)) K) (σ : K ≃+* K), σ ≠ 1 ∧
          x = conjAut (3 + k) K B * fieldAut (3 + k) K σ) ∨
      (∃ B : GL (Fin (3 + k)) K, x = conjAut (3 + k) K B * dualAut (3 + k) K) := by
    intro x hx hx1
    obtain ⟨B, σ, ε, hε, rfl⟩ := hgen x
    interval_cases ε
    · right; left
      refine ⟨B, σ, ?_, by rw [pow_zero, mul_one]⟩
      rintro rfl
      apply hx1
      apply hD _ hx
      rw [map_one, mul_one, pow_zero, mul_one]
      exact conjAut_mem_linearAutGroup B
    · by_cases hσ : σ = 1
      · right; right
        exact ⟨B, by rw [pow_one, hσ, map_one, mul_one]⟩
      · left
        exact ⟨B, σ, hσ, by rw [pow_one]⟩
  have pairE : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      (∃ (B : GL (Fin (3 + k)) K) (σ : K ≃+* K), σ ≠ 1 ∧
          x = conjAut (3 + k) K B * fieldAut (3 + k) K σ) →
      (∃ (B : GL (Fin (3 + k)) K) (σ : K ≃+* K), σ ≠ 1 ∧
          y = conjAut (3 + k) K B * fieldAut (3 + k) K σ) → False := by
    rintro x hx y hy hxy ⟨B, σ, hσ, rfl⟩ ⟨C, ρ, hρ, rfl⟩
    have hσσ : σ * σ = 1 := by
      have h := hsq _ hx
      rw [conjAut_mul_fieldAut_mul] at h
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one hN _ _ h).1
    have hρρ : ρ * ρ = 1 := by
      have h := hsq _ hy
      rw [conjAut_mul_fieldAut_mul] at h
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one hN _ _ h).1
    have hσρ : σ = ρ := involution_unique hf1 hK hσ hσσ hρ hρρ
    subst hσρ
    have hprod : conjAut (3 + k) K B * fieldAut (3 + k) K σ *
        (conjAut (3 + k) K C * fieldAut (3 + k) K σ) =
        conjAut (3 + k) K (B * GeneralLinearGroup.map (σ : K →+* K) C) := by
      rw [conjAut_mul_fieldAut_mul, hσσ, map_one, mul_one]
    have hmem : conjAut (3 + k) K B * fieldAut (3 + k) K σ *
        (conjAut (3 + k) K C * fieldAut (3 + k) K σ) ∈ linearAutGroup (3 + k) K := by
      rw [hprod]; exact conjAut_mem_linearAutGroup _
    have h1 := hD _ (A.mul_mem hx hy) hmem
    apply hxy
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [hinv _ hx] at h2
    exact h2.symm
  have pairG : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      (∃ B : GL (Fin (3 + k)) K, x = conjAut (3 + k) K B * dualAut (3 + k) K) →
      (∃ B : GL (Fin (3 + k)) K, y = conjAut (3 + k) K B * dualAut (3 + k) K) → False := by
    rintro x hx y hy hxy ⟨B, rfl⟩ ⟨C, rfl⟩
    have hprod : conjAut (3 + k) K B * dualAut (3 + k) K *
        (conjAut (3 + k) K C * dualAut (3 + k) K) =
        conjAut (3 + k) K (B * GeneralLinearGroup.inverseTranspose C) := by
      calc conjAut (3 + k) K B * dualAut (3 + k) K * (conjAut (3 + k) K C * dualAut (3 + k) K)
          = conjAut (3 + k) K B *
              (dualAut (3 + k) K * conjAut (3 + k) K C * dualAut (3 + k) K) := by
            simp only [mul_assoc]
        _ = conjAut (3 + k) K B * conjAut (3 + k) K (GeneralLinearGroup.inverseTranspose C) := by
            rw [htr.2.2.2.2.1]
        _ = _ := by rw [htr.1]
    have hmem : conjAut (3 + k) K B * dualAut (3 + k) K *
        (conjAut (3 + k) K C * dualAut (3 + k) K) ∈ linearAutGroup (3 + k) K := by
      rw [hprod]; exact conjAut_mem_linearAutGroup _
    have h1 := hD _ (A.mul_mem hx hy) hmem
    apply hxy
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [hinv _ hx] at h2
    exact h2.symm
  have hsucc : ∃ x ∈ A, x ≠ 1 ∧ ∃ (B : GL (Fin (3 + k)) K) (σ : K ≃+* K), σ ≠ 1 ∧
      x = conjAut (3 + k) K B * fieldAut (3 + k) K σ * dualAut (3 + k) K := by
    by_contra hno
    push Not at hno
    obtain ⟨a, ha, ha1, b, hb, hb1, hab⟩ := exists_two_ne_one A hcard
    have hc : a * b ∈ A := A.mul_mem ha hb
    have hc1 : a * b ≠ 1 := by
      intro h
      apply hab
      have h2 := eq_inv_of_mul_eq_one_right h
      rw [hinv _ ha] at h2
      exact h2.symm
    have hac : a ≠ a * b := fun h => hb1 (by simpa using h)
    have hbc : b ≠ a * b := fun h => ha1 (by simpa using h)
    have shape : ∀ x ∈ A, x ≠ 1 →
        (∃ (B : GL (Fin (3 + k)) K) (σ : K ≃+* K), σ ≠ 1 ∧
          x = conjAut (3 + k) K B * fieldAut (3 + k) K σ) ∨
        (∃ B : GL (Fin (3 + k)) K, x = conjAut (3 + k) K B * dualAut (3 + k) K) := by
      intro x hx hx1
      rcases trich x hx hx1 with ⟨B, σ, hσ, h⟩ | h | h
      · exact absurd h (hno x hx hx1 B σ hσ)
      · exact Or.inl h
      · exact Or.inr h
    rcases shape a ha ha1 with ea | ga
    · rcases shape b hb hb1 with eb | gb
      · exact pairE a ha b hb hab ea eb
      · rcases shape _ hc hc1 with ec | gc
        · exact pairE a ha _ hc hac ea ec
        · exact pairG b hb _ hc hbc gb gc
    · rcases shape b hb hb1 with eb | gb
      · rcases shape _ hc hc1 with ec | gc
        · exact pairE b hb _ hc hbc eb ec
        · exact pairG a ha _ hc hac ga gc
      · exact pairG a ha b hb hab ga gb
  obtain ⟨x, hx, hx1, B, σ, hσ, rfl⟩ := hsucc
  have hα : (conjAut (3 + k) K B * fieldAut (3 + k) K σ * dualAut (3 + k) K) ^ 2 = 1 :=
    hA.2 _ hx
  obtain ⟨-, -, H, hH⟩ :=
    odd_linear_graph_field_involution_conjugacy Nat.prime_two hf1 hK hN B σ hσ hα
  set y := proj (3 + k) K (sl7 k) with hy
  have hy7 : y ^ 7 = 1 := by rw [hy, ← map_pow, sl7_pow, map_one]
  have hy1 : y ≠ 1 := fun h => sl7_not_scalar k (proj_eq_one_iff.1 h)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf y = 7 := orderOf_eq_prime hy7 hy1
  refine ⟨_, hx, hx1, conjAut (3 + k) K H y, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hord]; decide
  · rw [MulEquiv.orderOf_eq, hord]; norm_num
  · have h1 := fieldAut_dualAut_apply_symm σ (sl7 k) (sl7_symm k) (sl7_map k σ)
    rw [hH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [h1, map_inv]

end CFSG.LieType.ChevTwo
