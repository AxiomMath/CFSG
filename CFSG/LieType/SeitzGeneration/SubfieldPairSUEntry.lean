module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUGen
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLEntry

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem suConj_injective (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1) :
    Function.Injective (suConj hσ A hA) := by
  intro g g' h
  apply Subtype.ext
  have h1 := congrArg (fun x : SUid σ n => (x : GL (Fin n) K)) h
  simp only [coe_suConj] at h1
  exact mul_left_cancel (mul_right_cancel h1)

theorem entry_of_tv {t : SUid σ n} {a : Fin n → K} {c : K}
    (h : ∀ v, t • v = v + (c * herm σ a v) • a) (i j : Fin n) :
    ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (1 : Matrix (Fin n) (Fin n) K) i j + c * a i * σ (a j) := by
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [smul_def, Matrix.mulVec_single_one] at h1
  rw [herm_single_right, mul_one] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
  rw [h1, Matrix.one_apply, Pi.single_apply]
  split_ifs with hij
  · subst hij; ring
  · ring

variable {k : Subfield K} (hk : ∀ x ∈ k, σ x ∈ k)

theorem tv_mem_ratSU (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : IsRat k a)
    (hia : herm σ a a = 0) {c : K} (hc : c ∈ k) (hct : c + σ c = 0) :
    tv hσ hia hct ∈ ratSU σ k hk n := by
  intro i j
  rw [entry_of_tv (tv_smul hσ hia hct) i j]
  refine k.add_mem ?_ (k.mul_mem (k.mul_mem hc (ha i)) (hk _ (ha j)))
  by_cases hij : i = j
  · subst hij; simp [k.one_mem]
  · simp [Matrix.one_apply_ne hij, k.zero_mem]

section Main

variable [Finite K] {p : ℕ}

theorem exists_offDiag_not_mem_su (hσ : ∀ c, σ (σ c) = c) (hk : ∀ x ∈ k, σ x ∈ k)
    (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K)) (hU : IsUnitaryInvolution σk)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : k, s ≠ 0 ∧ σk s * s ≠ 1) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (hne : (ratSU σ k hk n).map (suConj hσ A hA) ≠ ratSU σ k hk n) :
    ∃ (a : Fin n → K) (c : K), IsRat k a ∧ herm σ a a = 0 ∧ c ∈ k ∧ c + σ c = 0 ∧
      ∃ r s : Fin n, r ≠ s ∧ c * ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) r *
        σ (((A : Matrix (Fin n) (Fin n) K) *ᵥ a) s) ∉ k := by
  by_contra hall
  push Not at hall
  refine hne (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · rw [Subgroup.map_le_iff_le_comap]
    refine le_trans (ratSU_le_closure_ratTv σk hσk hk hU hn h3) ((Subgroup.closure_le _).2 ?_)
    rintro t ⟨a, c, ha, hia, hc, hct, ht⟩
    show suConj hσ A hA t ∈ ratSU σ k hk n
    set b : Fin n → K := (A : Matrix (Fin n) (Fin n) K) *ᵥ a with hb
    have hbb : herm σ b b = 0 := by rw [hb, herm_mulVec_unitary A hA, hia]
    have hoff : ∀ r s, r ≠ s → c * b r * σ (b s) ∈ k := hall a c ha hia hc hct
    have hdiag : ∀ r, c * b r * σ (b r) ∈ k := by
      intro r
      have hdot : (fun s => c * σ (b s)) ⬝ᵥ b = 0 := by
        have : (fun s => c * σ (b s)) ⬝ᵥ b = c * herm σ b b := by
          simp only [dotProduct, herm, Finset.mul_sum, mul_assoc]
        rw [this, hbb, mul_zero]
      have hsq := sq_diag_mem (k := k) b (fun s => c * σ (b s)) hdot
        (fun r' s hrs => by
          have := hoff r' s hrs
          rwa [show c * b r' * σ (b s) = b r' * (c * σ (b s)) by ring] at this) r
      have := mem_of_quadratic hp hp2 hK (x := b r * (c * σ (b r))) (α := 0)
        (β := -(b r * (c * σ (b r))) ^ 2) k.zero_mem (k.neg_mem hsq) (by ring)
      rwa [show c * b r * σ (b r) = b r * (c * σ (b r)) by ring]
    intro i j
    rw [entry_of_tv (suConj_smul_of_tv hσ A hA ht) i j]
    refine k.add_mem ?_ ?_
    · by_cases hij : i = j
      · subst hij; simp [k.one_mem]
      · simp [Matrix.one_apply_ne hij, k.zero_mem]
    · by_cases hij : i = j
      · subst hij; exact hdiag i
      · exact hoff i j hij
  · exact (Subgroup.card_map_of_injective (suConj_injective hσ A hA)).ge

end Main

end CFSG.LieType.SeitzGeneration.SUPair
