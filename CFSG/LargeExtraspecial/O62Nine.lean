module

public import CFSG.LargeExtraspecial.O62Transport
public import CFSG.LargeExtraspecial.O62Data
public import CFSG.LargeExtraspecial.O62Model

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Code

@[expose] def npowC (c : ℕ) : ℕ → ℕ
  | 0 => one
  | k + 1 => mul c (npowC c k)

theorem hasCode_pow {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hg : HasCode g c) :
    ∀ k : ℕ, HasCode ((g ^ k : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) (npowC c k)
  | 0 => hasCode_one
  | k + 1 => by
    rw [pow_succ']
    exact hg.mul (hasCode_pow hg k)

theorem npowC_lt (c : ℕ) : ∀ k, npowC c k < 2 ^ 36
  | 0 => one_lt
  | _ + 1 => mul_lt _ _

theorem nineWord_letters : ∀ n ∈ nineWord, qB true n = true := by decide +kernel

theorem npowC_nineWord_nine : npowC (wordC nineWord) 9 = one := by decide +kernel

theorem npowC_nineWord_three : npowC (wordC nineWord) 3 ≠ one := by decide +kernel

theorem wordProd_nineWord_mem : wordProd nineWord ∈ Ω₀ true :=
  (wordProd_mem_omegaGroup_iff nineWord_letters).mpr ⟨3, rfl⟩

theorem orderOf_wordProd_nineWord : orderOf (wordProd nineWord) = 9 := by
  have h9 : wordProd nineWord ^ 9 = 1 := by
    have h := hasCode_pow (hasCode_wordProd nineWord) 9
    rw [npowC_nineWord_nine] at h
    exact h.eq_of_equiv hasCode_one
  have h3 : wordProd nineWord ^ 3 ≠ 1 := by
    intro h
    have h1 := hasCode_pow (hasCode_wordProd nineWord) 3
    rw [h] at h1
    exact npowC_nineWord_three (h1.code_eq hasCode_one (npowC_lt _ _) one_lt)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime_pow (p := 3) (n := 1) (by simpa using h3) (by simpa using h9)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_orderOf_eq_nine [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate) (hm : ¬ IsPlus Q) :
    ∃ x ∈ omegaGroup Q hQ, orderOf x = 9 := by
  obtain ⟨L, hL⟩ := exists_linearEquiv_qMinus hV hQ hm
  have hL' : ∀ v, qModel true (L v) = Q v := fun v => by rw [qModel_true]; exact hL v
  refine ⟨(conjL L).symm (wordProd nineWord), ?_, ?_⟩
  · rw [← mem_omegaGroup_conjL hQ (qModel_nondegenerate true) hL', MulEquiv.apply_symm_apply]
    exact wordProd_nineWord_mem
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_wordProd_nineWord

end CFSG.LargeExtraspecial.O62
