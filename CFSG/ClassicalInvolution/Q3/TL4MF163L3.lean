module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Z
public import CFSG.ClassicalInvolution.Q3.TL4MF163L33

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem model163L3_proved :
    Model163L3 := by
  intro X _ _ R S z hm _ _ _ h3 p f hp hp2 hl
  have hl' := hl
  rcases hl' with ⟨-, -, K, _, _, hK, ⟨e₀⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  rotate_left
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  set N := genFittingFStar X with hNdef
  have hNn : N.Normal := genFittingFStar_normal X
  let e₁ : FStarQuot X ≃* projectiveSL 3 K :=
    (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  obtain ⟨a, b, hab⟩ := MF163.L3.exists_noncomm (K := K)
  have hZ : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · exfalso
      have h1 : ∀ q : FStarQuot X, q = 1 := fun q => by
        obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
        exact (QuotientGroup.eq_one_iff n).2 (h ▸ Subgroup.mem_top n)
      apply hab
      rw [← e₁.apply_symm_apply a, ← e₁.apply_symm_apply b, h1 (e₁.symm a), h1 (e₁.symm b)]
  let ψ : ↥N ≃* FStarQuot X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let e : ↥N ≃* projectiveSL 3 K := ψ.trans e₁
  have hnab : ∃ a b : N, a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact h
  by_cases hq3 : p ^ f = 3
  · exfalso
    obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
    obtain ⟨eQ⟩ := GH74.KGroups.L33.equiv_of_lieModel hl
    exact h3 (MF163.tightActs3_of_l33 (centralizer_genFittingFStar_eq_bot hnab) (ψ.trans eQ)
      hm.datum hm.cls)
  · have h5 : 5 ≤ p ^ f := by
      have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      obtain ⟨k, hk⟩ := hodd
      omega
    exact MF163.L3.concl163_of_psl3 hm hp hp2 hf hK h5 e

end CFSG.ClassicalInvolution.Q3.TL4
