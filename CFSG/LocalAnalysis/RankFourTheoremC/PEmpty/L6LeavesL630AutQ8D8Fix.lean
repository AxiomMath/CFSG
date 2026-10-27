module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630AutQ8D8Center

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.AutQ8D8

variable {R : Type} [Group R]

@[expose] def fixSub (Q : Subgroup (MulAut R)) : Subgroup R where
  carrier := {r | ∀ q ∈ Q, q r = r}
  mul_mem' := by
    intro a b ha hb q hq
    show q (a * b) = a * b
    rw [map_mul, ha q hq, hb q hq]
  one_mem' := by
    intro q _
    exact map_one q
  inv_mem' := by
    intro a ha q hq
    show q a⁻¹ = a⁻¹
    rw [map_inv, ha q hq]

theorem mem_fixSub {Q : Subgroup (MulAut R)} {r : R} :
    r ∈ fixSub Q ↔ ∀ q ∈ Q, q r = r :=
  Iff.rfl

theorem fixedPoints_eq (Q : Subgroup (MulAut R)) :
    MulAction.fixedPoints ↥Q R = (fixSub Q : Set R) := by
  ext r
  rw [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixSub]
  constructor
  · intro h q hq
    exact h ⟨q, hq⟩
  · intro h m
    exact h m.1 m.2

theorem mem_center_of_fixed [Finite R] {Q : Subgroup (MulAut R)} (hQ : IsPGroup 5 Q)
    (hQne : ∃ q ∈ Q, q ≠ 1) (hR : Nat.card R = 32) (hcen : Nat.card (Subgroup.center R) = 2)
    (hfix : ∀ q : MulAut R, ∀ z ∈ Subgroup.center R, q z = z) {r : R}
    (hr : ∀ q ∈ Q, q r = r) : r ∈ Subgroup.center R := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod : Nat.card R ≡ Nat.card (fixSub Q) [MOD 5] := by
    have h := hQ.card_modEq_card_fixedPoints R
    rw [fixedPoints_eq] at h
    exact h
  have hdvd : Nat.card (fixSub Q) ∣ 2 ^ 5 := by
    have h32 : (2 : ℕ) ^ 5 = Nat.card R := by norm_num [hR]
    rw [h32]
    exact Subgroup.card_subgroup_dvd_card (fixSub Q)
  obtain ⟨m, hm, hFm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h5 : 2 ^ m % 5 = 2 := by
    rw [← hFm]
    unfold Nat.ModEq at hmod
    rw [hR] at hmod
    omega
  have hm15 : m = 1 ∨ m = 5 := by
    interval_cases m
    · norm_num at h5
    · exact Or.inl rfl
    · norm_num at h5
    · norm_num at h5
    · norm_num at h5
    · exact Or.inr rfl
  rcases hm15 with rfl | rfl
  ·
    have hle : Subgroup.center R ≤ fixSub Q := by
      intro z hz
      rw [mem_fixSub]
      intro q _
      exact hfix q z hz
    have heq : Subgroup.center R = fixSub Q :=
      Subgroup.eq_of_le_of_card_ge hle (by norm_num [hcen, hFm])
    rw [heq]
    exact mem_fixSub.mpr hr
  ·
    have htop : fixSub Q = ⊤ :=
      Subgroup.eq_top_of_card_eq (fixSub Q) (by norm_num [hFm, hR])
    obtain ⟨q, hq, hq1⟩ := hQne
    exfalso
    apply hq1
    apply MulEquiv.ext
    intro x
    have hx : x ∈ fixSub Q := by
      rw [htop]
      exact Subgroup.mem_top x
    exact (mem_fixSub.mp hx) q hq

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.AutQ8D8
