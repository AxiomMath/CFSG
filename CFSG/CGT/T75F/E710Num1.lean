module

public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.CGT.T75F.E710Quot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.T75F

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki CFSG.CGT.Timmesfeld75

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem exists_delta_of_involution (hB : IsBenderGroup (X ⧸ Subgroup.center X)) (S : Sylow 2 X)
    (hMS : M ≤ S) {ω : X ⧸ Subgroup.center X}
    (hω : ω ∈ (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X))) (hω2 : ω * ω = 1)
    (hω1 : ω ≠ 1) : ∃ β ∈ D, β ∈ M ∧ (QuotientGroup.mk β : X ⧸ Subgroup.center X) = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hωord : orderOf ω = 2 := orderOf_eq_prime (by rw [pow_two]; exact hω2) hω1
  obtain ⟨y, hy, -⟩ := h.exists_out
  have hy2 : orderOf (QuotientGroup.mk y : X ⧸ Subgroup.center X) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.Dhat_sq ⟨y, hy, rfl⟩) (h.mk_ne_one hy)
  obtain ⟨g, hg⟩ := isConj_iff.1 (IsBenderGroup.isConj_of_orderOf_eq_two hB hy2 hωord)
  have hωD : ω ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D := by
    rw [← hg]
    exact h.Dhat_conj ⟨y, hy, rfl⟩ g
  obtain ⟨d, hd, hdω⟩ := hωD
  obtain ⟨s, hs, hsω⟩ := Subgroup.mem_map.1 hω
  have hz : s⁻¹ * d ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 : (QuotientGroup.mk s : X ⧸ Subgroup.center X) = ω := hsω
    have h2 : (QuotientGroup.mk d : X ⧸ Subgroup.center X) = ω := hdω
    rw [h1, h2]
    exact inv_mul_cancel _
  set z := s⁻¹ * d with hzdef
  have hdsz : d = s * z := by rw [hzdef]; group
  have hzc : ∀ x : X, x * z = z * x := Subgroup.mem_center_iff.1 hz
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨s, hs⟩
  have hsb : s ^ (2 ^ b) = 1 := by
    have h1 : orderOf s = 2 ^ b := by rw [← hb]; exact (Subgroup.orderOf_mk _ _).symm
    rw [← h1]
    exact pow_orderOf_eq_one s
  have hd2 := h.sq_eq_one d hd
  have hzz : z * z = (s ^ 2)⁻¹ := by
    have h1 : (s * z) * (s * z) = 1 := by rw [← hdsz]; exact hd2
    have h2 : s ^ 2 * (z * z) = 1 := by
      calc s ^ 2 * (z * z) = s * (s * z) * z := by rw [pow_two]; simp only [mul_assoc]
        _ = s * (z * s) * z := by rw [hzc s]
        _ = (s * z) * (s * z) := by group
        _ = 1 := h1
    exact eq_inv_of_mul_eq_one_right h2
  have hzpow : z ^ (2 ^ (b + 1)) = 1 := by
    have h1 : z ^ 2 = (s ^ 2)⁻¹ := by rw [pow_two z]; exact hzz
    calc z ^ (2 ^ (b + 1)) = (z ^ 2) ^ (2 ^ b) := by rw [← pow_mul, pow_succ']
      _ = ((s ^ 2)⁻¹) ^ (2 ^ b) := by rw [h1]
      _ = ((s ^ (2 ^ b)) ^ 2)⁻¹ := by rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [hsb]; simp
  have hordz : orderOf z ∣ 2 ^ (b + 1) := orderOf_dvd_of_pow_eq_one hzpow
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hordz
  have hP : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hnorm : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * z * g⁻¹ = z := by rw [hzc g]; group
    rw [← conj_zpow, this]
    exact Subgroup.zpow_mem_zpowers z k
  have hzS : z ∈ (S : Subgroup X) := hP.le_sylow_of_normal S (Subgroup.mem_zpowers z)
  have hdS : d ∈ (S : Subgroup X) := by rw [hdsz]; exact (S : Subgroup X).mul_mem hs hzS
  exact ⟨d, hd, h.mem_M_of_mem_sylow S hMS hd hdS, hdω⟩

end Endgame710

end CFSG.CGT.T75F
