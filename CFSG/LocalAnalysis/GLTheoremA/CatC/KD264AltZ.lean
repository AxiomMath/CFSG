module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultBound
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Z

theorem isPGroup_center_of_pPrimeCore {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (hcore : CFSG.pPrimeCore p G = ⊥) : IsPGroup p (Subgroup.center G) := by
  classical
  intro z
  have hz0 : orderOf (z : G) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨e, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0 p hp.one_lt.ne'
  refine ⟨e, Subtype.ext ?_⟩
  set u : G := (z : G) ^ (p ^ e) with hu
  have hucen : u ∈ Subgroup.center G := Subgroup.pow_mem _ z.2 _
  have hord : orderOf u = n' := by
    rw [hu, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (Dvd.intro _ hn.symm), hn,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos e)]
  have hnormal : (Subgroup.zpowers u).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcomm : Commute g u := Subgroup.mem_center_iff.1 hucen g
    have hgi : g * u ^ i * g⁻¹ = u ^ i := by
      rw [(hcomm.zpow_right i).eq, mul_inv_cancel_right]
    rw [hgi]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) i
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers u)) := by
    rw [Nat.card_zpowers, hord]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn'
  have hle : Subgroup.zpowers u ≤ CFSG.pPrimeCore p G := le_sSup ⟨hnormal, hcop⟩
  rw [hcore] at hle
  have hbot : Subgroup.zpowers u = ⊥ := le_bot_iff.1 hle
  have hu1 : u = 1 := by
    have := Subgroup.mem_zpowers u
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact hu1

theorem center_eq_bot_or_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) (hcore : CFSG.pPrimeCore p K = ⊥) {n : ℕ}
    (hn : 5 ≤ n) (eK : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Subgroup.center K = ⊥ ∨ (Nat.card (Subgroup.center K) = 3 ∧ (n = 6 ∨ n = 7)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨a, ha⟩ := (isPGroup_center_of_pPrimeCore hp hcore).exists_card_eq
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  set π : K →* alternatingGroup (Fin n) :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
  have hπ : Function.Surjective π := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    rw [ha]
    exact hpodd.pow
  by_cases hn8 : 8 ≤ n
  · left
    have hdvd := card_center_dvd_hopfMultiplier_of_cover hK π hπ hker
    rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup hn8] at hdvd
    have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 2 := Odd.coprime_two_right hodd
    have h1 : Nat.card (Subgroup.center K) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact Subgroup.eq_bot_of_card_eq _ h1
  · have hn8' : n ≤ 8 := by omega
    have hsmall := CFSG.SectionRank.alternating_small_odd_cover_bound hn hn8' π hπ
      (hker.le) (by rw [hker]; exact hodd)
    rw [hker] at hsmall
    obtain ⟨h58, h67⟩ := hsmall
    rcases (show n = 5 ∨ n = 6 ∨ n = 7 by omega) with h5 | h6 | h7
    · left
      exact h58 (Or.inl h5)
    · rcases h67 (Or.inl h6) with h1 | h3
      · left
        exact Subgroup.eq_bot_of_card_eq _ h1
      · right
        exact ⟨h3, Or.inl h6⟩
    · rcases h67 (Or.inr h7) with h1 | h3
      · left
        exact Subgroup.eq_bot_of_card_eq _ h1
      · right
        exact ⟨h3, Or.inr h7⟩

theorem fullCoverLevel_ne_four {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    (h : K1Cover p Q ∨ K2Cover p Q ∨ K3Cover p Q) : fullCoverLevel p Q ≠ 4 := by
  unfold fullCoverLevel
  by_cases h1 : K1Cover p Q
  · rw [if_pos h1]
    norm_num
  · by_cases h2 : K2Cover p Q
    · rw [if_neg h1, if_pos h2]
      norm_num
    · have h3 : K3Cover p Q := (h.resolve_left h1).resolve_left h2
      rw [if_neg h1, if_neg h2, if_pos h3]
      norm_num

end CFSG.LocalAnalysis.GLTheoremA.KD264Z
