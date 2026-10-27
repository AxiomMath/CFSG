module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Balance

theorem le_of_isComponentOf_of_coprime_quotient {Z : Type*} [Group Z] [Finite Z] {p : ℕ}
    (hp : p.Prime) (hO : GLAPPrimeCore p Z = ⊥) {N M : Subgroup Z} [N.Normal] (hNM : N ≤ M)
    (hexp : ∀ x ∈ M, ∃ n : ℕ, Nat.Coprime p n ∧ x ^ n ∈ N) (hab : commutator Z ≤ M)
    {L : Subgroup Z} (hL : CFSG.Open.IsComponentOf L ⊤) : L ≤ N := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLsn : CFSG.Open.IsSubnormal L ⊤ := hL.2.1
  have hLL : ⁅L, L⁆ = L := by
    have h2 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h2, hq.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hLM : L ≤ M := by
    have h1 : ⁅L, L⁆ ≤ commutator Z := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact (hLL ▸ h1).trans hab
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    (N.subgroupOf L) with hcen | htop
  · exfalso
    have hquot : Nat.Coprime p (Nat.card (↥L ⧸ Subgroup.center ↥L)) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L ⧸ Subgroup.center ↥L) p hdvd
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨n, hn, hxn⟩ := hexp (x : Z) (hLM x.2)
      have hxn' : x ^ n ∈ N.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hxn
      have h1 : (QuotientGroup.mk (x ^ n) : ↥L ⧸ Subgroup.center ↥L) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (hcen hxn')
      have h2 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) ^ n = 1 := by
        rw [← QuotientGroup.mk_pow]
        exact h1
      have h3 : p ∣ n := hg ▸ orderOf_dvd_of_pow_eq_one h2
      exact hp.one_lt.ne' (hn.eq_one_of_dvd h3)
    have hZp : Nat.Coprime (Nat.card (Subgroup.center ↥L))
        (Nat.card (↥L ⧸ Subgroup.center ↥L)) := by
      refine Nat.coprime_of_dvd fun q hq' hqd hqd2 => ?_
      have hqp := prime_eq_of_dvd_card_center hp hO hLsn hq' hqd
      subst hqp
      exact (Nat.Prime.coprime_iff_not_dvd hq').1 hquot hqd2
    have hc : Subgroup.center ↥L = ⊥ := center_eq_bot_of_perfect_of_coprime ⟨hq.1⟩ hZp
    have hcard : Nat.Coprime p (Nat.card L) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      have h1 : Nat.card (Subgroup.center ↥L) = 1 := by rw [hc, Subgroup.card_bot]
      rw [h1, mul_one] at h
      rw [h]
      exact hquot
    have hLbot : L = ⊥ := eq_bot_of_isSubnormal_coprime hp hO hLsn hcard
    have hnt := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hnt hLbot
  · exact Subgroup.subgroupOf_eq_top.1 htop

end CFSG.HardMathSupport.Dickson.I271
