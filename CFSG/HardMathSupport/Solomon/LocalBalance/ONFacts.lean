module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace ONFactsNs

theorem psl_arith (q : ℕ) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) ≠ orderON := by
  intro h
  by_cases hq : 41 ≤ q
  · have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 1681 ≤ q ^ 2 := by nlinarith
    have h2 : 68921 ≤ q ^ 3 := by nlinarith
    have h3 : 68921 * (1680 * 68920) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h2 (Nat.mul_le_mul (by omega) (by omega))
    have h4 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 ≤
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) :=
      Nat.div_le_div_left hg (by omega)
    have h5 : orderON < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      unfold orderON
      omega
    omega
  · push Not at hq
    interval_cases q <;> simp [orderON] at h

theorem psu_arith (q : ℕ) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) ≠ orderON := by
  intro h
  by_cases hq : 41 ≤ q
  · have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 1681 ≤ q ^ 2 := by nlinarith
    have h2 : 68921 ≤ q ^ 3 := by nlinarith
    have h3 : 68921 * (1680 * 68922) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul h2 (Nat.mul_le_mul (by omega) (by omega))
    have h4 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 ≤
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) :=
      Nat.div_le_div_left hg (by omega)
    have h5 : orderON < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      unfold orderON
      omega
    omega
  · push Not at hq
    interval_cases q <;> simp [orderON] at h

theorem card_psl3_ne {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) ≠ orderON := by
  intro h
  have e := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
    (by norm_num : 1 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at e
  have h' : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K))
      = orderON := h
  rw [e] at h'
  exact psl_arith (Nat.card K) (by simpa using h')

theorem card_psu3_ne {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card (StatedProj (StatedSU 3 q K)) ≠ orderON := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpc, n, hp, hn⟩ := FiniteField.card' (K := K)
  have hqn : q ^ 2 = p ^ (n : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hn]
  have hqd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hqn]; ring⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hq1 : q ≠ 1 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := K)
    rw [hK] at h1
    simp at h1
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exact absurd (by simpa [h0] using hf) hq1
    · exact h0
  subst hf
  intro h
  have e := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) hp hf1 hK
    (by norm_num : 2 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at e
  have h' : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) = orderON := h
  rw [e] at h'
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h2 : (((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
    have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]; ring]
    exact Int.toNat_natCast _
  have h3 : (((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3] at h'
  exact psu_arith (p ^ f) (by simpa using h')

end ONFactsNs

open ONFactsNs

theorem inputONSimple_of_group (h : UniquenessMaximal.InputONGroup) : Lemma59Ns.InputONSimple := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨hs, ?_⟩
  by_contra hno
  push Not at hno
  haveI : IsMulCommutative (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group :=
    ⟨⟨fun a b => hno a b⟩⟩
  haveI := hs
  have hp : (Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group).Prime :=
    IsSimpleGroup.prime_card
  rw [hc] at hp
  unfold orderON at hp
  exact absurd hp (by norm_num)

theorem inputONTypes_of_group (h : UniquenessMaximal.InputONGroup) : Lemma59Ns.InputONTypes := by
  intro K _ ⟨e⟩
  have hK : Nat.card K = orderON := by
    rw [Nat.card_congr e.toEquiv]; exact h.2
  refine ⟨?_, ?_⟩
  · rintro (⟨F, _, _, -, ⟨e'⟩⟩ | ⟨F, _, _, q, hF, -, -, ⟨e'⟩⟩)
    · exact card_psl3_ne ((Nat.card_congr e'.toEquiv).symm.trans hK)
    · exact card_psu3_ne hF ((Nat.card_congr e'.toEquiv).symm.trans hK)
  · rintro ⟨F, _, _, -, ⟨e'⟩⟩
    exact card_psl3_ne ((Nat.card_congr e'.toEquiv).symm.trans hK)

theorem input3_3_ON_of_group (h : UniquenessMaximal.InputONGroup) : Lemma53Ns.Input3_3_ON := by
  refine ⟨fun K _ _ => ⟨fun e => ?_⟩, fun K _ _ q hK => ⟨fun e => ?_⟩⟩
  · exact card_psl3_ne ((Nat.card_congr e.toEquiv).symm.trans h.2)
  · exact card_psu3_ne hK ((Nat.card_congr e.toEquiv).symm.trans h.2)


theorem inputONNotIso_of_group
    (h : UniquenessMaximal.InputONGroup) : Lemma56Ns.InputONNotIso := by
  have hON : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group = orderON := h.2
  have hA : ∀ n : ℕ, Nontrivial (Fin n) → ∀ e : (TauCeti.CFSGIndex.sporadic
      TauCeti.SporadicName.ONan).Group ≃* alternatingGroup (Fin n),
      (Nat.factorial (Fintype.card (Fin n))) / 2 = orderON := by
    intro n hn e
    rw [← card_alternatingGroup, ← Nat.card_eq_fintype_card, ← Nat.card_congr e.toEquiv, hON]
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · have := hA 6 inferInstance e
    simp [orderON, Nat.factorial] at this
  · have := hA 7 inferInstance e
    simp [orderON, Nat.factorial] at this
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    have h1 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520 := by
      rw [← Nat.card_congr b.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M22
    have h2 := Nat.card_congr e.toEquiv
    rw [hON, h1] at h2
    simp [orderON] at h2

end CFSG.HardMathSupport.Solomon.LocalBalance
