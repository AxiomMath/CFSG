module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.ShapeCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.BarX
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.FiveType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.NoInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Shape4A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.SmallGroups

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem t3_dvd_fifteen_of_dvd_120_of_not_two {n : ℕ} (h : n ∣ 120) (h2 : ¬ 2 ∣ n) :
    n ∣ 15 := by
  have h' : n ∣ 8 * 15 := by
    rwa [show (8 : ℕ) * 15 = 120 from by norm_num]
  have hcop : Nat.Coprime n 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num]
    exact (Nat.coprime_pow_right_iff (by norm_num : 0 < 3) n 2).mpr
      (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  exact (Nat.Coprime.dvd_mul_left hcop).mp h'

private theorem t3_eq_one_or_three_or_five_of_dvd_fifteen {n : ℕ} (h : n ∣ 15) (hne : n ≠ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 := by
  have hmem : n ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  have hset : Nat.divisors 15 = {1, 3, 5, 15} := by decide
  rw [hset] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h3 | h5 | h15
  · exact Or.inl h1
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h5)
  · exact absurd h15 hne

theorem tableIII_card_bar_dvd_4A (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hSGz : StructGzFacts a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z)
    (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 2) :
    Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ 15 := by
  have hHX : Gxyz a' z c ≤ Gxy a' z := by
    intro g hg
    obtain ⟨h1, h2, -⟩ := mem_Gxyz.1 hg
    exact mem_Gxy.2 ⟨h1, h2⟩
  have hle : tableIIIBar z (Gxyz a' z c) ≤ tableIIIBar z (Gxy a' z) :=
    tableIII_bar_mono hHX
  have hcardX : Nat.card ↥(tableIIIBar z (Gxy a' z)) = 120 :=
    tableIII_card_bar_Gxy hI h hX ha'Q ha'
  have hdvd120 : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ 120 := by
    rw [← hcardX]
    exact Subgroup.card_dvd_of_le hle
  have hnoinv : ¬ 2 ∣ Nat.card ↥(tableIIIBar z (Gxyz a' z c)) := by
    intro h2dvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    obtain ⟨x, hxH, hxy⟩ := tableIII_exists_of_mem_bar y.2
    have hbar2 : barOf z x ^ 2 = 1 := by
      rw [hxy]
      simpa [Subgroup.orderOf_coe y, hy2] using pow_orderOf_eq_one (↑y : Gbar z)
    have hbar1 : barOf z x = 1 :=
      tableIII_barOf_eq_one_4A hI h hSGz ha'Q ha' hc x hxH hbar2
    have hy1 : y = 1 := by
      apply Subtype.ext
      rw [hxy] at hbar1
      exact hbar1
    rw [hy1, orderOf_one] at hy2
    norm_num at hy2
  exact t3_dvd_fifteen_of_dvd_120_of_not_two hdvd120 hnoinv

theorem tableIII_card_bar_ne_4A (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hSGz : StructGzFacts a z) (ha'Q : a' ∈ Qz z) (ha' : IsConj a a')
    (hc : c ∈ tab3Set a z a' 2) : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ≠ 15 := by
  intro hB
  have hHGz : Gxyz a' z c ≤ Gx z := by
    intro g hg
    exact (mem_Gxyz.1 hg).2.1
  have hcard := tableIII_card_eq_card_inf_mul_card_bar (K := Gxyz a' z c) hHGz
  have hQcard := tableIII_card_inf_Qz_4A hI h ha'Q ha' hc
  have hHcard : Nat.card ↥(Gxyz a' z c) = 2 ^ 7 * 15 := by
    rw [hcard, hQcard, hB]
  have h5dvd : 5 ∣ Nat.card ↥(Gxyz a' z c) := by rw [hHcard]; norm_num
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ρ, hρ5⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  set ρ' : ↥(Gx z) := ⟨(ρ : G), hHGz ρ.2⟩ with hρ'def
  have hρ'val : (ρ' : G) = (ρ : G) := by rw [hρ'def]
  have hρ'5 : orderOf ρ' = 5 := by
    rw [hρ'def, Subgroup.orderOf_mk, Subgroup.orderOf_coe ρ, hρ5]
  obtain ⟨-, ha'1, ha'z, -, -, -, -, -⟩ := tableIII_basic hI h ha'Q ha'
  have hcomm_a' : (ρ' : G) * a' = a' * ρ' := by
    have h : a' * (ρ : G) = (ρ : G) * a' := mem_Gx.1 (mem_Gxyz.1 ρ.2).1
    rw [hρ'val]
    exact h.symm
  obtain ⟨hshape, -⟩ := tableIII_five_type h hSGz hρ'5 ha'Q ha'1 ha'z hcomm_a'
  have hcard25 : Nat.card ↥(CbarCent z ρ') = 25 := card_of_isShapeZpTimesZp_five hshape
  have hρH : (ρ' : G) ∈ Gxyz a' z c := by rw [hρ'val]; exact ρ.2
  have hρbar_mem : barOf z ρ' ∈ tableIIIBar z (Gxyz a' z c) :=
    tableIII_barOf_mem_bar ρ' hρH
  have hρbar5 : orderOf (barOf z ρ') = 5 := orderOf_barOf_five hρ'5
  have hr5 : orderOf (⟨barOf z ρ', hρbar_mem⟩ : ↥(tableIIIBar z (Gxyz a' z c))) = 5 := by
    rw [Subgroup.orderOf_mk, hρbar5]
  have hle : tableIIIBar z (Gxyz a' z c) ≤ CbarCent z ρ' := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc' := tableIII_mul_comm_of_card_eq_fifteen hB hr5
      (⟨y, hy⟩ : ↥(tableIIIBar z (Gxyz a' z c)))
    simpa using congrArg Subtype.val hc'
  have hdvd : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ Nat.card ↥(CbarCent z ρ') :=
    Subgroup.card_dvd_of_le hle
  rw [hB, hcard25] at hdvd
  norm_num at hdvd

theorem tableIII_card_stab_4A (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hSGz : StructGzFacts a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z)
    (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 2) :
    Nat.card ↥(Gxyz a' z c) = 2 ^ 7 ∨ Nat.card ↥(Gxyz a' z c) = 2 ^ 7 * 3 ∨
      Nat.card ↥(Gxyz a' z c) = 2 ^ 7 * 5 := by
  have hHGz : Gxyz a' z c ≤ Gx z := by
    intro g hg
    exact (mem_Gxyz.1 hg).2.1
  have hcard := tableIII_card_eq_card_inf_mul_card_bar (K := Gxyz a' z c) hHGz
  have hQcard := tableIII_card_inf_Qz_4A hI h ha'Q ha' hc
  have hHcard : Nat.card ↥(Gxyz a' z c) =
      2 ^ 7 * Nat.card ↥(tableIIIBar z (Gxyz a' z c)) := by
    rw [hcard, hQcard]
  have hdvd : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ 15 :=
    tableIII_card_bar_dvd_4A hI h hSGz hX ha'Q ha' hc
  have hne : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ≠ 15 :=
    tableIII_card_bar_ne_4A hI h hSGz ha'Q ha' hc
  have hcases := t3_eq_one_or_three_or_five_of_dvd_fifteen hdvd hne
  rw [hHcard]
  rcases hcases with h1 | h3 | h5
  · exact Or.inl (by simp [h1])
  · exact Or.inr (Or.inl (by simp [h3]))
  · exact Or.inr (Or.inr (by simp [h5]))

end CFSG.EvenSporadicStandard.HNRecog.Section3
