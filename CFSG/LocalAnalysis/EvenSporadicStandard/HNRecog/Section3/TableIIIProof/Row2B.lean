module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.BarX
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Row2BOdd

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableIII_card_inf_Qz_dvd_2B (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hF2 : Vert Fusion2Facts a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z)
    (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 1) :
    Nat.card ↥(Gxyz a' z c ⊓ Qz z) ∣ 2 ^ 7 := by
  obtain ⟨-, ha'1, ha'z, -, -, -, -, -⟩ := tableIII_basic hI h ha'Q ha'
  have hW : Nat.card ↥(Qz z ⊓ Gx a') = 2 ^ 8 := tableIII_card_Qz_inf_Gx h ha'Q ha'1 ha'z
  have hHW : Gxyz a' z c ⊓ Qz z ≤ Qz z ⊓ Gx a' := by
    intro g hg
    obtain ⟨hgH, hgQ⟩ := Subgroup.mem_inf.mp hg
    exact Subgroup.mem_inf.mpr ⟨hgQ, (mem_Gxyz.mp hgH).1⟩
  have hne : Gxyz a' z c ⊓ Qz z ≠ Qz z ⊓ Gx a' := by
    intro heq
    have hcenter : c ∈ centerOf (derivedOf (Gxy a' z)) := by
      rw [hX.center.1]
      simp only [centerOf, Subgroup.mem_inf]
      refine ⟨tableIII_mem_pCore_2B hI h hF2 hX ha'Q ha' hc, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro w hw
      have hw1 : w ∈ derivedOf (Gxy a' z) ⊓ Qz z := by
        simpa [hX.pCore_derived.1] using hw
      obtain ⟨hwD, hwQ⟩ := Subgroup.mem_inf.mp hw1
      have hwX : w ∈ Gxy a' z := derivedOf_le _ hwD
      have hwW : w ∈ Qz z ⊓ Gx a' := Subgroup.mem_inf.mpr ⟨hwQ, (mem_Gxy.mp hwX).1⟩
      have hwH : w ∈ Gxyz a' z c ⊓ Qz z := by rw [heq]; exact hwW
      exact (mem_Gx.mp ((mem_Gxyz.mp (Subgroup.mem_inf.mp hwH).1).2.2)).symm
    exact tableIII_not_mem_center_2B hI h hF2 hX ha'Q ha' hc hcenter
  have hdiv : Nat.card ↥(Gxyz a' z c ⊓ Qz z) ∣ 2 ^ 8 := by
    have h1 := Subgroup.card_dvd_of_le hHW
    rwa [hW] at h1
  have hne8 : Nat.card ↥(Gxyz a' z c ⊓ Qz z) ≠ 2 ^ 8 := by
    intro h8
    refine hne (Subgroup.eq_of_le_of_card_ge hHW ?_)
    exact le_of_eq (by rw [h8, hW])
  obtain ⟨k, hk8, hkn⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdiv
  have hkne : k ≠ 8 := by
    intro hk
    exact hne8 (by rw [hkn, hk])
  have hk7 : k ≤ 7 := by omega
  rw [hkn]
  exact pow_dvd_pow 2 hk7

theorem tableIII_card_stab_2B (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hF2 : Vert Fusion2Facts a z) (hSGz : StructGzFacts a z)
    (hX : XStruct a z a') (ha'Q : a' ∈ Qz z) (ha' : IsConj a a')
    (hc : c ∈ tab3Set a z a' 1) :
    Nat.card ↥(Gxyz a' z c) ∣ 2 ^ 10 := by
  have hHle : Gxyz a' z c ≤ Gx z := fun g hg => (mem_Gxyz.mp hg).2.1
  have hHleX : Gxyz a' z c ≤ Gxy a' z := fun g hg =>
    mem_Gxy.mpr ⟨(mem_Gxyz.mp hg).1, (mem_Gxyz.mp hg).2.1⟩
  have hcard := tableIII_card_eq_card_inf_mul_card_bar hHle
  have hBdiv : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ 120 := by
    have hle : tableIIIBar z (Gxyz a' z c) ≤ tableIIIBar z (Gxy a' z) :=
      tableIII_bar_mono hHleX
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [tableIII_card_bar_Gxy hI h hX ha'Q ha'] at h1
  have hBdvdH : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ Nat.card ↥(Gxyz a' z c) :=
    ⟨Nat.card ↥(Gxyz a' z c ⊓ Qz z), by rw [hcard, mul_comm]⟩
  have hno3 : ¬ 3 ∣ Nat.card ↥(Gxyz a' z c) := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Gxyz a' z c)) 3 h3
    exact tableIII_orderOf_ne_three_2B hI h hF2 hX ha'Q ha' hc g.2
      (by rw [Subgroup.orderOf_coe, hg])
  have hno5 : ¬ 5 ∣ Nat.card ↥(Gxyz a' z c) := by
    intro h5
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Gxyz a' z c)) 5 h5
    exact tableIII_orderOf_ne_five_2B hI h hSGz ha'Q ha' hc g.2
      (by rw [Subgroup.orderOf_coe, hg])
  have hno3B : ¬ 3 ∣ Nat.card ↥(tableIIIBar z (Gxyz a' z c)) :=
    fun h => hno3 (h.trans hBdvdH)
  have hno5B : ¬ 5 ∣ Nat.card ↥(tableIIIBar z (Gxyz a' z c)) :=
    fun h => hno5 (h.trans hBdvdH)
  have hcop : Nat.Coprime (Nat.card ↥(tableIIIBar z (Gxyz a' z c))) 15 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.coprime_mul_iff_right]
    refine ⟨?_, ?_⟩
    · exact ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mpr hno3B).symm
    · exact ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hno5B).symm
  have hB8 : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ 8 := by
    have h15 : Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣ 8 * 15 := by
      rwa [show (120 : ℕ) = 8 * 15 by norm_num] at hBdiv
    exact hcop.dvd_of_dvd_mul_right h15
  have hinf : Nat.card ↥(Gxyz a' z c ⊓ Qz z) ∣ 2 ^ 7 :=
    tableIII_card_inf_Qz_dvd_2B hI h hF2 hX ha'Q ha' hc
  rw [hcard]
  have hmul : Nat.card ↥(Gxyz a' z c ⊓ Qz z) * Nat.card ↥(tableIIIBar z (Gxyz a' z c)) ∣
      2 ^ 7 * 8 := Nat.mul_dvd_mul hinf hB8
  have hpow : 2 ^ 7 * 8 = 2 ^ 10 := by norm_num
  rwa [hpow] at hmul

end CFSG.EvenSporadicStandard.HNRecog.Section3
