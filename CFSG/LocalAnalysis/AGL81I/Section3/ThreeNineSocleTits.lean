module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleCore
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeTits
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
import CFSG.GroupTheory.CentralizerMapMulEquiv

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull)

theorem titsThreeOvergroupShape_of_tits
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 3 13) (hK : CFSG.Blueprint.ReeTitsModel ↥K .Tits 2 1)
    (hDK : D ≤ K) : TitsThreeOvergroupShape ↥X₁ ∧ Nat.card ↥X₁ = 11232 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : K.Normal := h.normal
  obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥K 2 1 hK
  have hcardK : Nat.card ↥K = 17971200 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  have hZ : Subgroup.center ↥K = ⊥ := by
    have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ
    rw [CFSG.Sporadic.Schreier.Tits.titsD_center] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have hout : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer ↥K) := by
    intro q hq hq2 hdq
    have : Fact q.Prime := ⟨hq⟩
    have h2 := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier (G := ↥K) (p := 2) (f := 1)
      hK).1
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Outer ↥K) q hdq
    obtain ⟨k, hk⟩ := h2 x
    have h3 : q ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h3))
  have hout13 : ¬ 13 ∣ Nat.card (Outer ↥K) := hout 13 (by norm_num) (by norm_num)
  obtain ⟨hYtop, hm3, hm13, h3Y, h13Y, -⟩ :=
    h.index_facts hZ (hout 3 Nat.prime_three (by norm_num)) hout13
  rw [hcardK] at h3Y h13Y
  have hv3 : (3 : ℕ) ^ (17971200 : ℕ).factorization 3 = 3 ^ 3 :=
    (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 3) (k := 665600)
      (N := 17971200) (by norm_num) (by norm_num)).symm
  rw [hv3] at h3Y
  set Y : Subgroup ↥K := X₁.subgroupOf K with hYdef
  have h3idx : ¬ 3 ∣ Y.index := by
    intro h3
    have := hm3
    unfold Nat.ModEq at this
    omega
  have hdata : TitsThreeOvergroupShape ↥Y :=
    CFSG.StandardType.SylowOvergroup.forall_of_mulEquiv (p := 3) φ
      (fun A _ => TitsThreeOvergroupShape A) (fun A B _ _ f hA => hA.of_mulEquiv f)
      (fun Y hY h3 => titsThreeOvergroupShape_of_not_dvd_index hY h3) Y hYtop h3idx
  have hv13 : (13 : ℕ) ^ (17971200 : ℕ).factorization 13 = 13 ^ 1 :=
    (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 13) (a := 1)
      (k := 1382400) (N := 17971200) (by norm_num) (by norm_num)).symm
  rw [hv13] at h13Y
  have h351 : 351 ∣ Nat.card Y :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 13) h3Y
      (by simpa using h13Y)
  have hidx := Y.card_mul_index
  rw [hcardK] at hidx
  have hYcard : Nat.card Y = 11232 := by
    have hpos : 0 < Nat.card Y := Nat.card_pos
    have hqdiv : 17971200 / Nat.card Y = Y.index := Nat.div_eq_of_eq_mul_right hpos hidx.symm
    have key : ∀ n ∈ Nat.divisors 11232, 351 ∣ n → 17971200 / n ≡ 1 [MOD 3] →
        17971200 / n ≡ 1 [MOD 13] → n = 11232 := by
      decide +kernel
    exact key _ (Nat.mem_divisors.mpr ⟨hdata.1, by norm_num⟩) h351 (by rw [hqdiv]; exact hm3)
      (by rw [hqdiv]; exact hm13)
  have hX₁K : X₁ ≤ K := by
    have h1 := h.lt
    rw [sup_eq_left.mpr hDK] at h1
    exact h1.le
  have eY : ↥Y ≃* ↥X₁ := Subgroup.subgroupOfEquivOfLe hX₁K
  have hX1card : Nat.card ↥X₁ = 11232 := (Nat.card_congr eY.toEquiv).symm.trans hYcard
  exact ⟨hdata.of_mulEquiv eY, hX1card⟩

theorem socle_of_tits
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 3 13) (hK : CFSG.Blueprint.ReeTitsModel ↥K .Tits 2 1)
    (hDK : D ≤ K) :
    IsSimpleGroup ↥(oPPrimeHull 13 X₁) ∧
      Subgroup.centralizer (oPPrimeHull 13 X₁ : Set X) ⊓ K = ⊥ := by
  obtain ⟨hdata, hX1card⟩ := titsThreeOvergroupShape_of_tits h hK hDK
  obtain ⟨M, hMn, hMi, hMs, ⟨eM⟩⟩ := hdata.2 hX1card
  have hMcard : Nat.card ↥M = 5616 := by
    have h1 := M.card_mul_index
    rw [hX1card, hMi] at h1
    omega
  obtain ⟨T₀, hT, hn, hs, ⟨eT⟩, hidx⟩ :=
    SporCent.exists_normal_of_mulEquiv (MulEquiv.refl ↥X₁) M hMn hMs
  have hTcard : Nat.card ↥T₀ = 5616 := by
    rw [Nat.card_congr eT.toEquiv, hMcard]
  have hTprime : ¬ (Nat.card ↥T₀).Prime := by
    rw [hTcard]
    norm_num
  have hdT : 13 ∣ Nat.card ↥T₀ := by
    rw [hTcard]
    norm_num
  have hidx2 : (T₀.subgroupOf X₁).index = 2 := hidx.trans hMi
  refine socle_of_index_two h hDK hT hn hs hTprime hdT hidx2 ?_
  obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥K 2 1 hK
  intro z hz hdvd
  have hzφ : orderOf (φ z) = 2 := (MulEquiv.orderOf_eq φ z).trans hz
  rw [hTcard, CFSG.GroupTheory.card_centralizer_singleton_mulEquiv φ z] at hdvd
  rcases CFSG.RankThree.PartTwo.Sec4.Item434RemTits.card_centralizer_of_involution hzφ with
    h | h
  · rw [h] at hdvd
    norm_num at hdvd
  · rw [h] at hdvd
    norm_num at hdvd

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
