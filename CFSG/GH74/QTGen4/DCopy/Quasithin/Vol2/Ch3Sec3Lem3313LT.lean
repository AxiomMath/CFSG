module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Stmt3313LT
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313
public import CFSG.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313He

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)

theorem stmt3_3_13LT_of_F4 (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h10 : Stmt3_3_10)
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hFa : Vol2.Ch10.SecB.FactL33M11)
    (hFc : Vol2.Ch10.SecB.FactL4L5) (hAut : FactAutL45Sylow) (hHe : FactAutHeSylow)
    (hB : Step3_3_13Bender) (hObl : Obl3_3_13LT_F4) : Stmt3_3_13LT_F4 := by
  intro G _ _ T M L D H h hH hHLT ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  have hTH : T ≤ H := hH.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow hTH⟩
  set φ := oTwoQuotEquiv e with hφ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  suffices hDY : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) by
    intro d hd
    rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hTsyl]
    refine A38.map_conj_eq_iff.mp ?_
    rw [Subgroup.map_sup, A38.map_conj_eq_iff.mpr (hDY hd), A38.map_conj_eq_iff.mpr (h.DN hd)]
  by_contra hDY
  have hO : pCoreOf 2 (H ⊔ D) ≠ ⊥ :=
    (h10 G T M L D h).1 H hH ⟨T, Lem3313.maxOver_eq_of_iso hTsyl φ⟩
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hTH.trans le_sup_left)⟩
  have hXi := Der6D.xi_of_iso hTsyl hH.2 φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ pCoreOf 2 (oTwoUpper H) := fun x hx => by
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx 3, C1Pack12.pow_three_mem_pCoreOf φ hx⟩
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  rcases h134 G (H ⊔ D) T (oTwoUpper H) P3 (hKc _ hO) hO hT₀ (hYH.trans le_sup_left) hXi hrel
      hP3.le hP3.isPGroup hP3card with hN | ⟨K, hK, hKq, hYK', hcases⟩
  · exact hDY (le_sup_right.trans hN)
  have hHN : H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKc h37 h38 hO hT₀ hK
  rcases hcases with ⟨⟨t, ⟨htT, -⟩, htn, -, -⟩, htype⟩ | ⟨hTL, htype⟩ | ⟨-, -, hcyc⟩ |
      ⟨hTL, htype⟩ | ⟨hHK, he⟩
  ·
    have hTK : ¬ T ≤ Subgroup.normalizer (K : Set G) := fun hle => htn (hle htT)
    rcases htype with hn | hq
    · exact hDY (hB G T M L D H K h hH ⟨e⟩ hO hK hKq hYK' hTK hn)
    · exact hDY (hObl G T M L D H K h hH hHLT ⟨e⟩ hO hK hKq hYK' hTK hq)
  ·
    have hYK : oTwoUpper H ≤ K := hYK'.trans (Vol2.Ch10.SecB.conjClosure_eq_self hTL).le
    obtain ⟨s, hs, x, hx, hne⟩ := Vol2.Ch10.SecB.exists_pow_four_not_mem hFa hT₀ hK (by
      rcases htype with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)) hYK hXi.1 hXi.2.1 hpow3 hrel
    exact hne (Lem3313.pow_four_comm_mem_of_iso hTsyl φ hs hx)
  ·
    exact Der6D.not_autCyclic h.sylow hTsyl φ hXi hP3 hP3card hcyc
  ·
    have hYK : oTwoUpper H ≤ K := hYK'.trans (Vol2.Ch10.SecB.conjClosure_eq_self hTL).le
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
      have h1 := le_sup_right.trans hHN
      rwa [Vol2.Ch10.SecB.conjClosure_eq_self hTL] at h1
    rcases htype with hM | hk | hk
    · obtain ⟨s, hs, x, hx, hne⟩ := Vol2.Ch10.SecB.exists_pow_four_not_mem hFa hT₀ hK
        (Or.inr (Or.inr hM)) hYK hXi.1 hXi.2.1 hpow3 hrel
      exact hne (Lem3313.pow_four_comm_mem_of_iso hTsyl φ hs hx)
    · exact hDY (Lem3313.le_normalizer_of_lk2 hFc hAut h.sylow hTsyl φ hH.2 hK hTL hDK h.DN
        h.Dodd hYK (Or.inl rfl) hk)
    · exact hDY (Lem3313.le_normalizer_of_lk2 hFc hAut h.sylow hTsyl φ hH.2 hK hTL hDK h.DN
        h.Dodd hYK (Or.inr rfl) hk)
  ·
    have hTL : T ≤ Subgroup.normalizer (K : Set G) := (hTH.trans le_sup_left).trans hHK
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := le_sup_right.trans hHK
    have hYK : oTwoUpper H ≤ K := hYK'.trans (Vol2.Ch10.SecB.conjClosure_eq_self hTL).le
    exact hDY (Lem3313.le_normalizer_of_he hHe h.sylow hTsyl hTL hDK h.DN h.Dodd hYK he)

end CFSG.Quasithin.H13
