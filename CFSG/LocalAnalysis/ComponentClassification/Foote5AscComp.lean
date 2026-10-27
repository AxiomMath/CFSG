module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseOne
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ProperTwoGeneratedCore

variable {X : Type} [Group X] [Finite X]

theorem exists_lever {L : Subgroup X} [hLn : L.Normal] (P : Sylow 2 X) {a : X} (haL : a ∈ L)
    (ha : orderOf a = 2) :
    ∃ z ∈ (P : Subgroup X), (∀ p ∈ (P : Subgroup X), Commute p z) ∧ z ∈ L ∧ orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ :=
    Assembly.exists_conj_mem_sylow P (Assembly.isPGroup_zpowers_of_orderOf_eq_two ha)
  have haP : g⁻¹ * a * g ∈ (P : Subgroup X) := hg a (mem_zpowers a)
  have haL' : g⁻¹ * a * g ∈ L := by simpa using hLn.conj_mem a haL g⁻¹
  have ha1 : g⁻¹ * a * g ≠ 1 := by
    intro h
    have h2 : a = 1 := by
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [h2, orderOf_one] at ha
    omega
  have hN : (L.subgroupOf (P : Subgroup X)).Normal := hLn.subgroupOf _
  have hNne : L.subgroupOf (P : Subgroup X) ≠ ⊥ := by
    intro h
    have hmem : (⟨g⁻¹ * a * g, haP⟩ : (P : Subgroup X)) ∈ L.subgroupOf (P : Subgroup X) := haL'
    rw [h, mem_bot] at hmem
    exact ha1 (congrArg Subtype.val hmem)
  have : Group.IsNilpotent (P : Subgroup X) := P.isPGroup'.isNilpotent
  have hM := Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
  set M := L.subgroupOf (P : Subgroup X) ⊓ center (P : Subgroup X) with hMdef
  have hM2 : IsPGroup 2 M := P.isPGroup'.to_subgroup M
  obtain ⟨n, hn⟩ := hM2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hM ((Subgroup.card_eq_one).mp hn)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  refine ⟨((w : (P : Subgroup X)) : X), (w : (P : Subgroup X)).2, fun p hp => ?_, w.2.1, ?_⟩
  · exact congrArg Subtype.val (mem_center_iff.mp w.2.2 ⟨p, hp⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]

theorem component_bender_of_not_mem (hodd : pPrimeCore 2 X = ⊥) {u : X}
    (huZ : u ∈ center X) (hu : orderOf u = 2) (huO : u ∈ CFSG.pCore 2 X)
    (hrk : Open.pRank 2 (CFSG.pCore 2 X) = 1) (h3 : 3 ≤ Open.twoRank X) (P : Sylow 2 X)
    {Y : Subgroup X} (hY : Y ≠ ⊤) (hPY : (P : Subgroup X) ≤ Y)
    (hcore : Open.properTwoGenCoreGamma (P : Subgroup X) 2 ≤ Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (huL : u ∉ L) :
    L.Normal ∧ Open.fusionIsBenderGroup L ∧ Open.pRank 2 (centralizer (L : Set X)) ≤ 1 ∧
      ∀ x : X, orderOf x = 2 → x ∈ L ⊔ centralizer (L : Set X) := by
  have hL2 := Assembly.component_two_le_pRank_of_not_mem hodd huZ hu huO hrk hL huL
  have hchar : L.Characteristic := proper_full_core_high_rank_component_characteristic P Y hY
    hPY hcore L ((CFSG.isComponent_iff_open L).mp hL) hL2
  have hLn : L.Normal := inferInstance
  obtain ⟨a, haL, -, -, ha2, -⟩ := Assembly.exists_commuting_involutions_of_two_le_pRank hL2
  obtain ⟨z, hzP, hzc, hzL, hz2⟩ := exists_lever P haL ha2
  have hc : TheoremC.CoreConfig Y u z :=
    ⟨hodd, huZ, hu, hY, ⟨P, hPY, hcore, hzP, hzc⟩, h3, hz2, fun h => huL (h ▸ hzL)⟩
  have hBen : Open.fusionIsBenderGroup L :=
    Open.fusionIsBenderGroup_of_isSimpleBenderGroup (BenderSuzuki.theorem_SE_simple _
      (hc.component_isStronglyEmbedded hL huL) (hc.component_isSimpleGroup hL huL))
  refine ⟨hLn, hBen, hc.component_centralizer_pRank_le_one hL huL, fun x hx => ?_⟩
  rcases hc.involution_mem_component_or hL huL hx with h | h
  · exact mem_sup_left h
  · rw [show x = u⁻¹ * (u * x) by group]
    exact mul_mem (mem_sup_right (inv_mem (hc.center_mem_centralizer _))) (mem_sup_left h)

end CFSG.ComponentClassification.Foote5
