module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.H13.U3Local
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Star
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13.L34
  CFSG.Quasithin.H13.Lem8

theorem stmt12_2_8_of_inputs_F4
    (h1222 : Stmt12_2_2_F4) (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) : Stmt12_2_8_F4 := by
  intro G _ _ T L V hH
  rcases rankTwoFacts_or_small_F4 h1222 hH with hsmall | hR
  · exact Or.inr (Or.inl hsmall)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := Subgroup.normalizer (L : Set G) with hMdef
  have hLM : L ≤ M := Subgroup.le_normalizer

  have hLn : (L.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  have hsub : IsSubnormal L M := A3.subnormal_of_normal hLM hLn
  have hO2M : pCoreOf 2 M ≠ ⊥ := fun h => U3.pCoreOf_ne_bot_of_isFaithfulLocal hH.faithful
    (le_bot_iff.mp (h ▸ pCoreOf_le_pCoreOf_of_isSubnormal hsub))
  have hsqtk : SQTKGroup ↥M := sqtkGroup_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hO2M
  have hhyp := sqtkHyp_quotient_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hO2M

  set L' : Subgroup ↥M := L.subgroupOf M with hL'
  have hcc : L ∈ cComp (L ⊔ T) := hH.faithful.1.2.1
  have hcomp : L' ∈ cComp (⊤ : Subgroup ↥M) :=
    subgroupOf_mem_cComp (cComp_mem_of_subnormal hsub (cComp_mem_of_le hcc le_rfl le_sup_left))
  let eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLM
  let eQ : ↥L' ⧸ CFSG.pCore 2 ↥L' ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
    QuotientGroup.congr _ _ eL (CFSG.pCore_map_iso 2 eL)
  have hQ' : CFSG.IsQuasisimple (↥L' ⧸ CFSG.pCore 2 ↥L') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hH.quasisimple

  have h2L : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hrank : 1 < CFSG.Open.pRank 3 L' := by
    rw [← pRank_top_subtype L', CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eL,
      ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) h2L]
    exact hR.rank

  have hZQ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∣ 3 := by
    rcases hR.center with h | ⟨-, -, -, h, -⟩
    · rw [h, Subgroup.card_bot]
      exact one_dvd 3
    · rw [h]
  obtain ⟨g3, hg3⟩ := exists_orderOf_eq_three_of_two_le_pRank (le_trans (by norm_num) hR.rank)
  obtain ⟨eS⟩ := nonempty_mulEquiv_starImage L' hQ'
    (by rw [card_center_eq_of_mulEquiv eQ]; exact hZQ)
    ⟨eQ.symm g3, by rw [MulEquiv.orderOf_eq]; exact hg3⟩
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(starImage 3 L') := eQ.symm.trans eS
  have hX : ListOrd (Nat.card ↥(starImage 3 L')) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hR.card
  have hX8 : Nat.card ↥(starImage 3 L') = 20160 →
      Nonempty (↥(starImage 3 L') ≃* alternatingGroup (Fin 8)) := fun h => by
    obtain ⟨e8⟩ := hR.a8 (by rw [Nat.card_congr e.toEquiv]; exact h)
    exact ⟨e.symm.trans e8⟩
  have hZX : Nat.card (Subgroup.center ↥(starImage 3 L')) = 3 →
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≠ ⊥ := fun h hb => by
    rw [← card_center_eq_of_mulEquiv e, hb, Subgroup.card_bot] at h
    omega
  have hXhat : Nat.card (Subgroup.center ↥(starImage 3 L')) = 3 →
      Nat.card ↥(starImage 3 L') = 1080 ∨ Nat.card ↥(starImage 3 L') = 7560 := fun h => by
    rw [← Nat.card_congr e.toEquiv]
    exact hR.hat (hZX h)

  rcases a318 hF hsqtk (h36 _ hhyp) (h38 _ hhyp) hcomp hQ' Nat.prime_three (by norm_num) hrank
    with h1 | ⟨-, s, q, hq, hpsl, -⟩ | ⟨-, h3g, h3⟩
  ·
    left
    have := eq_closure_image_of_subgroupOf_eq hLM h1
    rw [image_pElements_three] at this
    exact this.symm
  · exact (not_isPSLEps3q_of_card hX hX8 s q hq hpsl).elim
  · have hZ3 : Nat.card (Subgroup.center ↥(starImage 3 L')) = 3 := by
      rcases h3g with ⟨s, q, hq, hsl⟩ | hA | hA | hM22
      · exact (not_isSLEps3_of_card hX s q hq hsl).elim
      · exact hA.2.1
      · exact hA.2.1
      · exact (not_isHat_M22 hX hM22).elim
    rcases h3 with hθ | ⟨s, q, x, hsl, -⟩
    · refine Or.inr (Or.inr ⟨hR.center.resolve_left (hZX hZ3), ?_⟩)
      have := eq_closure_image_of_subgroupOf_eq hLM hθ
      rwa [image_orderThree] at this
    · exact (not_isSLEps3_of_card_hat (hXhat hZ3) s q hsl).elim

end CFSG.Quasithin.H13
