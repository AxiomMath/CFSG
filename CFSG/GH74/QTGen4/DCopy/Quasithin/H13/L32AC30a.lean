module

public import CFSG.Quasithin.H13.L32AC30a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Ambient

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V H : Subgroup G}

theorem isQuasisimple_cStar_F4 (h36 : A36ForSQTK) (h28 : Lemma14_7_28_F4) (S : Setting147 G T L V H)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G}
    (hK : K ∈ cComp H) : CFSG.IsQuasisimple (cStar K) := by
  have h := S.hyp
  have hpc : pCoreOf 2 H ≠ ⊥ := S.hz.1.2
  have hA := CFSG.Quasithin.lemma_1_2_1_four_strong h.fsu.qtke h.fsu.simple h.fsu.nonabelian
    h36 hpc hK
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  let e' : cStar K ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
    QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq_pCore K)
  have key : CFSG.IsQuasisimple ↥(modO2Image H K) → CFSG.IsQuasisimple (cStar K) := fun hq =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e'.trans e).symm hq
  have hcase : A36Case3 ↥(modO2Image H K) ∨ A36Case4 ↥(modO2Image H K) → False := by
    intro hc
    obtain ⟨hF0, hF6⟩ := fitting_ne_bot_coprime_six hc
    set Kb := modO2Image H K with hKb
    set F := CFSG.fittingSubgroup ↥Kb with hF
    have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
    have hFn : ((F.map Kb.subtype).subgroupOf Kb).Normal := by
      rw [map_subtype_subgroupOf']
      infer_instance
    have hFs : (F.map Kb.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le F) hKbs hFn
    have hcard : Nat.card (F.map Kb.subtype) = Nat.card F :=
      Subgroup.card_map_of_injective Kb.subtype_injective
    have hodd : Odd (Nat.card (F.map Kb.subtype)) := by
      rw [hcard]
      exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num) hF6)
    have hle := le_oddCore_of_isSubnormal hFs hodd
    have hone : Nat.card (F.map Kb.subtype) = 1 := by
      rcases h28 G T L V H S with h0 | h1
      · rw [h0, le_bot_iff] at hle
        rw [hle, Subgroup.card_bot]
      · rw [h1] at hle
        have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
        have hoddL : Odd (Nat.card (modO2Image H (l1 T L V))) := h1 ▸ odd_card_oddCore
        have hd : Nat.card (F.map Kb.subtype) ∣ 3 :=
          (Subgroup.card_dvd_of_le hle).trans (card_modO2Image_dvd_three hL1H hL3 hoddL)
        rw [hcard] at hd ⊢
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right (by norm_num) hF6) hd
    rw [hcard, Subgroup.card_eq_one] at hone
    exact hF0 hone
  rcases hA.1 with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
  · exact key hc.1
  · exact key hc.1
  · exact (hcase (Or.inl h3)).elim
  · exact (hcase (Or.inr h4)).elim

end Ambient

end CFSG.Quasithin.H13.L32A.C
