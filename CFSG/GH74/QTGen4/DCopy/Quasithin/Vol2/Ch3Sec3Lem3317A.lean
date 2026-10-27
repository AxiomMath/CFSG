module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317A

public section
namespace CFSG.Quasithin.H13.L3317

open CFSG.RankThree.PerfectCover
open CFSG.Open (pCoreOf)

section Cases

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem alt7_cases_F4 (h8 : Stmt3_3_8) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14_F4)
    (h : Hyp331 G T M L D) (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      AlternatingNatural (autOn L (vPlus L T)) (commVPlus L T L) ⊥ 7 ∨
        Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4 := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hc7 : Nat.card ↥(autOn L (vPlus L T)) = 2520 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H.A7.card_A7]
  obtain ⟨hab, hc⟩ := h8 G T M L D h
  refine ⟨hab, ?_⟩
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    obtain ⟨t, ht, htN, -⟩ := h1
    exact absurd (hTL ht) htN
  ·
    obtain ⟨n, -, hn, -⟩ := h2
    exact absurd hn ((h10 G T M L D h).2.1 n)
  ·
    rcases h3 with ⟨⟨e5⟩, -⟩ | ⟨-, hnat⟩
    · rw [hML] at e5
      have := Nat.card_congr e5.toEquiv
      rw [hc7, card_alt_five] at this
      norm_num at this
    · rw [hML] at hnat
      exact Or.inl hnat
  ·
    exfalso
    rcases h4 with ⟨n, K, _, _, hK, ⟨eK⟩, -⟩ | ⟨n, K, _, _, hn, hK, ⟨eK⟩, -⟩ | ⟨⟨e6⟩, -⟩ |
      ⟨n, K, _, _, hK, ⟨eK⟩, -⟩
    · rw [hML] at eK
      have hcK := Nat.card_congr eK.toEquiv
      rw [hc7, L3316.card_sl3 hK] at hcK
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · norm_num at hcK
      · have := L3316.sl3_ge hn
        omega
    · rw [hML] at eK
      have hcK := Nat.card_congr eK.toEquiv
      rw [hc7, L3316.card_sp4 hK] at hcK
      have := L3316.sp4_ge hn
      omega
    · rw [hML] at e6
      have := Nat.card_congr e6.toEquiv
      rw [hc7, card_alt_six] at this
      norm_num at this
    · rw [hML] at eK
      have hcK := Nat.card_congr eK.toEquiv
      rw [hc7] at hcK
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · have hd : Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ ∣ Nat.card ↥(quasithinG2 K) :=
            Subgroup.card_dvd_of_le (Subgroup.commutator_le.2 fun a ha b hb => by
              rw [commutatorElement_def]
              exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
                ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb))
          rw [← hcK, L3316.card_g2 le_rfl hK] at hd
          norm_num at hd
      · rw [Obs3324.commutator_quasithinG2_eq hn hK, L3316.card_g2 (by omega) hK] at hcK
        have := L3316.g2_ge hn
        omega
  ·
    obtain ⟨-, hc4⟩ := h5
    rw [hML] at hc4
    exact Or.inr hc4
  ·
    exfalso
    obtain ⟨-, hZ, -⟩ := h6
    rw [hML] at hZ
    have : IsSimpleGroup ↥(autOn L (vPlus L T)) := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autOn L (vPlus L T)))
      with hb | ht
    · rw [hb, Subgroup.card_bot] at hZ
      norm_num at hZ
    · apply CFSG.Quasithin.H.A7.not_comm_A7
      intro σ τ
      have hσ := (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top (e.symm σ)) (e.symm τ))
      apply e.symm.injective
      rw [map_mul, map_mul, hσ]
  ·
    exfalso
    obtain ⟨n, hn, ⟨eS⟩, -⟩ := h7
    rw [hML] at eS
    have hcS := Nat.card_congr eS.toEquiv
    rw [hc7] at hcS
    rcases hn with rfl | rfl
    · rw [CFSG.QuasithinUnique.Bridge.card_sl4] at hcS
      norm_num at hcS
    · rw [CFSG.QuasithinUnique.Bridge.card_sl5] at hcS
      norm_num at hcS

end Cases

end CFSG.Quasithin.H13.L3317
