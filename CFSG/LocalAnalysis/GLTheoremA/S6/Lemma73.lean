module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxN11

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure Lemma73Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i183 : Input18_3_4
  i112 : I112StarAt G p
  altNotWeakExc : AltNotWeakExcAt
  i2013 : I2013At
  i203 : I203At
  i1415Nine : I1415NineAt G
  i1415Seven : I1415SevenAt G
  i1422 : I1422At G
  i2014 : I2014At G
  i2017 : I2017At G
  i1016Co : I1016CoAt G
  kLevel : KLevelAltAt
  i182 : I182At G
  i2prod : I2ProdAt G
  i106L62 : I106L62At G
  i71L62 : I71L62At G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma73_holds (hc : S6Ctx G p) (hin : Lemma73Inputs G p) (h72 : Lemma72At G p) :
    Lemma73At G p := by
  intro B x L n y J hB S
  obtain ⟨hp3, hn9, hn12⟩ := h72 B x L n y J hB S
  subst hp3
  by_cases hn12' : n = 12
  · exfalso
    subst hn12'
    obtain ⟨T, I, a, K, Sg, C⟩ := l73_ctx hc hin.i183 hB S le_rfl (fun h => absurd h (by omega))
    exact l73_n12 hc hin.i183 hin.i112 hin.altNotWeakExc hin.i2013 hin.i203 hin.i1415Nine hin.i2014
      hin.i1016Co hB S C
  · have hn11 : n ≤ 11 := by omega
    obtain ⟨y', J', hy'B, S'⟩ := l73_rechoose hc hB S hn11
    by_cases hn9' : n = 9
    · exfalso
      subst hn9'
      exact l73_n9 hc hin.i203 hB S'
    · have hn1011 : n = 10 ∨ n = 11 := by omega
      obtain ⟨T, I, a, K, Sg, C⟩ := l73_ctx hc hin.i183 hB S' hn12 (fun _ => hy'B)
      rcases hn1011 with rfl | rfl
      · exfalso
        exact l73_n10 hc hin.i183 hin.i2013 hin.i1415Seven hin.kLevel hin.i2prod hB S' hy'B C
      · have F := l73_n11 hc hin.i183 hin.i112 hin.altNotWeakExc hin.i1422 hin.i2017 hin.i182
          hin.i106L62 hin.i71L62 hB S' hy'B C
        refine ⟨⟨rfl, l73_card_B hc hB S' le_rfl, rfl⟩, y', J', hy'B, S', a, K, T, I, Sg, ?_⟩
        exact
          { a_mem := C.a_mem
            a_ne_one := C.a_ne
            K_comp := F.K_comp
            K_eq := C.K_eq
            K_type := F.K_type
            B_eq_K := F.B_eq_K
            T_le := C.ti.T_le
            T_two := C.ti.T_two
            T_not_le := C.ti.T_not_le
            B_le_N := C.ti.B_le_N (Or.inr rfl)
            covers := C.ti.covers
            I_eq := C.ti.I_eq
            I_le_J := C.ti.I_le_J
            I_alt := by simpa using C.ti.I_alt
            comm_T := C.ti.comm_T
            S_eq := C.S_eq
            S_ne := C.S_ne
            S_le_K := C.S_le_K
            S_not_le := F.S_not_le
            J_alt8 := F.J8
            I_alt7 := F.I7 }

end CFSG.LocalAnalysis.GLTheoremA
