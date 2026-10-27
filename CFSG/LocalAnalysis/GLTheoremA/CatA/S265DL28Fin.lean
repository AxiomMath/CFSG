module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28T171
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open scoped commutatorElement

section Fin

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_big_E_of_extremal {S : Subgroup Ω} {x : Ω} (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxc : ∀ g : Ω, g * x = x * g)
    (hext : S171.ExtremalType 3 S) :
    ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ E ≤ S ⊔ Subgroup.zpowers x ∧ 3 ^ 5 ≤ Nat.card E := by
  obtain ⟨-, n, hn, hcase⟩ := hext
  have hrank := S171.I171ExtremalRankFact_holds Ω S hSq n hn
  rcases hcase with hU6 | hTE6
  · obtain ⟨E₀, hE₀S, hE₀, hE₀c⟩ := hrank.1 hU6
    exact exists_big_elem_abelian hE₀S hE₀ hx3 hx1 hxc hE₀c
  · obtain ⟨E₀, hE₀S, hE₀, hE₀c⟩ := hrank.2 hTE6
    refine exists_big_elem_abelian hE₀S hE₀ hx3 hx1 hxc ?_
    calc 3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω))
        ≤ 3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ Nat.card E₀ := hE₀c

theorem qsFamDL28_of_t171 (hShape : T171.T171ShapeFact) (hNoAct : T171.T171NoActFact) :
    QSFamDL28 := by
  intro p Ω _ _ S B T x D K h hp3 hL
  subst hp3
  exfalso
  have cfg := h.cfg
  have hBle : Nat.card B ≤ 3 ^ 4 := card_B_le_of_l28 h hL
  obtain ⟨hDB, -, hDcard, -, -, hKcomp, -⟩ := cfg.std
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKc : GLAPComponent 3 (S ⊓ cs D) K := (h.nlAct (three_dvd_card_of_l28 hL)).comp
  have hChev : IsChevSimple 2 (PSimple 3 K) := s265d_chevSimple_of_l28 hL
  obtain ⟨β, hβB, hβN, hβD, hβni⟩ := exists_noninner_of_l28 h hL
  have hβ3 : β ^ 3 = 1 := cfg.elem.2 β hβB
  have hni : ¬ InnDiagOn 3 (Subgroup.zpowers β) K := l28_not_innDiagOn hKc hKq hL hβN hβ3 hβni
  have hCfg := cfg_of_qsnl h
  have hMax := maxG_of_qsnl h
  have hext := hShape 3 Ω B x S D K β cfg.kgroup hCfg hMax cfg.normal cfg.std hKc hChev hβB hβD hni
  obtain ⟨E, hEel, hEle, hE5⟩ :=
    exists_big_E_of_extremal cfg.quasi (cfg.elem.2 x cfg.xB) cfg.x1 cfg.xcen hext
  rcases cfg.maxc with hmax | ⟨hmaxE, -⟩
  · by_cases hcomm : ∀ t ∈ T, ∀ b ∈ B, ⁅t, b⁆ ∈ centModSubgroup 3 S
    · exact s265d_false_of_central_commutators h hBle hEel hEle hE5 hmax hcomm
    · push Not at hcomm
      obtain ⟨t, ht, b, hb, hnc⟩ := hcomm
      have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
        (Subgroup.normalizer_eq_top_iff.2 cfg.normal) ▸ Subgroup.mem_top g
      have hTB := hNoAct 3 Ω B x S D K β cfg.kgroup hCfg hMax cfg.normal cfg.std hKc hChev hβB hβD
        hni hext T (fun g _ => hSN g)
        (fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen g)) cfg.two cfg.bnorm
      have hc : ⁅t, b⁆ ∈ Subgroup.centralizer (S : Set Ω) := hTB (Subgroup.commutator_mem_commutator ht hb)
      exact hnc (centMod_iff.1 (centMod_of_mem_centralizer hc))
  · have := hmaxE E hEel
    omega

end Fin

end CFSG.LocalAnalysis.GLTheoremA.S265D

end
