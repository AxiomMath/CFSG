module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28T171
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGU38Act
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSetup
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Mark
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Size
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Frame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

private theorem exists_big_elem_abelian_pow {Ω : Type} [Group Ω] [Finite Ω] {S E₀ : Subgroup Ω}
    {x : Ω} (k : ℕ) (hE₀S : E₀ ≤ S) (hE₀ : IsElemAbelian 3 E₀) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxc : ∀ g : Ω, g * x = x * g)
    (hE : 3 ^ k * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) ≤ Nat.card E₀) :
    ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ E ≤ S ⊔ Subgroup.zpowers x ∧
      3 ^ (k + 1) ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCz : Subgroup.zpowers x ≤ Subgroup.center Ω :=
    Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 hxc)
  have hCN : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set Ω) :=
    hCz.trans (Subgroup.center_le_normalizer _)
  have hCS : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) :=
    hCz.trans (Subgroup.center_le_centralizer _)
  have hC3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := fun a _ b hb =>
    Subgroup.mem_center_iff.1 (hCz hb) a
  refine ⟨E₀ ⊔ Subgroup.zpowers x,
    IsElemAbelian.sup_of_commute hE₀ (isElemAbelian_zpowers hx3) hcomm,
    sup_le_sup_right hE₀S _, ?_⟩
  have h2 := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hC3] at h2
  have h3 : Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E₀ hCS)
  have hz : 0 < Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := Nat.card_pos
  have h4 : 3 ^ (k + 1) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
    calc 3 ^ (k + 1) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)
        = 3 * (3 ^ k * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)) := by ring
      _ ≤ 3 * (3 ^ k * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ 3 * Nat.card E₀ := Nat.mul_le_mul_left _ hE
      _ = Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
        rw [h2, mul_comm]
  exact Nat.le_of_mul_le_mul_right h4 hz

private theorem false_of_central_commutators_lt {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) {E : Subgroup Ω}
    (hEel : IsElemAbelian 3 E) (hEle : E ≤ S ⊔ Subgroup.zpowers x)
    (hlt : Nat.card B < Nat.card E) (hmax : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hcomm : ∀ t ∈ T, ∀ b ∈ B, ⁅t, b⁆ ∈ centModSubgroup 3 S) : False := by
  have cfg := h.cfg
  have hTB : (⁅T, B⁆ : Subgroup Ω) ≤ T := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    have hb' := (Subgroup.mem_normalizer_iff.1 (cfg.bnorm hb) t⁻¹).1 (T.inv_mem ht)
    rw [commutatorElement_def]
    have : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
    rw [this]
    exact T.mul_mem ht hb'
  have hTB2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) := cfg.two.to_le hTB
  have hTBc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (S267.ModelGen.comm_of_mem_centMod cfg.normal cfg.core (hcomm t ht b hb) hs).symm
  have hSN : S ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.le_centralizer_iff.1 hTBc).trans (Subgroup.centralizer_le_normalizer _)
    · exact (Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 cfg.xcen)).trans
        (Subgroup.center_le_normalizer _)
  have h1 := card_le_pow_glaTwoLocalRank Nat.prime_three hEel hmax hTB2 (hEle.trans hSN)
  have h2 := cfg.rank
  omega

section Main


theorem qsF3U38_of_t171 (hShape : T171.T171ShapeFact) (hNoAct : T171Sh.TwE6NoAct) :
    QSF3U38 := by
  intro Ω _ _ S B T x D K h hU hB
  have cfg := h.cfg
  haveI : Nontrivial (PSimple 3 K) := (isSimple_of_isU3eight hU).toNontrivial
  have hKc := (h.nlAct (T123C.dvd_card_of_nontrivial_pSimple Nat.prime_three inferInstance)).comp
  have hChev : IsChevSimple 2 (PSimple 3 K) := isChevTwo_of_isU3eight hU
  obtain ⟨β, hβB, hβD, hni⟩ := SG.exists_not_innDiagOn_of_u38 h hU hB
  have hCfg := S265D.cfg_of_qsnl h
  have hMax := S265D.maxG_of_qsnl h
  have hext := hShape 3 Ω B x S D K β cfg.kgroup hCfg hMax cfg.normal cfg.std hKc hChev hβB
    hβD hni
  obtain ⟨-, n, hn, hcase⟩ := id hext
  rcases hcase with hU6 | hTE6
  ·
    obtain ⟨A, d, -, -, hSetup, hcardB⟩ :=
      T171Sh.setup_of_cfg hCfg cfg.std hKc hChev hβB hβD hni
    have h3 : 3 ∣ 2 ^ n + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1) (n := n) hn
    have hA := T171Sh.card_le_u6_of_marking T171Sh.u6Marking_holds T171Sh.u6Type9_holds
      T171Sh.u6SizeModel_holds hSetup hU6 hn h3
    rw [hcardB] at hB
    norm_num at hA hB
    omega
  ·
    obtain ⟨E₀, hE₀S, hE₀, hE₀c⟩ := (S171.I171ExtremalRankFact_holds Ω S cfg.quasi n hn).2 hTE6
    obtain ⟨E, hEel, hEle, hE6⟩ :=
      exists_big_elem_abelian_pow 5 hE₀S hE₀ (cfg.elem.2 x cfg.xB) cfg.x1 cfg.xcen hE₀c
    have hlt : Nat.card B < Nat.card E := by
      rw [hB]
      exact lt_of_lt_of_le (by norm_num) hE6
    rcases cfg.maxc with hmax | ⟨hmaxE, -⟩
    · by_cases hcomm : ∀ t ∈ T, ∀ b ∈ B, ⁅t, b⁆ ∈ centModSubgroup 3 S
      · exact false_of_central_commutators_lt h hEel hEle hlt hmax hcomm
      push Not at hcomm
      obtain ⟨t, ht, b, hb, hnc⟩ := hcomm
      have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
        (Subgroup.normalizer_eq_top_iff.2 cfg.normal) ▸ Subgroup.mem_top g
      have hTB := hNoAct 3 Ω B x S D K β n cfg.kgroup hCfg hMax cfg.normal cfg.std hKc hChev
        hβB hβD hni hext hTE6 hn T (fun g _ => hSN g)
        (fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen g)) cfg.two cfg.bnorm
      have hc : ⁅t, b⁆ ∈ Subgroup.centralizer (S : Set Ω) :=
        hTB (Subgroup.commutator_mem_commutator ht hb)
      exact hnc (centMod_iff.1 (centMod_of_mem_centralizer hc))
    · have := hmaxE E hEel
      omega

theorem qsF3U38_of_t171_noAct (hShape : T171.T171ShapeFact) (hNoAct : T171.T171NoActFact) :
    QSF3U38 :=
  qsF3U38_of_t171 hShape fun p Ω _ _ B x L D K β _ hK hc hm hL hs hpc hch hβ hβD hni hext _ _ =>
    hNoAct p Ω B x L D K β hK hc hm hL hs hpc hch hβ hβD hni hext

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
