module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Step

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Rank

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem s265f_card_dgrp {p : ℕ} (hp : p.Prime) {B : Subgroup Ω} {x b : Ω} (hB : IsElemAbelian p B)
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hb : b ∈ B) (hbx : b ∉ Subgroup.zpowers x) :
    Nat.card ↥(Dgrp b x) = p ^ 2 := by
  haveI := Fact.mk hp
  have hzx : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hxB
  have hordx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 x hxB) hx1]
  have hordb : Nat.card (Subgroup.zpowers b) = p := by
    have hb1 : b ≠ 1 := fun h => hbx (h ▸ (Subgroup.zpowers x).one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hb) hb1]
  rw [dgrp_eq]
  exact s265_card_sup hp hB hzx (by rw [hordx, pow_one]) hb hbx hordb

private theorem s265f_zpowers_le_dgrp (x b : Ω) : Subgroup.zpowers x ≤ Dgrp b x := by
  rw [dgrp_eq]
  exact le_sup_left

theorem qu_cent_eq {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b) :
    B ⊓ centModSubgroup p S = Subgroup.zpowers x := by
  ext c
  constructor
  · rintro ⟨hcB, hcM⟩
    exact (cfg.centB c hcB).1 (centMod_iff.2 hcM)
  · intro hc
    have hcB : c ∈ B := Subgroup.zpowers_le.2 cfg.xB hc
    exact ⟨hcB, centMod_iff.1 ((cfg.centB c hcB).2 hc)⟩

theorem qu_aut_rank {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b) :
    ∃ A : Subgroup (MulAut (↥S ⧸ Subgroup.center ↥S)), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A := by
  have hp := cfg.prime
  haveI := Fact.mk hp
  have hcard := s265f_card_dgrp hp cfg.elem cfg.xB cfg.x1 cfg.hb cfg.hbx
  have hle : Subgroup.zpowers x ≤ Dgrp b x := s265f_zpowers_le_dgrp x b
  have hordx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1]
  refine S2019.exists_elemAbelian_aut_rank_ge_three hp cfg.normal cfg.quasi cfg.core cfg.elem
    (D := Dgrp b x) (by rw [qu_cent_eq cfg]; exact hle) ?_ ?_
  · rw [qu_cent_eq cfg]
    have h1 := S2019.relIndex_mul_card_of_le hle
    rw [hordx, hcard] at h1
    have hp0 : 0 < p := hp.pos
    have : (Subgroup.zpowers x).relIndex (Dgrp b x) * p = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  · rw [hcard, ← pow_add]
    exact cfg.big

noncomputable def qu_pSimpleEquiv {p : ℕ} {S : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) :
    PSimple p S ≃* (↥S ⧸ Subgroup.center ↥S) :=
  let eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)

theorem qu_aut_rank' {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b) :
    ∃ A : Subgroup (MulAut (PSimple p S)), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A := by
  obtain ⟨A, hA, hcard⟩ := qu_aut_rank cfg
  let e : MulAut (↥S ⧸ Subgroup.center ↥S) ≃* MulAut (PSimple p S) :=
    MulAut.congr (qu_pSimpleEquiv cfg.core).symm
  refine ⟨A.map e.toMonoidHom, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hA e.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard

end Rank

end CFSG.LocalAnalysis.GLTheoremA.S265

end
