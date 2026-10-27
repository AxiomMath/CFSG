module

public import CFSG.GH74.Generic.JMaxCongr
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.BProg.B3.S3L3Defs
public import CFSG.GH74.Generic.BProg.B3.S3SL2Depth
public import CFSG.GH74.Generic.S45.LDiagPerm
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

theorem gen4_bar (hgen : Gen4 G) (y : G) : Gen4 (CentralizerBar y) :=
  Gen4.quotient _ (Gen4.subgroup _ hgen)

theorem pPrimeCore_bar_eq_bot (y : G) : pPrimeCore 2 (CentralizerBar y) = ⊥ :=
  GLS.pPrimeCore_quotient_eq_bot (↥(centralizer ({y} : Set G)))

omit [Finite G] in
theorem yy_mem (y : G) : y ∈ centralizer ({y} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]

omit [Finite G] in
theorem ybar_central (y : G) (b : CentralizerBar y) :
    b * proj y ⟨y, yy_mem y⟩ = proj y ⟨y, yy_mem y⟩ * b := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
  show proj y c * proj y ⟨y, yy_mem y⟩ = proj y ⟨y, yy_mem y⟩ * proj y c
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 c.2)

theorem ybar_ne_one (hy : orderOf y = 2) : proj y ⟨y, yy_mem y⟩ ≠ 1 := by
  intro h1
  have hodd := proj_odd y ⟨y, yy_mem y⟩ h1
  rw [Subgroup.orderOf_mk, hy] at hodd
  exact absurd hodd (by decide)

theorem rank_ge_three (h : Setup30 G x K A y) : oBound 2 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := by
  obtain ⟨-, hel, hcard, -⟩ := h.src
  have hyA : y ∈ A := (Subgroup.mem_inf.1 h.y_mem).1
  have hAy : A ≤ centralizer ({y} : Set G) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact (GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hel).1 a ha y hyA
  have h8 : Nat.card ↥A = 2 ^ pRank 2 ↥A := GLS.C3.Layer1.Back.card_eq_two_pow_pRank hel
  have hr : pRank 2 ↥A = 3 := by
    have : (2 : ℕ) ^ pRank 2 ↥A = 2 ^ 3 := by rw [← h8, hcard]; norm_num
    exact Nat.pow_right_injective le_rfl this
  have := GLS.C3.Layer1.Back.pRank_mono' hAy
  have h3 : oBound 2 = 3 := by simp [oBound]
  omega

theorem center_bar_ne_bot {H : Subgroup G} (hy : orderOf y = 2) (hyH : y ∈ H) :
    center ↥(barSub y H) ≠ ⊥ := by
  intro hbot
  have hmem : proj y ⟨y, yy_mem y⟩ ∈ barSub y H := proj_mem_barSub (yy_mem y) hyH
  have hc : (⟨proj y ⟨y, yy_mem y⟩, hmem⟩ : ↥(barSub y H)) ∈ center ↥(barSub y H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (ybar_central y g.1)
  rw [hbot, Subgroup.mem_bot] at hc
  exact ybar_ne_one hy (congrArg Subtype.val hc)

theorem isSimple_of_depth {Kt : Type} [Group Kt] {i : ℕ} (hi : InG2Depth i Kt) (h78 : i = 7 ∨ i = 8) :
    IsSimpleGroup Kt := by
  obtain ⟨-, hc⟩ := hi
  rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hL3⟩ |
    ⟨rfl, -, hA⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · obtain ⟨p, f, -, -, -, hm⟩ := hL3
    exact isSimpleGroup_of_lieModel_L3' hm
  · rcases hA with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
      exact MulEquiv.isSimpleGroup e
    · have : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
      exact MulEquiv.isSimpleGroup e

theorem not_inG2_bar (h : Setup30 G x K A y) {H : Subgroup G}
    (hHc : IsPCompIn 2 (centralizer ({y} : Set G)) H) (hyH : y ∈ H) : ¬ InG2 ↥(barSub y H) := by
  intro hG2
  obtain ⟨eH⟩ := GLS.C3.Layer1.PumpCalc.kBar_equiv_bar hHc
  have hG2' : InG2 (↥H ⧸ pPrimeCore 2 ↥H) := inG2_of_mulEquiv eH.symm hG2
  have hIL : IsILo 2 y H := ⟨h.y_ord, rank_ge_three h, hHc⟩
  have hsimple : IsSimpleGroup (↥H ⧸ pPrimeCore 2 ↥H) := by
    rcases BProg.B3.depth7_simple h.circ h.shape hIL hG2' with h7 | h8
    · exact isSimple_of_depth h7 (Or.inl rfl)
    · exact isSimple_of_depth h8 (Or.inr rfl)
  have hnc := exists_noncomm_of_isQuasisimple_aux hG2'.1.1
  have hcen : center (↥H ⧸ pPrimeCore 2 ↥H) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥H ⧸ pPrimeCore 2 ↥H)) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top b)) a)
  apply center_bar_ne_bot h.y_ord hyH
  change center ↥(GLS.C3.Layer1.PumpCalc.bar y H) = ⊥
  rw [← Subgroup.map_center_eq eH, hcen, Subgroup.map_bot]

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
