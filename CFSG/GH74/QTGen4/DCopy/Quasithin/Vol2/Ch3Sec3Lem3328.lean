module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

@[expose] def Stmt3_3_28L32_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      qL L T = vPlus L T ⊔ tC L T ∧ ⁅vPlus L T, tC L T⁆ = ⊥ ∧ frattini ↥(qL L T) = ⊥

open Lem3328

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_28L32_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h23 : Stmt3_3_23_F4) (h25 : Stmt3_3_25_F4) (h26 : Stmt3_3_26_F4) (h27 : Stmt3_3_27_F4) :
    Stmt3_3_28L32_F4 := by
  intro G _ _ T M L D h hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hshort : IsShort2 L := by
    rcases (h25 G T M L D h).1 with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  obtain ⟨hLn, hDT₀⟩ : IsLnBlock L 3 ∧
      D ≤ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G) := by
    rcases h23 G T M L D h hP with h1 | ⟨⟨h2c, -⟩, -⟩
    · exact h1
    · exact absurd h2c (not_hasNoncentralTwoChief_two_of_isShort2 hshort)
  obtain ⟨d, hdD, hdM, hdV⟩ := h26 G T M L D h
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hCL : tC L T ≤ qL L T := h.tC_le_qL h38 h39 hTL
  have hQeq : qL L T = vPlus L T ⊔ tC L T :=
    le_antisymm (h.qL_le_sup_tC h38 h39 hTL hP hLn hDT₀ hdD hdV) (sup_le hVQ hCL)
  have hVT : vPlus L T ≤ Subgroup.centralizer (tC L T : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hCL.trans hQC)
  refine ⟨hQeq, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hVT, ?_⟩
  have hTCe : IsElemAbelian 2 (tC L T) := by
    by_cases hTC : tC L T = ⊥
    · rw [hTC]
      refine ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => ?_⟩
      rw [Subgroup.mem_bot] at hx
      rw [hx, one_pow]
    · obtain ⟨-, hF, -⟩ := h27 G T M L D h d hdD hdM hdV hTC
      exact isElemAbelian_of_frattini_eq_bot (h.sylow.1.to_le inf_le_left) hF
  have hQe : IsElemAbelian 2 (qL L T) := by
    rw [hQeq]
    exact B2F.isElemAbelian_sup_of_commute hred.2.1 hTCe fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hCL.trans hQC hb) a ha)
  exact frattini_eq_bot_of_isElemAbelian hQe

end CFSG.Quasithin.H13
