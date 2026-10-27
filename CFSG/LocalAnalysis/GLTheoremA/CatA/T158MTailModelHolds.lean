module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailModelAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FD
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailModelBar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.HardMathSupport.Solomon.Coordinator.I28_8

@[expose] def T158PreSetupPassage : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B L₁ L₂ : Subgroup X) (x₁ x₂ : X),
    T158Hyp p K B x₁ x₂ L₁ L₂ → InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K →
    catalogIs (PSimple p K) (t158Shape p) → IsChevSimple 2 (PSimple p K) →
    ∃ A W : Subgroup (T158Q X p),
      PreSetup p (barX p ⊤ K) (barX p ⊤ L₁) A (t158xbar p x₁) (t158xbar p x₂) ∧
        W = barX p ⊤ B ⊓ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p)) ∧
        A ≤ barX p ⊤ B ∧ A ⊓ W = ⊥ ∧ A ⊔ W = barX p ⊤ B ∧
        Nat.card A = (B ⊓ centModSubgroup p K).relIndex B

section Aux

variable {X Y : Type} [Group X] [Finite X] [Group Y]

private theorem card_eq_of_relindex {A : Subgroup Y} {B C : Subgroup X} {e : ℕ}
    (hA : Nat.card A = (B ⊓ C).relIndex B) (hB : Nat.card B = 3 ^ e * Nat.card ↥(B ⊓ C)) :
    Nat.card A = 3 ^ e := by
  have h1 : Nat.card ↥((B ⊓ C).subgroupOf B) * ((B ⊓ C).subgroupOf B).index = Nat.card B :=
    Subgroup.card_mul_index _
  have h2 : Nat.card ↥((B ⊓ C).subgroupOf B) = Nat.card ↥(B ⊓ C) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, hB, mul_comm] at h1
  have hpos : 0 < Nat.card ↥(B ⊓ C) := Nat.card_pos
  have h3 : ((B ⊓ C).subgroupOf B).index = 3 ^ e := Nat.eq_of_mul_eq_mul_right hpos h1
  rw [hA]
  exact h3

end Aux

theorem t158TailModel_union_of
    (hInn : T158InnOn t158FamTwo) (hN : T158Norm) (hPass : T158PreSetupPassage) (hS : T158SetupLU)
    (hSE : T158SetupE6) (h9 : U6Type9) (hX : TwE6BigToralExit) :
    T158TailModel fun i => t158FamU6 i ∨ t158FamTE6 i := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ _ hh hc T hT2 hTN hBT
  obtain ⟨hp3, n, hn, -, hD⟩ := hc
  subst hp3
  have hK : catalogIs (PSimple 3 K) (S10.isU6n n) ∨ catalogIs (PSimple 3 K) (S10.isTE6n n) := by
    rcases hD with ⟨h, -⟩ | ⟨h, -⟩
    exacts [Or.inl h, Or.inr h]
  have hinn := hInn X 3 K B x₁ x₂ L₁ L₂ (catalogIs_famTwo_of_tail hK) hh.prime hh.odd hh.hyp
  have hshape : catalogIs (PSimple 3 K) (t158Shape 3) := by
    rcases hK with h | h
    exacts [catalogIs_t158Shape_of_isU6n hn h, catalogIs_t158Shape_of_isTE6n hn h]
  have hcK : IsChevSimple 2 (PSimple 3 K) := S10.caseAlphaEnd_chev2 hK
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := hN X 3 K B x₁ x₂ L₁ L₂ hshape hh hinn
  obtain ⟨A, W, hPre, hW, hAB, -, hAWs, hAcard⟩ := hPass X 3 K B L₁ L₂ x₁ x₂ hh hinn hshape hcK
  have hKmap : barX 3 ⊤ K = K.map (piHom X) := barX_eq_map K
  have hBmap : barX 3 ⊤ B = B.map (piHom X) := barX_eq_map B
  have hker : Nat.Coprime 3 (Nat.card (piHom X).ker) := by
    rw [ker_piHom]
    exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28.coprime_card_oPrime3
  have eP : PSimple 3 K ≃* PSimple 3 (barX 3 ⊤ K) :=
    CFSG.LocalAnalysis.GLTheoremA.K148F.k148f_psimple_congr
      (CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv le_top)
  have hBA : ∀ b ∈ B.map (piHom X), ∃ a ∈ A, b * a⁻¹ ∈
      Subgroup.centralizer ((K.map (piHom X) : Subgroup _) : Set _) := by
    intro b hb
    rw [← hBmap, ← hAWs] at hb
    have hBel : IsElemAbelian 3 (barX 3 ⊤ B) := isElemAbelian_barX hh.hyp.1.2.2.1
    have hWB : W ≤ barX 3 ⊤ B := hW ▸ inf_le_left
    have hcomm : ∀ a ∈ A, ∀ w ∈ W, Commute a w := fun a ha w hw =>
      hBel.comm (hAB ha) (hWB hw)
    obtain ⟨a, ha, w, hw, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).1 hb
    refine ⟨a, ha, ?_⟩
    have hwc : w ∈ Subgroup.centralizer ((barX 3 ⊤ K : Subgroup _) : Set _) := by
      rw [hW] at hw
      exact hw.2
    rw [← hKmap]
    have e : a * w * a⁻¹ = w := by
      rw [(hcomm a ha w hw).eq, mul_inv_cancel_right]
    rw [e]
    exact hwc
  have hAB' : A ≤ B.map (piHom X) := hBmap ▸ hAB
  rcases hD with ⟨hU6, -, -, hcard⟩ | ⟨hTE6, -, -, hcard⟩
  ·
    have hcatL : catalogIs (PSimple 3 (barX 3 ⊤ K)) (S10.isU6n n) :=
      CFSG.LocalAnalysis.GLTheoremA.I2018.catalogIs_congr' eP hU6
    obtain ⟨hSet, -⟩ := hS _ 3 _ _ A _ _ 6 hPre (catalogIs_setupLU_of_isU6n hn hcatL)
    rw [hKmap] at hSet hcatL
    have hA27 : 3 ^ 3 ≤ Nat.card A := (card_eq_of_relindex hAcard hcard).ge
    exact t158TailModel_bar_U6 (piHom X) hker hSet hcatL hn hAB' hA27 hBA hT2 hTN hBN hBT h9
  ·
    have hcatL : catalogIs (PSimple 3 (barX 3 ⊤ K)) (S10.isTE6n n) :=
      CFSG.LocalAnalysis.GLTheoremA.I2018.catalogIs_congr' eP hTE6
    have hSet := hSE _ _ _ A _ _ hPre (catalogIs_setupE6_of_isTE6n hn hcatL)
    rw [hKmap] at hSet hcatL
    have hA81 : 3 ^ 4 ≤ Nat.card A := (card_eq_of_relindex hAcard hcard).ge
    exact t158TailModel_bar_TE6 (piHom X) hker hSet hcatL hn hAB' hA81 hBA hT2 hTN hBN hBT hX

theorem t158PreSetupPassage_of (hN : T158Norm) : T158PreSetupPassage :=
  fun _ _ _ _ _ _ _ _ _ _ hh hinn hcat hcK => exists_preSetup hN hh hinn hcat hcK

section Tables

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem t158MainTail_of_inputs
    (T : Tables112) (TL : TableL2) (TT : Tables112Types) (hInn : T158InnOn t158FamTwo)
    (hN : T158Norm) (hS : T158SetupLU) (hSE : T158SetupE6) (h9 : U6Type9) (hX : TwE6BigToralExit) :
    T158MainTail :=
  t158MainTail_of_model T TL TT
    (t158TailModel_union_of hInn hN (t158PreSetupPassage_of hN) hS hSE h9 hX)

end Tables

end CFSG.LocalAnalysis.GLTheoremA.T158

end
