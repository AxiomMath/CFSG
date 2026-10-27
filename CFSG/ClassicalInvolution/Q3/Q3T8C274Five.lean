module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262Type
public import CFSG.ClassicalInvolution.Q3.Q3T7SectC
public import CFSG.ClassicalInvolution.Q3.Q3MTModel1
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk1
public import CFSG.ClassicalInvolution.Q3.Q3EXD4Model
public import CFSG.ClassicalInvolution.Asc77.AscC25J12
public import CFSG.ClassicalInvolution.Asc77.AscC25J13
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3MTDatum
public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3TIVOr2
public import CFSG.ClassicalInvolution.Q3.Q3TY1
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank

section Clique


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dConnected_of_five_clique3 {n : ℕ} (hih : IH8T 3 1 n) (hn : CITBelowT (.sl2 3 1) n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (B : Fin 5 → Subgroup X) (hB : ∀ i, B i ∈ Φ) (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) : DConnected Φ := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hne : Φ.Nonempty := ⟨B 0, hB 0⟩
  have hedge : dAdj Φ (B 0) (B 1) := Or.inl (hadj 0 1 (by decide))
  rcases dConnected_or_transitive3 hih.thm4 hlt hΦ hO hA with hc | htrans
  · exact hc
  obtain ⟨D, hcard⟩ := Q3T7.exists_omegaLieU_sect hn hlt hΦ hO hgen htrans hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · obtain ⟨M⟩ : Nonempty (Ih8Model 3 1 Φ t k e) :=
      ⟨Q3T7.toIh8ModelSect D hΦ hgen hcard i ht hadm he hc⟩
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
      rcases ih8G2D4EdgeU_proved X Φ hΦ hA htrans t k e ⟨M⟩ hG2d4 with h' | h'
      · exact absurd hedge (h' _ (hB 0) _ (hB 1))
      · exact h'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    subst hef
    by_cases h3' : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)
    · have : IsSimpleGroup X := Q3T7.isSimpleGroup_of_ih8Model_three M h3'
      exact absurd hedge (ih8ThreeU_proved X Φ hΦ htrans t k 1 ⟨M⟩ h3' _ (hB 0) _ (hB 1))
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have hpre : ∀ j, ∃ R ∈ M.cls, B j = R.map M.ψ := fun j => (M.mem_iff _).mp (hB j)
    choose R hRcls hRB using hpre
    have hcomm : ∀ j j', j ≠ j' → Commutes (R j) (R j') := fun j j' hjj =>
      Q3MT.commutes_of_omegaNbr3 M hΦ hG2 hD4 (hRcls j) (hRcls j')
        (by rw [← hRB j, ← hRB j']; exact hadj j j' hjj)
    have hRne : ∀ j j', j ≠ j' → R j ≠ R j' := fun j j' hjj h =>
      hjj (hinj (by rw [hRB j, hRB j', h]))
    have hRf := fun j => M.cls_sub (hRcls j)
    rcases tag_casesU hp2 ht hadm hG2 hD4 with hconn | hsmall
    · exact dConnected_of_connectedU M hΦ hne hG2 hD4 hconn
    exfalso
    have h01 : (0 : Fin 5) ≠ 1 := by decide
    have h02 : (0 : Fin 5) ≠ 2 := by decide
    have h12 : (1 : Fin 5) ≠ 2 := by decide
    have hNT := Q3TIY.smallNoThree3
    rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      have hk2 : 2 ≤ k := hadm.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact hA1 ⟨rfl, rfl⟩
      · exact h3' (Or.inl ⟨rfl, rfl⟩)
      · exact hNT _ _ hadm (Or.inr (Or.inl ⟨rfl, rfl⟩)) _ (hRf 0) _ (hRf 1) _ (hRf 2)
          (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
          (hcomm 1 2 h12)
    ·
      have hk3 : 3 ≤ k := hadm.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact h3' (Or.inr ⟨rfl, rfl⟩)
      · exact hNT _ _ hadm (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) _ (hRf 0) _ (hRf 1) _ (hRf 2)
          (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
          (hcomm 1 2 h12)
    · exact hNT _ _ hadm (Or.inl ⟨rfl, rfl⟩) _ (hRf 0) _ (hRf 1) _ (hRf 2) (hRne 0 1 h01)
        (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)
    · exact hNT _ _ hadm (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) _ (hRf 0) _ (hRf 1) _
        (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
        (hcomm 1 2 h12)
    ·
      obtain ⟨F₄, -, -, -, -, -, -, hall⟩ := Q3W.EX.cliqueFour_fund_plus_four3 hadm
        ⟨R 0, hRf 0⟩ ⟨R 1, hRf 1⟩ ⟨R 2, hRf 2⟩
        (fun h => hRne 0 1 h01 (congrArg Subtype.val h))
        (fun h => hRne 0 2 h02 (congrArg Subtype.val h))
        (fun h => hRne 1 2 h12 (congrArg Subtype.val h))
        (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)
      have h3 := hall ⟨R 3, hRf 3⟩ (hcomm 0 3 (by decide))
      have h4 := hall ⟨R 4, hRf 4⟩ (hcomm 0 4 (by decide))
      have h31 : R 3 ≠ R 1 := hRne 3 1 (by decide)
      have h32 : R 3 ≠ R 2 := hRne 3 2 (by decide)
      have h41 : R 4 ≠ R 1 := hRne 4 1 (by decide)
      have h42 : R 4 ≠ R 2 := hRne 4 2 (by decide)
      have e3 : R 3 = F₄.1 := by
        rcases h3 with h | h | h
        · exact absurd (congrArg Subtype.val h) h31
        · exact absurd (congrArg Subtype.val h) h32
        · exact congrArg Subtype.val h
      have e4 : R 4 = F₄.1 := by
        rcases h4 with h | h | h
        · exact absurd (congrArg Subtype.val h) h41
        · exact absurd (congrArg Subtype.val h) h42
        · exact congrArg Subtype.val h
      exact hRne 3 4 (by decide) (e3.trans e4.symm)
    · exact hNT _ _ hadm (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) _ (hRf 0) _ (hRf 1) _
        (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
        (hcomm 1 2 h12)
  ·
    exact absurd hedge (Q3T7.dEdgeless_of_top_mem3 htrans
      (Q3T7.top_mem_of_sl23_component_sect D hne hgen hcard i hc) _ (hB 0) _ (hB 1))
  ·
    obtain ⟨e⟩ := Q3T7.exists_mulEquiv_m11_sect D hgen hcard i hc
    exact absurd hedge (dEdgeless_of_mulEquiv_m11 e hΦ (D.card_eq h3) _ (hB 0) _ (hB 1))

end Clique

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
