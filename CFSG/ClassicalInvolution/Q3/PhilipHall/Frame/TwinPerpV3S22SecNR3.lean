module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecNR2
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutL
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecNR

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_tag3_of_trans {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hlt : Nat.card X < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hdisc : ¬ DConnected Φ)
    {A B : Subgroup X} (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) :
    ∃ (t : StatedLieTag) (k : ℕ), ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) ∧
      Nonempty (Ih8Model 3 1 Φ t k 1) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hne : Φ.Nonempty := ⟨A, hAΦ⟩
  have hedge : dAdj Φ A B := Or.inl hB
  obtain ⟨D, hcard⟩ := Q3T7.exists_omegaLieU_sect hn hlt hΦ hO hgen htrans hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · obtain ⟨M⟩ : Nonempty (Ih8Model 3 1 Φ t k e) :=
      ⟨Q3T7.toIh8ModelSect D hΦ hgen hcard i ht hadm he hc⟩
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exfalso
      have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
      rcases ih8G2D4EdgeU_proved X Φ hΦ hA htrans t k e ⟨M⟩ hG2d4 with h' | h'
      · exact h' A hAΦ B hB.1 hedge
      · exact hdisc h'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    subst hef
    by_cases h3' : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)
    · exfalso
      have : IsSimpleGroup X := Q3T7.isSimpleGroup_of_ih8Model_three M h3'
      exact ih8ThreeU_proved X Φ hΦ htrans t k 1 ⟨M⟩ h3' A hAΦ B hB.1 hedge
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    rcases tag_casesU hp2 ht hadm hG2 hD4 with hconn | hsmall
    · exact absurd (dConnected_of_connectedU M hΦ hne hG2 hD4 hconn) hdisc
    rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ k := hadm.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact absurd ⟨rfl, rfl⟩ hA1
      · exact absurd (Or.inl ⟨rfl, rfl⟩) h3'
      · exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, rfl⟩), ⟨M⟩⟩
    · have hk3 : 3 ≤ k := hadm.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact absurd (Or.inr ⟨rfl, rfl⟩) h3'
      · exact ⟨.PSU, 4, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ⟨M⟩⟩
    · exact ⟨.PSp, 2, Or.inl ⟨rfl, rfl⟩, ⟨M⟩⟩
    · exact ⟨.POmegaOdd, 3, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), ⟨M⟩⟩
    · exact ⟨.POmegaPlus, 4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))), ⟨M⟩⟩
    · exact ⟨.POmegaMinus, 4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))), ⟨M⟩⟩
  · exfalso
    exact Q3T7.dEdgeless_of_top_mem3 htrans
      (Q3T7.top_mem_of_sl23_component_sect D hne hgen hcard i hc) A hAΦ B hB.1 hedge
  · exfalso
    obtain ⟨e⟩ := Q3T7.exists_mulEquiv_m11_sect D hgen hcard i hc
    exact dEdgeless_of_mulEquiv_m11 e hΦ (D.card_eq h3) A hAΦ B hB.1 hedge

theorem sq_noRoot_of_twin_pair {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hlt : Nat.card X < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hdisc : ¬ T3.DStarConnected Φ)
    {A B : Subgroup X} (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x₀ : X}
    (hxA : IsUniqueInvolution A x₀) (hxB : IsUniqueInvolution B x₀) (α : MulAut X)
    (hαA : ∀ a ∈ A, α a = a) (hαB : ∀ b ∈ B, α b = b) : α * α ≠ MulAut.conj x₀ := by
  have hΩg := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  obtain ⟨t, k, htag, ⟨M⟩⟩ := e4_tag3_of_trans hn hlt hΦ hO hgen hA htrans
    (fun hc => hdisc fun K hK L hL => Q3T6.Mu.dComp_subset_dstarComp hΩg K (hc K hK L hL))
    hAΦ hB
  have hcen : x₀ * x₀ ∈ Subgroup.center X := by
    rw [hxA.sq]
    exact Subgroup.one_mem _
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h4 | ⟨rfl, rfl⟩ | h6
  ·
    have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
    have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
    have hnpsl : ¬ (StatedLieTag.PSp = .PSL ∧ (2 : ℕ) = 2) := by simp
    have hSperf : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
      Group.isPerfect_def.2
        (ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial M.admissible).1.1
    obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
      Q3T8.Asc77.E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hAΦ hB hxA hxB hcen
    have key := sqNoRootC_psp2 X M.ψ M.surj M.ker_le_center R R' (M.cls_sub hR)
      (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1
      (hy.trans hy'.symm) α (fun r hr => hαA _ (hAR ▸ Subgroup.mem_map_of_mem _ hr))
      (fun r hr => hαB _ (hBR ▸ Subgroup.mem_map_of_mem _ hr))
    rwa [hy] at key
  ·
    have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
    have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
    have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
    have hSperf : Group.IsPerfect (modelUniv .PSL 4 3 1 Fact.out).K :=
      Group.isPerfect_def.2
        (ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial M.admissible).1.1
    obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
      Q3T8.Asc77.E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hAΦ hB hxA hxB hcen
    have key := sqNoRootC_psl4 M.admissible X M.ψ M.surj M.ker_le_center R R'
      (M.cls_sub hR) (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1
      (hy.trans hy'.symm) α (fun r hr => hαA _ (hAR ▸ Subgroup.mem_map_of_mem _ hr))
      (fun r hr => hαB _ (hBR ▸ Subgroup.mem_map_of_mem _ hr))
    rwa [hy] at key
  · exact absurd (Q3T8.Asc77.E4G3.dstarConnected_psu43 hΦ M) hdisc
  · exact absurd (Q3T8.Asc77.E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inl h4) hAΦ hB hxA hxB
      hcen) hdisc
  · exact absurd (Q3T8.Asc77.E4G3.dstarConnected_spin8plus3 hΦ M) hdisc
  · exact absurd (Q3T8.Asc77.E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inr h6) hAΦ hB hxA hxB
      hcen) hdisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecNR
