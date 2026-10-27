module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectA
public import CFSG.ClassicalInvolution.Q3.Q3T7SectA
public import CFSG.ClassicalInvolution.Q3.Q3T7SectB
public import CFSG.ClassicalInvolution.Q3.Q3T7SectC1
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk1
public import CFSG.ClassicalInvolution.Q3.Q3MTModel1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuGraph
public import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Uniform.U3Thm7
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.U5Three2
public import CFSG.ClassicalInvolution.Uniform.U8Basic
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen
public import CFSG.ClassicalInvolution.Uniform.UMember
public import CFSG.ClassicalInvolution.Q3.Q3TIVOr2

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.Blueprint
open scoped MatrixGroups commutatorElement

section TwinTriple


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstarConnected_of_twinTriple3 (hS : TransSect3 Φ) (D : OmegaLieU 3 1 Φ)
    (hcard : D.card = 1) (htt : TwinTriple Φ) : T3.DStarConnected Φ := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨K, hK, K', hK'tw, hne', J, hJK, hJK'⟩ := htt
  have hΦ := hS.hyp
  have hΩg := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  have hne : Φ.Nonempty := ⟨K, hK⟩
  have hDStar : DConnected Φ → T3.DStarConnected Φ := fun hc K₁ hK₁ L hL =>
    Q3T6.Mu.dComp_subset_dstarComp hΩg K₁ (hc K₁ hK₁ L hL)
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · obtain ⟨M⟩ : Nonempty (Ih8Model 3 1 Φ t k e) :=
      ⟨toIh8ModelSect D hΦ hS.gen hcard i ht hadm he hc⟩
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exact absurd (noTwins_of_g2d4_datum M hS.trans hG2d4 K hK K' hK'tw) hne'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    subst hef
    by_cases h3' : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)
    · have : IsSimpleGroup X := isSimpleGroup_of_ih8Model_three M h3'
      exact absurd (Or.inl hJK : dAdj Φ K J)
        (ih8ThreeU_proved X Φ hΦ hS.trans t k 1 ⟨M⟩ h3' _ hK _ hJK.1)
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have hex : ExactMembers Φ := D.exactMembers hΦ
    obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
    obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
    obtain ⟨B, hB, rfl⟩ := (M.mem_iff K').mp hK'Ω
    obtain ⟨S, hS', rfl⟩ := (M.mem_iff J).mp hJK.1
    have hAB : A ≠ B := fun h => hne' (by rw [h])
    have hAS : A ≠ S := fun h => hJK.2.1 (by rw [h])
    have hBS : B ≠ S := fun h => hJK'.2.1 (by rw [h])
    have hne'' : A.map M.ψ ≠ B.map M.ψ := fun h => hne' h.symm
    obtain ⟨cAB, -⟩ := ih8_twin_data3 hΦ hex M.ker_le_center (ih8Model_ker_pow_three M hD4)
      (ih8Model_gen3 M hG2 hD4 hA) (M.map_mem hA) (M.map_mem hB) hne'' hzK hzK'
    have cAS := Q3MT.commutes_of_omegaNbr3 M hΦ hG2 hD4 hA hS' hJK
    have cBS := Q3MT.commutes_of_omegaNbr3 M hΦ hG2 hD4 hB hS' hJK'
    have hAf := M.cls_sub hA
    have hBf := M.cls_sub hB
    have hSf := M.cls_sub hS'
    rcases tag_casesU hp2 ht hadm hG2 hD4 with hconn | hsmall
    · exact hDStar (dConnected_of_connectedU M hΦ hne hG2 hD4 hconn)
    have hNT := Q3TIY.smallNoThree3
    rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      exfalso
      have hk2 : 2 ≤ k := hadm.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact hA1 ⟨rfl, rfl⟩
      · exact h3' (Or.inl ⟨rfl, rfl⟩)
      · exact hNT _ _ hadm (Or.inr (Or.inl ⟨rfl, rfl⟩)) _ hAf _ hBf _ hSf hAB hAS hBS cAB cAS cBS
    ·
      exfalso
      have hk3 : 3 ≤ k := hadm.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact h3' (Or.inr ⟨rfl, rfl⟩)
      · exact hNT _ _ hadm (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) _ hAf _ hBf _ hSf hAB hAS hBS
          cAB cAS cBS
    · exfalso
      exact hNT _ _ hadm (Or.inl ⟨rfl, rfl⟩) _ hAf _ hBf _ hSf hAB hAS hBS cAB cAS cBS
    · exfalso
      exact hNT _ _ hadm (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) _ hAf _ hBf _ hSf hAB
        hAS hBS cAB cAS cBS
    ·
      exact Q3T8.Asc77.ih8D4Star3 X Φ hΦ ⟨M⟩
    · exfalso
      exact hNT _ _ hadm (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) _ hAf _ hBf _ hSf hAB
        hAS hBS cAB cAS cBS
  ·
    exact absurd (top_mem_of_sl23_component_sect D hne hS.gen hcard i hc)
      (top_notMem_of_transitive3 hS.trans hK hK'tw.1 hne')
  ·
    obtain ⟨e⟩ := exists_mulEquiv_m11_sect D hS.gen hcard i hc
    exact absurd (noTwins_of_mulEquiv_m11 e hΦ K hK K' hK'tw) hne'

end TwinTriple

end CFSG.ClassicalInvolution.Q3.Q3T7
