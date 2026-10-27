module

public import CFSG.Goldschmidt.StatementsG
import CFSG.Goldschmidt.Steps.G41
import CFSG.Goldschmidt.Steps.G44
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage
public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G4

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_ge_eight (S : Sylow 2 G) {U : Subgroup G} (hUS : U ≤ S)
    (hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G)) (hU : IsElemAbelian 2 U)
    (hU4 : 4 ≤ Nat.card U) (h3 : 3 ≤ CFSG.Assembly.twoRank G) :
    ∃ B : Subgroup G, U ≤ B ∧ IsElemAbelian 2 B ∧ 8 ≤ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h8 : 8 ≤ Nat.card U
  · exact ⟨U, le_rfl, hU, h8⟩
  have hcard : Nat.card U = 4 := by
    obtain ⟨k, hk⟩ := ((S.isPGroup').to_le hUS).exists_card_eq
    rw [hk] at hU4 h8 ⊢
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> omega
    · exact absurd (Nat.pow_le_pow_right (show 0 < 2 by norm_num) h) (by omega)
  obtain ⟨E₀, hE₀, hE₀8⟩ :=
    CFSG.ProperTwoGeneratedCore.exists_elementary_eight_of_rank_three (G := G) h3
  obtain ⟨Q, hE₀Q⟩ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 E₀ hE₀).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  set E : Subgroup G := E₀.map (MulAut.conj g).toMonoidHom with hEdef
  have hES : E ≤ S := by
    rw [← hg, Sylow.coe_subgroup_smul, hEdef]
    exact Subgroup.map_mono hE₀Q
  have hE : IsElemAbelian 2 E := CFSG.LargeEvenClassification.Helpers.elementary_map E₀ hE₀ _
  have hE8 : Nat.card E = 8 := by
    rw [hEdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀8]
  have hVn : (U.subgroupOf S).Normal := normal_subgroupOf_of_stronglyClosed hUS hUcl
  have hsub : ∀ {X : Subgroup G}, IsElemAbelian 2 X → IsElemAbelian 2 (X.subgroupOf S) := by
    intro X hX
    have := hX.1
    refine ⟨Subgroup.comap_injective_isMulCommutative X (S : Subgroup G).subtype_injective,
      fun x hx => Subtype.ext ?_⟩
    simpa using hX.2 (x : G) hx
  have hV : IsElemAbelian 2 (U.subgroupOf S) := hsub hU
  have hVcard : Nat.card (U.subgroupOf S) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hcard]
  have hA : IsElemAbelian 2 (E.subgroupOf S) := hsub hE
  have hAcard : Nat.card (E.subgroupOf S) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv, hE8]
  obtain ⟨-, -, hVW, hW, hW8, -⟩ := CFSG.ProperTwoGeneratedCore.normal_four_centralizer_rank_three
    S.isPGroup' (U.subgroupOf S) hV hVcard (E.subgroupOf S) hA hAcard
  refine ⟨(E.subgroupOf S ⊓ Subgroup.centralizer ((U.subgroupOf S : Subgroup S) : Set S) ⊔
    U.subgroupOf S).map (S : Subgroup G).subtype, ?_,
    CFSG.LargeEvenClassification.Helpers.elementary_map _ hW _, ?_⟩
  · intro u hu
    exact ⟨⟨u, hUS hu⟩, hVW (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  · rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hW8

end G4

theorem G4 :
    S_G4 := by
  intro G _ _ _ hnab hIH h3 hse S A U hAS hA hAcl hUA hmin
  obtain ⟨hUel, hU4, -, -, hidx2, hirr⟩ := N31 G hnab S A U hAS hA hAcl hUA hmin
  exact
    { isSimpleGroup := inferInstance
      nonabelian := hnab
      le := hmin.1
      elem := hUel
      ne_bot := hmin.2.1
      closed := hmin.2.2.1
      irreducible := hirr
      noIndexTwo := hidx2
      rank := G4.exists_elemAbelian_ge_eight S hmin.1 hmin.2.2.1 hUel hU4 h3
      gen := G44.g44 hnab S A U hAS hA hAcl hUA hmin hse
      sstar := G41 G hIH S U hmin.1 hUel.1 hmin.2.2.1 }

end CFSG.Goldschmidt
