module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Sporadic.Schreier.TitsStab
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open TauCeti CFSG.Blueprint CFSG.TauCetiBridge CFSG.TauCetiBridge.ReeF4

theorem two_le_pRank_three_of_titsModel
    {X : Type} [Group X] [Finite X] (h : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.Tits_sylow3_cubic_witness (K := K) hK
  have : Finite (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) :=
    Finite.of_equiv X e.toEquiv
  have h2 := two_le_pRank_of_cubic_witness' Nat.prime_three hx hz hzx hzy
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact h2

open CFSG.Sporadic.Schreier.Tits in
theorem threeTwoWitness_titsD
    : ThreeTwoWitness titsD := by
  obtain ⟨-, -, -, ⟨-, -, hN, -, hK, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hKn, -, hKS,
      -⟩ :=
    AT_Tits_local_stabilizers_and_normal_cores
  have hKN : titsK ≤ titsN := titsK_le_titsN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := titsN) 3 (by rw [hN]; norm_num)
  have hconj : ∀ k ∈ titsK, (x : Equiv.Perm (Fin 1755)) * k * (x : Equiv.Perm (Fin 1755))⁻¹ ∈
      titsK := fun k hk => by
    have := hKn.conj_mem ⟨k, hKN hk⟩ (Subgroup.mem_subgroupOf.2 hk) x
    exact Subgroup.mem_subgroupOf.1 this
  let x' : titsD := ⟨x, titsN_le_titsD x.2⟩
  have hx' : orderOf x' = 3 := by
    have h3 : orderOf (x : Equiv.Perm (Fin 1755)) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    exact (Subgroup.orderOf_coe x').symm.trans h3
  refine ThreeTwoWitness.mk' (P := titsK.subgroupOf titsD) ?_ ?_ hx' ?_
  · intro h
    have := card_subgroupOf_titsD titsK_le_titsD
    rw [h, Subgroup.card_bot, hK] at this
    omega
  · exact titsS_isPGroup.to_le (Subgroup.comap_mono hKS)
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    exact hconj y hy

theorem reeTitsModel_tits_of_equiv
    {X : Type} [Group X] {hv : LieTypeIndex.tits.Valid}
    (e : X ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group) : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 := by
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_tits TitsLieIndex.of
  exact ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, TitsLieIndex.of.1.fixedField,
    inferInstance, inferInstance, (card_fixedField_tits _).trans (pow_one 2).symm,
    ⟨(e.trans e₁).trans (nativeModelEquiv 0).symm⟩⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
