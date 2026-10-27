module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt
public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dU3Proof

theorem exists_noncomm_of_four_dvd {S : Type} [Group S] [IsSimpleGroup S]
    (h4 : 4 ∣ Nat.card S) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI : IsMulCommutative S := ⟨⟨h⟩⟩
  have hp : (Nat.card S).Prime := Group.is_simple_iff_prime_card.1 inferInstance
  rcases hp.eq_one_or_self_of_dvd 4 h4 with h1 | h1
  · omega
  · rw [← h1] at hp
    exact absurd hp (by norm_num)

theorem isSylowTwoOf_of_isSylowOf {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.isSylowOf_iff.1 hU

end K21dU3Proof

section U3


theorem k21dGeomU3_holds : K21dGeomU3 := by
  intro S _ _ hU3
  obtain ⟨⟨d1, hv⟩, ⟨q, hq3, hd⟩, ⟨e⟩⟩ := hU3
  simp only at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp (ksm_card_eq hq3)
  rw [hp3, he1] at hm
  have hord := CFSG.HardMathSupport.Curtis.Proving.ordBound_psu_three_three hm
  haveI : IsSimpleGroup S :=
    (CFSG.LieType.Simplicity.fam_classical_converse S ⟨_, _, _, _, hm⟩).2.2
  have h4 : 4 ∣ Nat.card S := by
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm]
    norm_num
  obtain ⟨a, b, hab⟩ := K21dU3Proof.exists_noncomm_of_four_dvd h4
  intro U D E hU hUD hDs hED hE hE9 _
  exfalso
  by_cases hDtop : D = ⊤
  · subst hDtop
    have hsolv : Group.IsSolvable S :=
      solvable_of_solvable_injective (f := (Subgroup.topEquiv (G := S)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := S)).symm.injective
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  · have h96 : Nat.card D ∣ 96 := hord U D (K21dU3Proof.isSylowTwoOf_of_isSylowOf hU) hUD hDtop
    have h9 : 9 ∣ Nat.card D := hE9 ▸ Subgroup.card_dvd_of_le hED
    exact absurd (h9.trans h96) (by norm_num)

end U3

end CFSG.LocalAnalysis.RankThreeUC.S15
