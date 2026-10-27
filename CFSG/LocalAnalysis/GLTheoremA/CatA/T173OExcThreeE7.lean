module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7Conj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7Unitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.SeitzReduction.EPilot

section Model


variable {F : Type} [Field F] [Finite F]

theorem exists_twoGroup_decomp_of_le_perpLevi (hF : Nat.card F = 2)
    {A : Subgroup ↥(adjointGroup .E7 F)} {d : ↥(adjointGroup .E7 F)}
    (hAel : IsElemAbelian 3 A) (h6 : 3 ^ 6 ≤ Nat.card A) (hd : IsStdElt 3 A d)
    (hAM : A ≤ perpLevi .E7 F) (hKM : stdLayer d ≤ perpLevi .E7 F) :
    ∃ T : Subgroup ↥(adjointGroup .E7 F), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ stdLayer d ∧
      A = (A ⊓ stdLayer d) ⊔
        (A ⊓ Subgroup.normalizer (T : Set ↥(adjointGroup .E7 F))) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  let e := omegaEquivPerpLeviE7 F
  have hdM : d ∈ perpLevi .E7 F := hAM hd.1
  let Bb := (A.subgroupOf (perpLevi .E7 F)).map e.symm.toMonoidHom
  let L := ((stdLayer d).subgroupOf (perpLevi .E7 F)).map e.symm.toMonoidHom
  have hcomp := isComponentOf_centralizer_map_symm e hdM hd.2.2.2.1 hKM
  have hcd := inf_centralizer_map_symm_eq e hAM hKM hdM hd.2.2.2.2
  have hBb : IsElemAbelian 3 Bb :=
    (hAel.subgroupOf (perpLevi .E7 F)).map e.symm.toMonoidHom
  have hsub : Nat.card (A.subgroupOf (perpLevi .E7 F)) = Nat.card A := by
    rw [← Subgroup.card_map_of_injective (K := A.subgroupOf (perpLevi .E7 F))
        (f := (perpLevi .E7 F).subtype) (perpLevi .E7 F).subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le hAM]
  have hcard : 3 ^ 6 ≤ Nat.card Bb := by
    change 3 ^ 6 ≤ Nat.card ((A.subgroupOf (perpLevi .E7 F)).map e.symm.toMonoidHom)
    rw [Subgroup.card_map_of_injective e.symm.injective, hsub]
    exact h6
  have hdB : e.symm ⟨d, hdM⟩ ∈ Bb :=
    Subgroup.mem_map_of_mem e.symm.toMonoidHom (Subgroup.mem_subgroupOf.mpr hd.1)
  have hd1 : e.symm ⟨d, hdM⟩ ≠ 1 := by
    intro h
    apply hd.2.1
    have h' : (⟨d, hdM⟩ : ↥(perpLevi .E7 F)) = 1 := by
      rw [← e.apply_symm_apply ⟨d, hdM⟩, h, map_one]
    exact congrArg Subtype.val h'
  have hpq : 3 ∣ Nat.card F + 1 := by
    rw [hF]
  obtain ⟨T', hT'ne, hT'2, hT'L, hT'dec⟩ :=
    exists_twoGroup_decomp_of_full_rank
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 F) (by simp)
      (by norm_num) Nat.prime_three (by norm_num) hpq
      (Bb := Bb) (L := L) hBb hcard hdB hd1 hcomp hcd
  obtain ⟨T, hTne, hT2, hTL, hTdec⟩ :=
    exists_twoGroup_decomp_map (A' := Bb) (K' := L)
      (ι := (perpLevi .E7 F).subtype.comp e.toMonoidHom)
      ((perpLevi .E7 F).subtype_injective.comp e.injective)
      ⟨T', hT'ne, hT'2, hT'L, hT'dec⟩
  have hBmap : Bb.map ((perpLevi .E7 F).subtype.comp e.toMonoidHom) = A :=
    map_map_symm_subgroupOf_eq e hAM
  have hLmap : L.map ((perpLevi .E7 F).subtype.comp e.toMonoidHom) = stdLayer d :=
    map_map_symm_subgroupOf_eq e hKM
  rw [hBmap, hLmap] at hTdec
  exact ⟨T, hTne, hT2, hTL.trans hLmap.le, hTdec⟩

theorem stdExtendsN_of_le_perpLevi (hF : Nat.card F = 2)
    {A : Subgroup ↥(adjointGroup .E7 F)} {d : ↥(adjointGroup .E7 F)}
    (hAel : IsElemAbelian 3 A) (h6 : 3 ^ 6 ≤ Nat.card A) (hd : IsStdElt 3 A d)
    (hAM : A ≤ perpLevi .E7 F) (hKM : stdLayer d ≤ perpLevi .E7 F) : StdExtendsN 3 A d := by
  obtain ⟨y, hyC, hy3, hyM⟩ := exists_mem_centralizer_perpLevi_E7_two hF
  refine ⟨exists_twoGroup_decomp_of_le_perpLevi hF hAel h6 hd hAM hKM, y,
    Subgroup.centralizer_le hAM hyC, Subgroup.centralizer_le hKM hyC, hy3, ?_⟩
  exact fun hy => hyM (hAM hy)

end Model

section Big


variable {F : Type} [Field F] [Finite F]

theorem stdVanishes_or_stdExtendsN_three_E7_two (hF : Nat.card F = 2)
    [Finite ↥(adjointGroup .E7 F)] {A : Subgroup ↥(adjointGroup .E7 F)}
    {d : ↥(adjointGroup .E7 F)} (hA : GLAIsBmax 3 A) (hd : IsStdElt 3 A d) :
    StdVanishes A d ∨ StdExtendsN 3 A d := by
  obtain ⟨hAel, hcard, -⟩ := hA
  have h6 : 3 ^ 6 ≤ Nat.card A := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (six_le_glaTwoLocalRank_E7_two hF)
  by_cases hv : StdVanishes A d
  · exact Or.inl hv
  · obtain ⟨T, hT, hT2, hTN⟩ := not_not.1 hv
    obtain ⟨g, hAM, hKM⟩ := exists_conj_le_perpLevi_of_stdElt hF hAel h6 hd hT hT2 hTN
    have hAel' : IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) :=
      hAel.map (MulAut.conj g).toMonoidHom
    have hcard' : 3 ^ 6 ≤ Nat.card (A.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact h6
    have hd' : IsStdElt 3 (A.map (MulAut.conj g).toMonoidHom) (MulAut.conj g d) :=
      isStdElt_map (MulAut.conj g) hd
    exact Or.inr ((stdExtendsN_map_iff (MulAut.conj g)).1
      (stdExtendsN_of_le_perpLevi hF hAel' hcard' hd' hAM hKM))

theorem modelFactExcThree_E7 : ModelFactExcThree .E7 :=
  fun _ _ _ _ hF => fun _ _ hA hd => stdVanishes_or_stdExtendsN_three_E7_two hF hA hd

end Big

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
