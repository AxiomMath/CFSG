module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.SeitzReduction.EPilot

section Big


variable {F : Type} [Field F] [Finite F]

theorem exists_conj_le_perpLevi_of_stdElt (hF : Nat.card F = 2)
    {A : Subgroup ↥(adjointGroup .E7 F)} {d : ↥(adjointGroup .E7 F)} (hAel : IsElemAbelian 3 A)
    (h6 : 3 ^ 6 ≤ Nat.card A) (hd : IsStdElt 3 A d)
    {T : Subgroup ↥(adjointGroup .E7 F)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTN : innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set ↥(adjointGroup .E7 F))) :
    ∃ g : ↥(adjointGroup .E7 F), A.map (MulAut.conj g).toMonoidHom ≤ perpLevi .E7 F ∧
      stdLayer (MulAut.conj g d) ≤ perpLevi .E7 F := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  obtain ⟨g, hA, hK⟩ := exists_conj_le_of_stdElt_of_levi .E7 Nat.prime_three (by norm_num)
    (M₀ := rootSpan .E7 F (perpRoots .E7)) hAel hd
    (fun J hJ E hE hEel hcard =>
      parabolicLevi_le_rootSpan_perpRoots_of_card hF hJ hE hEel (h6.trans hcard)) hT hT2 hTN
  refine ⟨g, fun z hz => Subgroup.mem_subgroupOf.2 (hA (Subgroup.mem_map_of_mem _ hz)),
    fun z hz => Subgroup.mem_subgroupOf.2 (hK (Subgroup.mem_map_of_mem _ hz))⟩

end Big

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
