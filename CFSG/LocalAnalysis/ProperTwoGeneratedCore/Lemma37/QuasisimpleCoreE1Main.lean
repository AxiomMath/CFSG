module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Order
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1TypesBC

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem StarLift.nonempty_mulEquiv_alternating_of_caseC3
    (hu : StarLift B z u)
    (h : Setting J Q B) (hz : FourGen Q z) (T : Sylow 2 (quasiNormalizer u))
    {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hP : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u) {y : J}
    (hyT : y ∈ partCSylow T) (hy : y ∉ partCLeft T L ⊔ partCRight T L)
    (hyy : y * y ∈ partCRight T L)
    (hψ : Nonempty ((partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) ≃* QuaternionGroup 4))
    (hφ : Nonempty (partCRight T L ≃* QuaternionGroup 2)) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨S, y', x, m, d⟩ := hu.exists_e1Data h hz T hL hP hyT hy hyy hψ hφ
  by_cases htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s
  · exact d.nonempty_mulEquiv_alternating_of_typeD htype
  · exact (d.caseC3BCD_false_of_not_typeD htype).elim

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
