module

public import CFSG.ClassicalInvolution.Q3.Q3B1
public import CFSG.ClassicalInvolution.Q3.Q3UFix

public section

namespace CFSG.ClassicalInvolution.Q3.Q3B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification CFSG.LocalCores CFSG
open scoped commutatorElement

section Comp

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem nontrivial_of_isQuasisimple {G : Type} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    Nontrivial G := by
  have : Nontrivial (G ⧸ Subgroup.center G) := h.2.toNontrivial
  exact (QuotientGroup.mk_surjective (s := Subgroup.center G)).nontrivial

omit [Finite Y] in
theorem not_isSolvable_of_isComponentOf {T : Subgroup Y} (hT : IsComponentOf T ⊤) :
    ¬ Group.IsSolvable T := by
  intro hs
  have := nontrivial_of_isQuasisimple hT.2.2
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial T).ne hT.2.2.1

theorem isComponentOf_le_centralizer_pCore_not_le {T : Subgroup Y} (hT : IsComponentOf T ⊤) :
    T ≤ Subgroup.centralizer ((pCore 2 Y : Subgroup Y) : Set Y) ∧ ¬ T ≤ pCore 2 Y := by
  have hn : (pCore 2 Y).Normal := pCore_normal
  have hnil : Group.IsNilpotent (pCore 2 Y) := IsPGroup.isNilpotent pCore_isPGroup
  have hsub : (pCore 2 Y).IsSubnormal := hn.isSubnormal
  refine ⟨?_, fun hle => not_isSolvable_of_isComponentOf hT ?_⟩
  · have h := (component_solvable_centralizer (inferInstance : Group.IsSolvable (pCore 2 Y))
      hsub).1 T ((isComponent_iff_open T).mpr hT)
    rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  · have := IsPGroup.isNilpotent (pCore_isPGroup.to_le hle)
    infer_instance

theorem eq_top_of_isComponentOf_of_isQuasisimple {T : Subgroup Y} (hT : IsComponentOf T ⊤)
    (hY : CFSG.Open.IsQuasisimple Y) : T = ⊤ := by
  have hTop : IsComponent (⊤ : Subgroup Y) :=
    (isComponent_iff_open ⊤).mpr ⟨le_top, IsSubnormal.refl ⊤,
      Components.quasisimple_of_equiv Subgroup.topEquiv hY⟩
  rcases distinct_components_commute ((isComponent_iff_open T).mpr hT) hTop with h | h
  · exact h
  · exfalso
    refine not_forall_commute_of_isComponent hT fun x hx a ha => ?_
    have hmem : ⁅x, a⁆ ∈ ⁅T, (⊤ : Subgroup Y)⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_top a)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm

end Comp

section Equiv


theorem solvableMemberInnerTightConn_of_qs3Comp (h : QuasisimpleConnected3Comp) :
    SolvableMemberInnerTightConn := by
  intro Y _ _ hBelow hO z L hz T hT hTL hgen hconn hTz
  have hΛ : InClass3 (conjClass L) := inClass3_conjClass hz hgen
  have hns : ¬ Group.IsSolvable Y := fun hs =>
    not_isSolvable_of_isComponentOf hT (inferInstance : Group.IsSolvable (T : Subgroup Y))
  obtain ⟨hTC, hTnle⟩ := isComponentOf_le_centralizer_pCore_not_le hT
  have hC : ¬ Subgroup.centralizer ((pCore 2 Y : Subgroup Y) : Set Y) ≤ pCore 2 Y :=
    fun hle => hTnle (hTC.trans hle)
  have hqs := h Y hBelow hO (conjClass L) hΛ hconn hns hC
  have hT' : T = ⊤ := eq_top_of_isComponentOf_of_isQuasisimple hT hqs
  rw [hT']
  exact le_sup_of_le_left le_top

theorem solvableMemberInnerTight_of_qs3Comp (h : QuasisimpleConnected3Comp) :
    SolvableMemberInnerTight :=
  solvableMemberInnerTight_of_conn (solvableMemberInnerTightConn_of_qs3Comp h)

end Equiv

section Iff


theorem solvableMemberInnerTight_iff (hM : M11Facts) :
    SolvableMemberInnerTight ↔ QuasisimpleConnected3Comp :=
  ⟨quasisimpleConnected3Comp_of_tight hM, solvableMemberInnerTight_of_qs3Comp⟩

end Iff

end CFSG.ClassicalInvolution.Q3.Q3B
