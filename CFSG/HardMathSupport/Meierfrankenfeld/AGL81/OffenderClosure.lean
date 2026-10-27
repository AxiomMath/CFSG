module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B1Offender

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem le_closure_transvectionsIn_of_le_solvable [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X Y A : Subgroup (MulAut V)} (hYX : Y ≤ X) (hAY : A ≤ Y) (hsolv : Group.IsSolvable ↥Y)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ Y → (Q.subgroupOf Y).Normal → IsPGroup 2 Q → Q = ⊥)
    (hA : IsFFStarOffender X A) : A ≤ Subgroup.closure (transvectionsIn X) := by
  have hAY' : IsFFStarOffender Y A := ⟨hAY, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hJY : Subgroup.closure (transvectionsIn Y) ≤ Y := B1.closure_transvectionsIn_le Y
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn Y)) :=
    B1.solvable_of_le hJY hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJY
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn Y))) =
      Subgroup.closure (transvectionsIn Y) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  obtain ⟨a, ha, haeq⟩ := hb.offender_structure hV hsolv hO2 (Nat.card A) A hAY' le_rfl
  rw [haeq]
  refine iSup₂_le fun H hH => (ha H hH).1.trans ?_
  have hHJ : H ≤ Subgroup.closure (transvectionsIn Y) := by
    rw [← hb.iSup_eq]
    exact le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH
  exact hHJ.trans (Subgroup.closure_mono fun t ht => ⟨hYX ht.1, ht.2⟩)

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81
