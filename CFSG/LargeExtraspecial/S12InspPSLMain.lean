module

public import CFSG.LargeExtraspecial.S12InspPSLCaseH4
public import CFSG.LargeExtraspecial.S12InspP5Main
public import CFSG.LargeExtraspecial.SL4ModMain
public import CFSG.LargeExtraspecial.S12InspPSLGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL
open CFSG.Blueprint

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

include P in
theorem case1 (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width)
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hred : ¬ S.IsReducible12) : S.S12Case1 g t := by
  obtain ⟨haT, -⟩ := S.timmesfeld_12_6 haQ hne ht htA
  rcases P.eq_of_mem_commSpace haT (S.s12_cl_ne_zero_of_conj haQ hne) with ha | ha | ha
  · exact P.case1_of_eq_c haQ hne hn ht htA hS hred ha
  · exact P.swap.case1_of_eq_c haQ hne hn ht htA hS hred ha
  · exact P.case1_of_eq_add haQ hne hn ht htA hS hred ha

end PSLPair

theorem psl_actX12_injective (g : G) : Function.Injective (S.actX12 g) :=
  S.O.subtype_injective.comp (S.Xbar12 g).subtype_injective

theorem psl_nonempty_mulEquiv_sl_of_lieModel {X : Type} [Group X] {m : ℕ}
    (h : LieModel X .PSL m 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two m K
      (by rw [hK]; norm_num))⟩
  all_goals exact absurd ht (by decide)

theorem psl_false_of_irred_four {g : G} (hw : S.width = 4)
    (hL : LieModel (S.Xbar12 g) .PSL 4 2 1)
    (hirr : ∀ U : Submodule (ZMod 2) S.Qt, IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤) : False := by
  obtain ⟨φ⟩ := psl_nonempty_mulEquiv_sl_of_lieModel hL
  have hdim : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  set H := (S.Xbar12 g).map S.O.subtype
  have ψ : H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ((S.Xbar12 g).equivMapOfInjective S.O.subtype (subtype_injective _)).symm.trans φ
  obtain ⟨W, hW0, hWt, hWH⟩ := SL4Mod.s12SL4ModuleInput S.Qt hdim H ⟨ψ⟩
  rcases hirr W (fun x w hw => hWH _ ⟨x, x.2, rfl⟩ w hw) with h | h
  · exact hW0 h
  · exact hWt h

end Setting

theorem insp4PlusResidual2 : Insp4PlusResidual2 := by
  intro G _ _ _ S g t haQ hne hw _ _ _ ht htA hS hred hnd hL
  rcases Setting.irred_or_pslPair ht htA hS hred hnd with hirr | hP
  · exact (Setting.psl_false_of_irred_four hw hL hirr).elim
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.case1 haQ hne (by omega) ht htA hS hred)

end CFSG.LargeExtraspecial
