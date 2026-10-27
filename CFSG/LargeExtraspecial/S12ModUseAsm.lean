module

public import CFSG.LargeExtraspecial.S12ModUse
public import CFSG.LargeExtraspecial.S12ModDWDefs
public import CFSG.LargeExtraspecial.S12InspFamESp
public import CFSG.LargeExtraspecial.S12InspFamER3b
public import CFSG.LargeExtraspecial.S12InspPSUMain
public import CFSG.LargeExtraspecial.S12InspFamJ2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_lieModel_fieldF (hF : DW.DW2FieldInput) {g : G} {t : S.O}
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) {τ : StatedLieTag} {n f : ℕ} (hf : 2 ≤ f)
    (hτ : (τ = .PSL ∧ 3 ≤ n) ∨ (τ = .PSp ∧ 3 ≤ n) ∨
      ((τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧ 4 ≤ n) ∨
      (n = 0 ∧ τ ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag)))
    (h : LieModel (S.Xbar12 g) τ n 2 f) : False :=
  hF (S.Xbar12 g) τ n f hf hτ h _ (isTransClass34_Ebar12 ht htA hS)

end Setting

theorem insp5Input_of_familiesF (hF : DW.DW2FieldInput) (hL : InspPSL) (hSp : InspPSp)
    (hO : InspPOmega) (hE : InspExcNondeg) (hU : InspU33) (hA6 : InspAlt6) (hJ : InspJ2)
    (hSym : InspSym) (hSpT : InspSpTv) (hOT : InspOTv) (hPSU : InspPSU) (hF3 : InspF3)
    (hFi : InspFi) : Insp5Input := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred hcls
  have hfam : ∀ {P : ∀ (X : Type) [Group X], Set X → Prop}, InspFor P →
      P (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) → _ := fun hP hx =>
    hP G S g t haQ hne hn ht htA hS hred hx
  have hfield := fun {τ n f} hf hτ h =>
    Setting.false_of_lieModel_fieldF (τ := τ) (n := n) (f := f) hF ht htA hS hf hτ h
  rcases hcls with ⟨hnd, hout⟩ | ⟨hdeg, hfis⟩
  · have hND := Setting.isNondeg12_iff_inspNondeg.mp hnd
    rcases hout with ⟨m, f, hm, hf, h⟩ | ⟨m, f, hm, hf, h⟩ | ⟨m, f, hm, hf, h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, τ, hτ, h⟩ | h | h | h
    · rcases Nat.lt_or_ge f 2 with hf1 | hf2
      · obtain rfl : f = 1 := by omega
        exact hfam hL ⟨hND, m, hm, h⟩
      · exact (hfield hf2 (Or.inl ⟨rfl, hm⟩) h).elim
    · rcases Nat.lt_or_ge f 2 with hf1 | hf2
      · obtain rfl : f = 1 := by omega
        exact hfam hSp ⟨hND, m, hm, h⟩
      · exact (hfield hf2 (Or.inr (Or.inl ⟨rfl, hm⟩)) h).elim
    · rcases Nat.lt_or_ge f 2 with hf1 | hf2
      · obtain rfl : f = 1 := by omega
        exact hfam hO ⟨hND, m, hm, h⟩
      · rcases h with h | h
        · exact (hfield hf2 (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hm⟩))) h).elim
        · exact (hfield hf2 (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hm⟩))) h).elim
    · exact (hfield hf (Or.inr (Or.inr (Or.inr ⟨rfl, by decide⟩))) h).elim
    · rcases Nat.lt_or_ge f 2 with hf1 | hf2
      · obtain rfl : f = 1 := by omega
        exact hfam hE ⟨hND, τ, hτ, h⟩
      · refine (hfield hf2 (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))) h).elim
        revert hτ
        cases τ <;> decide
    · exact hfam hU h
    · exact hfam hA6 h
    · exact hfam hJ h
  · have hND : ¬ InspNondeg (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) := fun h =>
      hdeg (Setting.isNondeg12_iff_inspNondeg.mpr h)
    rcases hfis with h | h | h | h | h | h
    · exact hfam hSym ⟨hND, h⟩
    · exact hfam hSpT ⟨hND, h⟩
    · exact hfam hOT ⟨hND, h⟩
    · exact hfam hPSU ⟨hND, h⟩
    · exact hfam hF3 ⟨hND, h⟩
    · exact hfam hFi ⟨hND, h⟩

theorem insp5Input_of_residualN
    (hDW : DW.DW2OutInspectionInputN) (hL : InspPSL4)
    (hSp : InspPSp) (hO : InspPOmega) : Insp5Input :=
  insp5Input_of_familiesF hDW.field (inspPSL_of hL) hSp hO
    (inspExcNondeg_of hDW.moduleD4 hDW.moduleExc) inspU33 inspAlt6 inspJ2 inspSym
    (inspSpTv_of inspSpTv3) (inspOTv_of inspOTv3) inspPSU (inspF3_of_inspPSU inspPSU)
    (inspFi_of S12Tri.fischerTrialityInput (inspSpTv_of inspSpTv3) (inspOTv_of inspOTv3) inspPSU
      (inspF3_of_inspPSU inspPSU))

end CFSG.LargeExtraspecial
