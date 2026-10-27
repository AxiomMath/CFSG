module

public import CFSG.LargeExtraspecial.A2ModNDefs
public import CFSG.LargeExtraspecial.A2ModD4Defs
public import CFSG.LargeExtraspecial.S12InspSpOOmega
public import CFSG.LargeExtraspecial.S12InspFamMain
public import CFSG.LargeExtraspecial.S12InspPSLMain
public import CFSG.LargeExtraspecial.S12InspSpOMod
public import CFSG.LargeExtraspecial.S3bTenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem rootClass_Xbar12 {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hnd : S.IsNondeg12 g) :
    A2Mod.RootClass (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) :=
  ⟨isTransClass34_Ebar12 ht htA hS, isNondeg12_iff_inspNondeg.mp hnd,
    s12_center_eq_bot hS.center_trivial, s12_normal_pGroup_eq_bot noNormalTwo_Xbar12⟩

theorem a2Action_Xbar12 (g : G) :
    A2Mod.A2Action (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) S.q (S.actX12 g) :=
  ⟨S.q_nondegenerate, psl_actX12_injective g, fun x v => psl_q_apply (x : S.O) v,
    fun _ hd => isTypeA_of_mem_Ebar12 hd⟩

theorem psl_false_of_irred (hML : S12PSLModuleInputN) {g : G} {t : S.O} (hn : 5 ≤ S.width)
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hnd : S.IsNondeg12 g) {m : ℕ} (hm : 4 ≤ m)
    (hL : LieModel (S.Xbar12 g) .PSL m 2 1)
    (hirr : ∀ U : Submodule (ZMod 2) S.Qt, IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤) : False := by
  have h := hML (S.Xbar12 g) m hm hL _ (rootClass_Xbar12 ht htA hS hnd) S.Qt S.q (S.actX12 g)
    (a2Action_Xbar12 g) fun W hW => hirr W hW
  rw [S.finrank_Qt_eq_two_mul_width] at h
  omega

theorem spo_false_of_irred_sp (hML : S12SpModuleInputN) {g : G} {t : S.O} (hn : 5 ≤ S.width)
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hnd : S.IsNondeg12 g) {m : ℕ} (hm : 3 ≤ m)
    (hL : LieModel (S.Xbar12 g) .PSp m 2 1)
    (hirr : ∀ U : Submodule (ZMod 2) S.Qt, IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤) : False := by
  have h := hML (S.Xbar12 g) m hm hL _ (rootClass_Xbar12 ht htA hS hnd) S.Qt S.q (S.actX12 g)
    (a2Action_Xbar12 g) fun W hW => hirr W hW
  rw [S.finrank_Qt_eq_two_mul_width] at h
  omega

theorem spo_width_eq_of_irred_omega' (hML : S12OmegaModuleInputN) {g : G} {t : S.O}
    (hn : 5 ≤ S.width) (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hnd : S.IsNondeg12 g) {m : ℕ} (hm : 4 ≤ m)
    (hL : LieModel (S.Xbar12 g) .POmegaPlus m 2 1 ∨ LieModel (S.Xbar12 g) .POmegaMinus m 2 1)
    (hirr : ∀ U : Submodule (ZMod 2) S.Qt, IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤) :
    S.width = m := by
  have h := hML (S.Xbar12 g) m hm hL _ (rootClass_Xbar12 ht htA hS hnd) S.Qt S.q (S.actX12 g)
    (a2Action_Xbar12 g) fun W hW => hirr W hW
  rw [S.finrank_Qt_eq_two_mul_width] at h
  omega

theorem false_of_lieModel_exceptional' (hD4 : DW.DW2ModuleInputD4) (hE : S12ExcModuleInputN)
    {g : G} {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hnd : S.IsNondeg12 g) {τ : StatedLieTag}
    (hτ : τ ∈ ({.trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (h : LieModel (S.Xbar12 g) τ 0 2 1) : False := by
  have hR := rootClass_Xbar12 ht htA hS hnd
  have hA := a2Action_Xbar12 (S := S) g
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨htX, h1, h2, h3⟩ := spo_t_mem ht htA
    have := hD4 (S.Xbar12 g) h S.Qt (S.actX12 g) (psl_actX12_injective g) _ h1 h2
    omega
  · exact hE _ .F4 (by decide) h _ hR S.Qt S.q _ hA
  · exact hE _ .E6 (by decide) h _ hR S.Qt S.q _ hA
  · exact hE _ .twistedE6 (by decide) h _ hR S.Qt S.q _ hA
  · exact hE _ .E7 (by decide) h _ hR S.Qt S.q _ hA
  · exact hE _ .E8 (by decide) h _ hR S.Qt S.q _ hA

end Setting

theorem inspPSL4_ofN (hML : S12PSLModuleInputN) : InspPSL4 := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, hL⟩ := h
  have hnd := Setting.isNondeg12_iff_inspNondeg.mpr hND
  rcases Setting.irred_or_pslPair ht htA hS hred hnd with hirr | hP
  · exact (Setting.psl_false_of_irred hML hn ht htA hS hnd hm hL hirr).elim
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.case1 haQ hne (by omega) ht htA hS hred)

theorem inspPSp_ofN (hML : S12SpModuleInputN) : InspPSp := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, hL⟩ := h
  have hnd := Setting.isNondeg12_iff_inspNondeg.mpr hND
  rcases Setting.irred_or_pslPair ht htA hS hred hnd with hirr | hP
  · exact (Setting.spo_false_of_irred_sp hML hn ht htA hS hnd hm hL hirr).elim
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.case1 haQ hne (by omega) ht htA hS hred)

theorem inspPOmega_ofN (hML : S12OmegaModuleInputN) (hFS : FSmith1977cOmegaInput) :
    InspPOmega := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, hL⟩ := h
  have hnd := Setting.isNondeg12_iff_inspNondeg.mpr hND
  rcases Setting.irred_or_pslPair ht htA hS hred hnd with hirr | hP
  · have hw := Setting.spo_width_eq_of_irred_omega' hML hn ht htA hS hnd hm hL hirr
    rw [← hw] at hL
    have hX := Setting.spo_Xbar12_map_eq_omegaGroup (by omega) hL
    have hM := Setting.spo_Mbar_map_eq_timmesfeldOmega (by omega) hX
    have h4 := (hFS G S (by omega) hM).1
    omega
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.case1 haQ hne (by omega) ht htA hS hred)

@[expose] def InspExcNondeg : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  InspNondeg X D ∧
    ∃ τ ∈ ({.trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag),
      LieModel X τ 0 2 1

theorem inspExcNondeg_of (hD4 : DW.DW2ModuleInputD4) (hE : S12ExcModuleInputN) :
    InspExcNondeg := by
  intro G _ _ _ S g t _ _ _ ht htA hS _ h
  obtain ⟨hND, τ, hτ, hX⟩ := h
  exact (Setting.false_of_lieModel_exceptional' hD4 hE ht htA hS
    (Setting.isNondeg12_iff_inspNondeg.mpr hND) hτ hX).elim

end CFSG.LargeExtraspecial
