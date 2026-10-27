module

public import CFSG.GH74.QTGen4.U42.StubA4h
public import CFSG.GH74.QTGen4.U42.AmalgamGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5
public import CFSG.GH74.QTGen4.U42.GSidePairCore
public import CFSG.GH74.QTGen4.U42.GSidePairData
public import CFSG.GH74.QTGen4.U42.ModelPairCore

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5
open CFSG.Quasithin.H13.F431.U42 U42F431

private theorem plainInK4_sign : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ.sign = 1 := by
  rintro σ (rfl | rfl | rfl | rfl) <;> decide +kernel

private theorem plain_mem_Tc (x : Mc) : x ∈ Tc ↔ InK4 x.right := Iff.rfl

private theorem plain_mem_Bc (x : Mc) : x ∈ Bc ↔ x.right.sign = 1 ∧ x.right 4 = 4 := Iff.rfl

private theorem plain_InK4_of_mem_U0 {x : Mc} (hx : x ∈ U0) : InK4 x.right :=
  (show _ ∧ InK4 x.right from hx).2

section Assembly

variable {G : Type} [Group G] [Finite G] {T' L V : Subgroup G}

theorem amalgam_iso_plain (S : A5.Setting G T' L V) {H I : Subgroup G} (hH : H ∈ S.Hz)
    (D : Data13515 S H I) (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) :
    Nonempty ((RankTwoAmalgam.ofSubgroups H (L ⊔ T')).Iso (RankTwoAmalgam.ofSubgroups P1 P2)) := by
  obtain ⟨e, hco, hU, hB, hT, hUB⟩ := pairData_plain S hH D hP
  obtain ⟨eY, hY1, hY2⟩ := exists_model_coords_plain
  have hB' : ∀ g : ↥P2, (g : Y) ∈ P1 ↔ ((eY g : Mof (alternatingGroup (Fin 5))) : Mc) ∈ Bc := by
    intro g
    have h1 : (g : Y) ∈ P1 ↔ (g : Y) ∈ B0 := ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
    rw [h1, model_B0_iff g]
    have hs : ((eY g : Mof (alternatingGroup (Fin 5))) : Mc).right.sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 (mem_Mof.1 (eY g).2)
    rw [plain_mem_Bc, hY2 g]
    rw [hY2 g] at hs
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  have hT' : ∀ g : ↥P2, (g : Y) ∈ T ↔ ((eY g : Mof (alternatingGroup (Fin 5))) : Mc) ∈ Tc := by
    intro g
    rw [model_T_iff g, plain_mem_Tc, hY2 g]
  have hU' := model_U_iff eY hY1 hY2
  have hU0R : U0 ≤ Mof (alternatingGroup (Fin 5)) := fun x hx =>
    mem_Mof.2 (Equiv.Perm.mem_alternatingGroup.2 (plainInK4_sign _ (plain_InK4_of_mem_U0 hx)))
  exact amalgam_iso_of_coords hU0R e eY hB hB' hT hT' hU hU' (pairCore_plain S hH D hP)
    model_pairCore hUB

theorem amalgam_U42_plain (S : A5.Setting G T' L V) {H I : Subgroup G} (hH : H ∈ S.Hz)
    (D : Data13515 S H I) (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H (L ⊔ T')) (IsLieOverTwo .PSU 4 1) :=
  ⟨Y, inferInstance, lieModel_Y, T, P1, P2, isYAmalgamPair, amalgam_iso_plain S hH D hP⟩

end Assembly

end CFSG.GH74.QTGen4.U42
