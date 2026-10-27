module

public import CFSG.GH74.QTGen4.U42.GSideB
public import CFSG.GH74.QTGen4.U42.U0Core
public import CFSG.GH74.QTGen4.U42.PairExt

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

private noncomputable def coordsRestrict {G : Type*} [Group G] {M K : Subgroup G}
    {Kc : Subgroup Mc} (e : ↥M ≃* Mof (alternatingGroup (Fin 5)))
    (hK : K ≤ M) (hKc : Kc ≤ Mof (alternatingGroup (Fin 5)))
    (hmem : ∀ m : ↥M, (m : G) ∈ K ↔ ((e m : Mof _) : Mc) ∈ Kc) : ↥K ≃* ↥Kc :=
  ((Subgroup.subgroupOfEquivOfLe hK).symm.trans
    (restrictEquiv (K.subgroupOf M) (Kc.subgroupOf (Mof (alternatingGroup (Fin 5)))) e
      (fun m => hmem m))).trans (Subgroup.subgroupOfEquivOfLe hKc)

variable {G : Type} [Group G] [Finite G] {T L V H I : Subgroup G}

theorem pairCore_plain (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I)
    (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) :
    PairCore H (H ⊓ (L ⊔ T)) T (pCoreOf 2 H) := by
  obtain ⟨e, he⟩ := exists_coords_plain S D.V_eq hP
  have hBc : Bc ≤ Mof (alternatingGroup (Fin 5)) := by
    intro x hx
    exact mem_Mof.mpr (Equiv.Perm.mem_alternatingGroup.mpr hx.1)
  have hTc : Tc ≤ Mof (alternatingGroup (Fin 5)) := by
    intro x hx
    exact mem_Mof.mpr (Equiv.Perm.mem_alternatingGroup.mpr (sign_of_InK4 _ hx))
  have hB : ∀ m : ↥(L ⊔ T), (m : G) ∈ H ⊓ (L ⊔ T) ↔ ((e m : Mof _) : Mc) ∈ Bc := by
    intro m
    have hsign : ((e m : Mof _) : Mc).right.sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (mem_Mof.mp (e m).2)
    have hfix := mem_H_iff_fix_four S hH D m
    rw [← IsCoords.right he m] at hfix
    change ((m : G) ∈ H ∧ (m : G) ∈ L ⊔ T) ↔
      (((e m : Mof _) : Mc).right.sign = 1 ∧ ((e m : Mof _) : Mc).right 4 = 4)
    exact ⟨fun hm => ⟨hsign, hfix.mp hm.1⟩, fun hm => ⟨hfix.mpr hm.2, m.2⟩⟩
  have hT : ∀ m : ↥(L ⊔ T), (m : G) ∈ T ↔ ((e m : Mof _) : Mc) ∈ Tc := by
    intro m
    change (m : G) ∈ T ↔ InK4 (((e m : Mof _) : Mc).right)
    rw [IsCoords.right he m]
    exact ⟨fun hm => hP ⟨(m : G), LT_le_normalizer S m.2⟩ hm,
      fun hm => S.mem_T_of_InK4 ⟨(m : G), LT_le_normalizer S m.2⟩ m.2 hm⟩
  have hcardB : Nat.card ↥(H ⊓ (L ⊔ T)) = 192 :=
    (Nat.card_congr (coordsRestrict e inf_le_right hBc hB).toEquiv).trans card_Bc
  have hcardT : Nat.card ↥T = 64 :=
    (Nat.card_congr (coordsRestrict e le_sup_right hTc hT).toEquiv).trans card_Tc
  have hTH : T ≤ H := S.T_le_H hH
  have hsyl := S.sylow_of_le hTH
  refine ⟨F7.isSylowTwoOf_pCoreOf_le hsyl, le_inf hTH le_sup_right, inf_le_left,
    ?_, S.isPGroup_T, hsyl.2.2, ?_, ?_⟩
  · intro h hh u hu
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) u).mp hu
  · intro h hh hc
    have hchar : CharTwo H := S.charTwo_of_inH ⟨hTH, hH.1.2⟩
    exact hchar ⟨hh, Subgroup.mem_centralizer_iff.mpr (fun u hu => (hc u hu).symm)⟩
  · rw [card_H_eq_three_mul_B S hH D, hcardB, hcardT]

end CFSG.GH74.QTGen4.U42
