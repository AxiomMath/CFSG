module

public import CFSG.GH74.QTGen4.U42.GSideCoordsExt
public import CFSG.GH74.QTGen4.U42.GSideB
public import CFSG.GH74.QTGen4.U42.PairExt
public import CFSG.GH74.QTGen4.U42.U0Core

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

variable {G : Type} [Group G] [Finite G] {T L V H I : Subgroup G}

theorem mem_T_iff_InD_extension (S : A5.Setting G T L V)
    (hE : ¬ Setting.PlainCase S) (m : ↥(L ⊔ T)) :
    (m : G) ∈ T ↔ InD (S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩) := by
  let mN : ↥(Subgroup.normalizer (V : Set G)) := ⟨(m : G), LT_le_normalizer S m.2⟩
  change (m : G) ∈ T ↔ InD (S.frame.ρ mN)
  constructor
  · intro hm
    exact S.frame.T_D mN hm
  · intro hD
    by_cases hs : (S.frame.ρ mN).sign = 1
    · exact S.mem_T_of_InK4 mN m.2 (InK4_of_InD _ hD hs)
    · have hodd : ∃ t : ↥(Subgroup.normalizer (V : Set G)),
          (t : G) ∈ T ∧ (S.frame.ρ t).sign ≠ 1 := by
        by_contra hn
        push Not at hn
        exact hE (fun t ht => InK4_of_InD _ (S.frame.T_D t ht) (hn t ht))
      obtain ⟨t, ht, hts⟩ := hodd
      have hK : InK4 (S.frame.ρ (mN * t⁻¹)) := by
        rw [map_mul, map_inv]
        exact InK4_mul_inv_of_odd _ hD hs _ (S.frame.T_D t ht) hts
      have hmT : ((mN * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ T :=
        S.mem_T_of_InK4 (mN * t⁻¹)
          ((L ⊔ T).mul_mem m.2 ((L ⊔ T).inv_mem ((le_sup_right : T ≤ L ⊔ T) ht))) hK
      have h := T.mul_mem hmT ht
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using h

private noncomputable def extCoordsRestrict {G : Type*} [Group G] {M K : Subgroup G}
    {Kc : Subgroup Mc} (e : ↥M ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (hK : K ≤ M)
    (hmem : ∀ m : ↥M, (m : G) ∈ K ↔ ((e m : Mof _) : Mc) ∈ Kc) : ↥K ≃* ↥Kc :=
  let hKc : Kc ≤ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
    fun _ _ => mem_Mof.mpr (Subgroup.mem_top _)
  ((Subgroup.subgroupOfEquivOfLe hK).symm.trans
    (restrictEquiv (K.subgroupOf M) (Kc.subgroupOf (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))) e
      (fun m => hmem m))).trans (Subgroup.subgroupOfEquivOfLe hKc)

theorem pairCore_extension (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I)
    (hE : ¬ Setting.PlainCase S) : PairCore H (H ⊓ (L ⊔ T)) T (pCoreOf 2 H) := by
  obtain ⟨e, he⟩ := exists_coords_extension S D.V_eq hE
  have hB : ∀ m : ↥(L ⊔ T), (m : G) ∈ H ⊓ (L ⊔ T) ↔ ((e m : Mof _) : Mc) ∈ Bhc := by
    intro m
    have hfix := mem_H_iff_fix_four S hH D m
    rw [← IsCoords.right he m] at hfix
    change ((m : G) ∈ H ∧ (m : G) ∈ L ⊔ T) ↔ ((e m : Mof _) : Mc).right 4 = 4
    exact ⟨fun hm => hfix.mp hm.1, fun hm => ⟨hfix.mpr hm, m.2⟩⟩
  have hT : ∀ m : ↥(L ⊔ T), (m : G) ∈ T ↔ ((e m : Mof _) : Mc) ∈ Thc := by
    intro m
    change (m : G) ∈ T ↔ InD (((e m : Mof _) : Mc).right)
    rw [IsCoords.right he m]
    exact mem_T_iff_InD_extension S hE m
  have hcardB : Nat.card ↥(H ⊓ (L ⊔ T)) = 384 :=
    (Nat.card_congr (extCoordsRestrict e inf_le_right hB).toEquiv).trans card_Bhc
  have hcardT : Nat.card T = 128 :=
    (Nat.card_congr (extCoordsRestrict e le_sup_right hT).toEquiv).trans card_Thc
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
