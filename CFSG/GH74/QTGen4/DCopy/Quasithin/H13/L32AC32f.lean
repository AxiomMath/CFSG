module

public import CFSG.Quasithin.H13.L32AC32f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace CtxS

variable {K : Subgroup G} {t₀ : G} (C : CtxS T L V H K t₀)
include C

theorem mk_l1_mem_normalizer_szB12_F4 (h1332 : Stmt13_3_2_F4)
    (hS1 : ∀ y (hy : y ∈ l1 T L V), y ^ 3 = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈ Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  refine mem_normalizer_sup'' (C.mk_l1_mem_normalizer_szB1 hS1 hy hy3)
    (mem_normalizer_map_conj ?_)
  obtain ⟨hy', hy'3⟩ := C.conj_l1_F4 h1332 hy hy3
  have h1 := C.mk_l1_mem_normalizer_szB1 hS1 hy' hy'3
  have e : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact h1

theorem mk_l1T_le_normalizer_szB12_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4)
    (hS1 : ∀ y (hy : y ∈ l1 T L V), y ^ 3 = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    modO2Image H (l1 T L V ⊔ T) ≤ Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hl1P : l1 T L V ≤ ((Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
          H.subtype := by
    rw [← hl1]
    refine l1_le_of_cube_F4 S14 fun y hyL hy3 => ?_
    have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
    exact Subgroup.mem_map.mpr ⟨⟨y, Setting147.l1H' C.S hy⟩,
      C.mk_l1_mem_normalizer_szB12_F4 h1332 hS1 hy hy3, rfl⟩
  have hTP : T ≤ ((Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
          H.subtype := fun t ht =>
    Subgroup.mem_map.mpr ⟨⟨t, C.hTH ht⟩, C.mk_T_mem_normalizer_szB12 ht, rfl⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_modO2Image'.mp hz
  obtain ⟨w', hw', hww⟩ := Subgroup.mem_map.mp (sup_le hl1P hTP hw)
  have : w' = w := Subtype.ext hww
  rw [← this]
  exact hw'

theorem isSolvable_szX_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4)
    (hS1 : ∀ y (hy : y ∈ l1 T L V), y ^ 3 = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    Group.IsSolvable ↥(szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) ⊔
      modO2Image H (l1 T L V ⊔ T)) := by
  have hLT : Group.IsSolvable ↥(l1 T L V ⊔ T) := by
    rw [sup_comm]
    exact isSolvable_of_isTwoThree (isTwoThree_card_sup (relIndex_l1_F4 h1222 h1332 h1334 C.S.hyp)
      C.S.hyp.fsu.sylow.1 (Setting147.T_le_N_l1_F4 C.S h1332))
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' C.S) C.hTH
  have : Group.IsSolvable ↥((l1 T L V ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLTH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hLTb : Group.IsSolvable ↥(modO2Image H (l1 T L V ⊔ T)) :=
    Group.isSolvable_of_surjective
      (f := MonoidHom.subgroupMap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ((l1 T L V ⊔ T).subgroupOf H)) (MonoidHom.subgroupMap_surjective _ _)
  exact isSolvable_sup_of_le_normalizer' (C.mk_l1T_le_normalizer_szB12_F4 h1222 h1332 h1334 hS1)
    (C.isSolvable_szB12 hA37) hLTb

theorem mem_normalizer_L_F4 (hA37 : A37ForSQTK) (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hS1 : ∀ y (hy : y ∈ l1 T L V), y ^ 3 = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    {β : ↥H} (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈
      szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) ⊔
        modO2Image H (l1 T L V ⊔ T)) :
    (β : G) ∈ Subgroup.normalizer (L : Set G) := by
  set X := szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) ⊔
    modO2Image H (l1 T L V ⊔ T) with hX
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' C.S) C.hTH
  have hLTY : l1 T L V ⊔ T ≤ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    fun z hz => Subgroup.mem_map.mpr ⟨⟨z, hLTH hz⟩,
      Subgroup.mem_sup_right (mem_modO2Image'.mpr ⟨_, hz, rfl⟩), rfl⟩
  have hYM := h29 G T L V C.S.hyp _ hLTY ((Subgroup.map_subtype_le _).trans C.S.hz.2.1)
    (isSolvable_preimage (C.isSolvable_szX_F4 hA37 h1222 h1332 h1334 hS1))
  exact hYM (Subgroup.mem_map.mpr ⟨β, hβ, rfl⟩)

theorem mem_nX_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {β : G} (hβH : β ∈ H)
    (hβL : β ∈ Subgroup.normalizer (L : Set G)) : β ∈ L32NSet14.nX T V := by
  have hVc : conjClosure (fsuV1 T V) L = V :=
    (h1334 G T L V C.S.hyp.hyp.h13 (C.S.hyp.hyp1223_F4 (stmt13_3_2_two_of_F4 h1332)).irrPlus).2.1
  have hβ1 : β ∈ Subgroup.normalizer (fsuV1 T V : Set G) := C.S.hz.2.1 hβH
  refine ⟨?_, hβ1⟩
  rw [← hVc]
  exact SzN16.mem_normalizer_conjClosure hβL hβ1

end CtxS

end CFSG.Quasithin.H13.L32A.C
