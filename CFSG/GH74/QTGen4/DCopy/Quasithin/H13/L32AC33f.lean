module

public import CFSG.Quasithin.H13.L32AC33f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem mem_normalizer_l1_of_solvable_F4 (h29 : Thm14_7_29_F4) (S : Setting147 G T L V H)
    {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hX : Group.IsSolvable ↥X)
    (hLT : modO2Image H (l1 T L V ⊔ T) ≤ X) {β : ↥H}
    (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ X) :
    (β : G) ∈ Subgroup.normalizer (l1 T L V : Set G) := by
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  have hLTY : l1 T L V ⊔ T ≤ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    fun z hz => Subgroup.mem_map.mpr ⟨⟨z, hLTH hz⟩, hLT (mem_modO2Image'.mpr ⟨_, hz, rfl⟩), rfl⟩
  have hYM := h29 G T L V S.hyp _ hLTY ((Subgroup.map_subtype_le _).trans S.hz.2.1)
    (isSolvable_preimage hX)
  have hβY : (β : G) ∈ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    Subgroup.mem_map.mpr ⟨β, hβ, rfl⟩
  exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hYM hβY, Subgroup.le_normalizer (S.hz.2.1 β.2)⟩)

namespace CtxB

variable {K : Subgroup G} {t₀ : G} (C : CtxB T L V H K t₀)
include C

theorem mk_l1_mem_normalizer_szB12_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈ Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  refine mem_normalizer_sup'' (C.mk_l1_mem_normalizer_szB1_F4 h1222 h1332 h1334 hy hy3)
    (mem_normalizer_map_conj ?_)
  have hTl1 := Setting147.T_le_N_l1_F4 C.S h1332
  have hy' : t₀⁻¹ * y * t₀ ∈ l1 T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (hTl1 (inv_mem C.ht₀)) y).mp hy
    simpa using this
  have hy'3 : (t₀⁻¹ * y * t₀) ^ 3 = 1 := by
    rw [show (t₀⁻¹ * y * t₀) ^ 3 = t₀⁻¹ * y ^ 3 * t₀ by rw [pow_three, pow_three]; group, hy3]
    group
  have h1 := C.mk_l1_mem_normalizer_szB1_F4 h1222 h1332 h1334 hy' hy'3
  have e : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact h1

theorem mk_l1T_le_normalizer_szB12_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
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
      C.mk_l1_mem_normalizer_szB12_F4 h1222 h1332 h1334 hy hy3, rfl⟩
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
    (h1334 : A6.Stmt13_3_4_F4) :
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
  exact isSolvable_sup_of_le_normalizer' (C.mk_l1T_le_normalizer_szB12_F4 h1222 h1332 h1334)
    (C.isSolvable_szB12 hA37) hLTb

theorem mem_normalizer_l1_of_szB1_F4 (hA37 : A37ForSQTK) (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {β : ↥H}
    (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K) :
    (β : G) ∈ Subgroup.normalizer (l1 T L V : Set G) :=
  mem_normalizer_l1_of_solvable_F4 h29 C.S (C.isSolvable_szX_F4 hA37 h1222 h1332 h1334) le_sup_right
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left hβ))

end CtxB

end CFSG.Quasithin.H13.L32A.C
