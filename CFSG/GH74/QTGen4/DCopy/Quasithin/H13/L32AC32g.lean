module

public import CFSG.Quasithin.H13.L32AC32g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.SBc5SL2

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem isSolvable_l1T_star_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) : Group.IsSolvable ↥(modO2Image H (l1 T L V ⊔ T)) := by
  have hLT : Group.IsSolvable ↥(l1 T L V ⊔ T) := by
    rw [sup_comm]
    exact isSolvable_of_isTwoThree (isTwoThree_card_sup (relIndex_l1_F4 h1222 h1332 h1334 S.hyp)
      S.hyp.fsu.sylow.1 (Setting147.T_le_N_l1_F4 S h1332))
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  have : Group.IsSolvable ↥((l1 T L V ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLTH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.isSolvable_of_surjective
    (f := MonoidHom.subgroupMap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      ((l1 T L V ⊔ T).subgroupOf H)) (MonoidHom.subgroupMap_surjective _ _)

namespace CtxL2

variable {K : Subgroup G} {t₀ : G} {n : ℕ} (C : CtxL2 T L V H K t₀ n)
include C

theorem mem_normalizer_szS1_of_inner_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1)
    {k : ↥H ⧸ CFSG.pCore 2 ↥H} (hkK : k ∈ modO2Image H K)
    (hk : ∀ m ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      m * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k * m * k⁻¹) :
    k ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image H A ≤ modO2Image H B :=
    fun h => Subgroup.map_mono fun _ hz => h hz
  have := isSolvable_l1T_star_F4 h1222 h1332 h1334 C.S
  have hP : Group.IsSolvable ↥(modO2Image H (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : _ ≤ modO2Image H (l1 T L V ⊔ T)))
      (Subgroup.inclusion_injective _)
  refine mem_normalizer_of_inner C.isPSL_kb
    (not_isSolvable_of_mem_cComp (modO2Image_mem_cComp C.hK)) C.center_kb inf_le_right hP
    C.isSylowIn_szS1 (fun s hs => ⟨hmono le_sup_right hs.1, Subgroup.le_normalizer hs.2⟩)
    ⟨hmono le_sup_left (mem_modO2Image'.mpr ⟨_, hy, rfl⟩), (C.mk_mem_normalizers hy hy3).1⟩
    hkK hk

theorem mk_l1_mem_normalizer_szS1_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (y : G) (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  obtain ⟨k₁, hk₁K, -, -, -, -, -, hk₁, -⟩ := C.decomp hA37 hy hy3
  have hk := C.mem_normalizer_szS1_of_inner_F4 h1222 h1332 h1334 hy hy3 hk₁K hk₁
  refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
  rw [hk₁ s hs.2]
  exact (Subgroup.mem_normalizer_iff.mp hk s).mp hs

theorem k₁_mem_szB1_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {y : G}
    (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) {k : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hkK : k ∈ modO2Image H K)
    (hk : ∀ m ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      m * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k * m * k⁻¹) :
    k ∈ szB1 T H K :=
  ⟨C.mem_normalizer_szS1_of_inner_F4 h1222 h1332 h1334 hy hy3 hkK hk, hkK⟩

theorem k₂_mem_szB2_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {y : G}
    (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) {k : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hkK : k ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)))
    (hk : ∀ m ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * m *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k * m * k⁻¹) :
    k ∈ (szB1 T H K).map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ with htb
  rw [← C.kb'_eq] at hkK hk
  obtain ⟨k', hk'K, rfl⟩ := Subgroup.mem_map.mp hkK
  obtain ⟨hy', hy'3⟩ := C.conj_l1_F4 h1332 hy hy3
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ =
      tb⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * tb := by
    rw [htb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hk'' : ∀ m ∈ modO2Image H K,
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ * m *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩)⁻¹ =
          k' * m * k'⁻¹ := by
    intro m hm
    have h1 := hk (tb * m * tb⁻¹) (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply] at h1
    rw [e]
    calc tb⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * tb * m *
          (tb⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * tb)⁻¹ =
          tb⁻¹ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
            (tb * m * tb⁻¹) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹) * tb := by group
      _ = tb⁻¹ * (tb * k' * tb⁻¹ * (tb * m * tb⁻¹) * (tb * k' * tb⁻¹)⁻¹) * tb := by rw [h1]
      _ = k' * m * k'⁻¹ := by group
  exact Subgroup.mem_map.mpr ⟨k', C.k₁_mem_szB1_F4 h1222 h1332 h1334 hy' hy'3 hk'K hk'', rfl⟩

end CtxL2

end CFSG.Quasithin.H13.L32A.C
