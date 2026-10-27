module

public import CFSG.Quasithin.H13.L32AC32e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace CtxS

variable {K : Subgroup G} {t₀ : G} (C : CtxS T L V H K t₀)
include C

theorem conj_l1_F4 (h1332 : Stmt13_3_2_F4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    t₀⁻¹ * y * t₀ ∈ l1 T L V ∧ (t₀⁻¹ * y * t₀) ^ 3 = 1 := by
  have hTl1 := Setting147.T_le_N_l1_F4 C.S h1332
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (hTl1 (inv_mem C.ht₀)) y).mp hy
    simpa using this
  · rw [show (t₀⁻¹ * y * t₀) ^ 3 = t₀⁻¹ * y ^ 3 * t₀ by rw [pow_three, pow_three]; group, hy3]
    group

theorem mk_ne_one_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x : G}
    (hx : x ∈ l1 T L V) (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, Setting147.l1H' C.S hx⟩ ≠ 1 := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxO : x ∉ pCoreOf 2 (l1 T L V) := by
    intro h
    rw [← hl1] at h
    have hxt := S14.pCoreOf_L1_le_F4 h
    have hle : V ≤ fsuV1 T V := fun v hv =>
      hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V_F4, S14.card_V1_F4] at this
    omega
  intro h
  apply hxO
  refine pCoreOf_inf_le_of_le (Setting147.l1H' C.S) ⟨?_, hx⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf] at h
  exact h

end CtxS

namespace CtxL2

variable {K : Subgroup G} {t₀ : G} {n : ℕ} (C : CtxL2 T L V H K t₀ n)
include C

theorem l1_le_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : l1 T L V ≤ conjClosure K T := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa using mem_conjClosure C.ht₀ hk
  have hle : l1 T L V ≤ conjClosure K T ⊔ pCoreOf 2 H := by
    rw [← hl1]
    refine l1_le_of_cube_F4 S14 fun y hyL hy3 => ?_
    have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
    obtain ⟨k₁, hk₁K, k₂, hk₂K, he, -⟩ := C.decomp hA37 hy hy3
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        modO2Image H (conjClosure K T) := by
      have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image H A ≤ modO2Image H B :=
        fun h => Subgroup.map_mono fun _ hz => h hz
      rw [he]
      exact mul_mem (hmono (le_conjClosure K T) hk₁K) (hmono hKt hk₂K)
    obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp hmem
    have hq : (a : G)⁻¹ * y ∈ pCoreOf 2 H := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hae
      simpa using hae
    have e : y = (a : G) * ((a : G)⁻¹ * y) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hq)
  have h2 := C58.oTwoUpper_le_of_le_sup hle (pCoreOf_isPGroup 2 H)
    C.pCoreOf_le_normalizer_conjClosure
  rwa [A4.oTwoUpper_oTwoUpper] at h2

theorem k_ne_one_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {x : G} (hx : x ∈ l1 T L V) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    {k₁ k₂ : ↥H ⧸ CFSG.pCore 2 ↥H} (hk₁K : k₁ ∈ modO2Image H K)
    (hk₂K : k₂ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)))
    (he : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, Setting147.l1H' C.S hx⟩ = k₁ * k₂) :
    k₁ ≠ 1 ∧ k₂ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxH : x ∈ H := Setting147.l1H' C.S hx
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ with htb
  set xb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ with hxb
  have hxb1 : xb ≠ 1 := C.mk_ne_one_F4 h1222 h1332 h1334 hx hfpf
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hx3)
  obtain ⟨hxK, hxK'⟩ := C.mk_mem_normalizers hx hx3
  have hLN : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L C.S.hyp.hyp.h13 L C.S.hyp.hyp.h13.faithful).2.1.1
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hxbL : xb ∈ modO2Image H L := mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hl1L hx, rfl⟩
  have hzH : t₀ * x * t₀⁻¹ ∈ H := mul_mem (mul_mem C.ht₀H hxH) (inv_mem C.ht₀H)
  have hze : tb * xb * tb⁻¹ = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀ * x * t₀⁻¹, hzH⟩ := by
    rw [htb, hxb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hzL : tb * xb * tb⁻¹ ∈ modO2Image H L := by
    rw [hze]
    exact mem_modO2Image'.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp (hLN C.ht₀) x).mp (hl1L hx),
      rfl⟩
  have hz3 : (tb * xb * tb⁻¹) ^ 3 = 1 := by
    rw [show tb * xb * tb⁻¹ = MulAut.conj tb xb from rfl, ← map_pow, hxb3, map_one]
  have hz1 : tb * xb * tb⁻¹ ≠ 1 := fun h => hxb1 (by
    have := congrArg (fun z => tb⁻¹ * z * tb) h
    simpa [mul_assoc] using this)
  have h9 : ¬ 9 ∣ Nat.card ↥(modO2Image H L) := fun h =>
    not_nine_dvd_card_L_F4 h1222 h1332 h1334 C.S (h.trans card_modO2Image_dvd_card)
  have htt : tb * tb ∈ Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have := mk_mem_normalizer (y := ⟨t₀, C.ht₀H⟩ * ⟨t₀, C.ht₀H⟩) C.hKH C.sq_mem
    rwa [map_mul] at this
  refine ⟨fun hk₁1 => ?_, fun hk₂1 => ?_⟩
  ·
    rw [hk₁1, one_mul] at he
    have hxKb' : xb ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := he ▸ hk₂K
    have hxnK : xb ∉ modO2Image H K := fun h => hxb1 (C.eq_one_of_mem_kb_kt hA37 h hxKb')
    have hzK : tb * xb * tb⁻¹ ∈ modO2Image H K := by
      rw [← C.kb'_eq] at hxKb'
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hxKb'
      have e : tb * xb * tb⁻¹ = (tb * tb) * m * (tb * tb)⁻¹ := by
        rw [← hme, htb]
        simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp htt m).mp hm
    exact h9 (nine_dvd_card hxbL hxK hxb3 hxnK hzL hzK hz3 hz1)
  ·
    rw [hk₂1, mul_one] at he
    have hxKb : xb ∈ modO2Image H K := he ▸ hk₁K
    have hxnK' : xb ∉ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := fun h =>
      hxb1 (C.eq_one_of_mem_kb_kt hA37 hxKb h)
    have hzK' : tb * xb * tb⁻¹ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := by
      rw [← C.kb'_eq]
      exact Subgroup.mem_map.mpr ⟨xb, hxKb, by
        rw [htb]
        simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]⟩
    exact h9 (nine_dvd_card hxbL hxK' hxb3 hxnK' hzL hzK' hz3 hz1)

end CtxL2

end CFSG.Quasithin.H13.L32A.C
