module

public import CFSG.Quasithin.H13.L32AL2f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A702
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2e

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

include X

theorem not_kb_le_ker_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : ¬ modO2Image (A6.g1 T V) K ≤ X.actDot.ker := by
  intro hle
  have C := X.C

  have hle2 : modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) ≤ X.actDot.ker := by
    rw [← C.kb'_eq]
    rintro _ ⟨a, ha, rfl⟩
    exact (MonoidHom.normal_ker _).conj_mem _ (hle ha) _

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨y, hyL, hy3, hfpfy⟩ := exists_l1_fpf_F4 C.S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
  have hyH : y ∈ A6.g1 T V := Setting147.l1H' C.S hy
  obtain ⟨k₁, hk₁K, k₂, hk₂K, he, -⟩ := C.decomp hA37 hy hy3
  have h1 : X.top.act ⟨y, hyH⟩ = 1 := by
    have : X.actDot (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) ⟨y, hyH⟩) = 1 := by
      rw [he]
      exact mul_mem (hle hk₁K) (hle2 hk₂K)
    exact this
  rw [X.top.act_eq_one_iff_comm] at h1
  have hVW := Setting147.inf_V_eq_F4 X.top.S h1222 h1332 h1334 X.top.hV₁W X.top.hWU X.top.hHW
  have hyV : y ∈ Subgroup.normalizer (V : Set G) := (S14.L1_le_X_F4 hyL).1
  have hle' : V ≤ fsuV1 T V := fun v hv => hfpfy v hv (by
    have hmem : y * v * y⁻¹ * v⁻¹ ∈ V ⊓ W :=
      Subgroup.mem_inf.mpr ⟨mul_mem ((Subgroup.mem_normalizer_iff.mp hyV v).mp hv) (inv_mem hv),
        h1 v (le_conjClosure V _ hv)⟩
    rw [hVW] at hmem
    exact hmem)
  have := Subgroup.card_le_of_le hle'
  rw [S14.card_V_F4, S14.card_V1_F4] at this
  omega

theorem actDot_injective_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Function.Injective X.actDot := by
  have C := X.C
  set N := X.actDot.ker with hN
  have hNn : N.Normal := MonoidHom.normal_ker _

  have h1 : ∀ a ∈ modO2Image (A6.g1 T V) K, a ∈ N → a = 1 := by
    have : IsSimpleGroup ↥(modO2Image (A6.g1 T V) K) := C.isSimpleGroup_kb
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (modO2Image (A6.g1 T V) K))
      with h | h
    · intro a ha haN
      have : (⟨a, ha⟩ : ↥(modO2Image (A6.g1 T V) K)) ∈ N.subgroupOf _ := haN
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      refine X.not_kb_le_ker_F4 hA37 h1222 h1332 h1334 fun a ha => ?_
      have : (⟨a, ha⟩ : ↥(modO2Image (A6.g1 T V) K)) ∈ N.subgroupOf _ := by
        rw [h]
        exact Subgroup.mem_top _
      exact this

  have h2 : ∀ b ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)), b ∈ N → b = 1 := by
    intro b hb hbN
    rw [← C.kb'_eq] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have haN : a ∈ N := by
      have := hNn.conj_mem _ hbN (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) ⟨t₀, C.ht₀H⟩)⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [h1 a ha haN, map_one]

  have h3 : ∀ w ∈ modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V)
      (K.map (MulAut.conj t₀ : G →* G)), w ∈ N → w = 1 := by
    intro w hw hwN
    refine eq_one_of_centralizes_F4 hA37 hA38 h76 h33 h36 hlist X.R C (fun a ha => ?_) (fun b hb => ?_)
    · have hwa : w * a * w⁻¹ ∈ modO2Image (A6.g1 T V) K :=
        (Subgroup.mem_normalizer_iff.mp (CtxL2.sup_le_normalizer_kb C hA37 hw) a).mp ha
      have hcN : w * a * w⁻¹ * a⁻¹ ∈ N := by
        have := mul_mem hwN (hNn.conj_mem _ (inv_mem hwN) a)
        rwa [show w * (a * w⁻¹ * a⁻¹) = w * a * w⁻¹ * a⁻¹ by group] at this
      have hc := h1 _ (mul_mem hwa (inv_mem ha)) hcN
      calc w * a = (w * a * w⁻¹ * a⁻¹) * a * w := by group
        _ = a * w := by rw [hc, one_mul]
    · have hwb : w * b * w⁻¹ ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) :=
        (Subgroup.mem_normalizer_iff.mp (CtxL2.sup_le_normalizer_kt C hA37 hw) b).mp hb
      have hcN : w * b * w⁻¹ * b⁻¹ ∈ N := by
        have := mul_mem hwN (hNn.conj_mem _ (inv_mem hwN) b)
        rwa [show w * (b * w⁻¹ * b⁻¹) = w * b * w⁻¹ * b⁻¹ by group] at this
      have hc := h2 _ (mul_mem hwb (inv_mem hb)) hcN
      calc w * b = (w * b * w⁻¹ * b⁻¹) * b * w := by group
        _ = b * w := by rw [hc, one_mul]

  rw [injective_iff_map_eq_one]
  intro x hxN
  have hxN' : x ∈ N := hxN
  have hcomm : ∀ c : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V), c ∈ N → ∀ a,
      a ∈ modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) →
      c * a * c⁻¹ * a⁻¹ ∈ N ∧ c * a * c⁻¹ * a⁻¹ ∈
        modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) := by
    intro c hc a ha
    refine ⟨?_, ?_⟩
    · have := mul_mem hc (hNn.conj_mem _ (inv_mem hc) a)
      rwa [show c * (a * c⁻¹ * a⁻¹) = c * a * c⁻¹ * a⁻¹ by group] at this
    · refine mul_mem ?_ (inv_mem ha)
      have hle : modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V)
          (K.map (MulAut.conj t₀ : G →* G)) ≤ (modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V)
            (K.map (MulAut.conj t₀ : G →* G))).comap (MulAut.conj c).toMonoidHom := by
        refine sup_le (fun a' ha' => ?_) (fun b' hb' => ?_)
        · rcases CtxL2.conj_cases C c with ⟨h1', -⟩ | ⟨h1', -⟩
          · exact Subgroup.mem_sup_left (h1' a' ha')
          · exact Subgroup.mem_sup_right (h1' a' ha')
        · rcases CtxL2.conj_cases C c with ⟨-, h2'⟩ | ⟨-, h2'⟩
          · exact Subgroup.mem_sup_right (h2' b' hb')
          · exact Subgroup.mem_sup_left (h2' b' hb')
      exact hle ha
  refine eq_one_of_centralizes_F4 hA37 hA38 h76 h33 h36 hlist X.R C (fun a ha => ?_) (fun b hb => ?_)
  · have hw := hcomm x hxN' a (Subgroup.mem_sup_left ha)
    have := h3 _ hw.2 hw.1
    calc x * a = (x * a * x⁻¹ * a⁻¹) * a * x := by group
      _ = a * x := by rw [this, one_mul]
  · have hw := hcomm x hxN' b (Subgroup.mem_sup_right hb)
    have := h3 _ hw.2 hw.1
    calc x * b = (x * b * x⁻¹ * b⁻¹) * b * x := by group
      _ = b * x := by rw [this, one_mul]

theorem act_eq_one_iff_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h : ↥(A6.g1 T V)) :
    X.top.act h = 1 ↔ (h : G) ∈ pCoreOf 2 (A6.g1 T V) := by
  refine ⟨fun h1 => ?_, X.top.act_eq_one_of_mem⟩
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) h = 1 :=
    X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
      (by rw [actDot_mk, h1, map_one])
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf] at h2
  exact h2

theorem pCoreOf_range_eq_bot_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : pCoreOf 2 X.top.act.range = ⊥ :=
  LRed5.pCoreOf_range_eq_bot X.top.act
    (X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334)

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
