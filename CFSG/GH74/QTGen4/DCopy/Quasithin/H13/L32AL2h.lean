module

public import CFSG.Quasithin.H13.L32AL2h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2f

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

include X in

theorem mem_pCoreOf_iff_comm_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {f : G} (hf : f ∈ A6.g1 T V) :
    f ∈ pCoreOf 2 (A6.g1 T V) ↔ ∀ u ∈ conjClosure V (A6.g1 T V), f * u * f⁻¹ * u⁻¹ ∈ W := by
  rw [← X.top.act_eq_one_iff_comm ⟨f, hf⟩,
    X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334]

theorem card_img_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {B : Subgroup G} (hBH : B ≤ A6.g1 T V) :
    Nat.card (X.img B) = (B ⊓ pCoreOf 2 (A6.g1 T V)).relIndex B := by
  have hE : X.img B = autSec (autOn B (conjClosure V (A6.g1 T V))) ⊤
      (W.subgroupOf (conjClosure V (A6.g1 T V))) := by
    ext ψ
    rw [A6.A6Mod.mem_autSec_iff (le_normalizer_conjClosure V (A6.g1 T V)) X.top.hHUW hBH]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  rw [hE]
  exact A6.A6Mod.card_autSec_eq (le_normalizer_conjClosure V (A6.g1 T V)) X.top.hHUW hBH
    fun f hf => X.mem_pCoreOf_iff_comm_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 (hBH hf)

theorem isA2_img_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V (A6.g1 T V) B) : IsA2 (X.img (A6.g1 T V)) (X.img B) := by
  obtain ⟨hBH, hBe, hBQ, -, -⟩ := hB
  refine ⟨Subgroup.map_mono (by rw [Subgroup.subgroupOf_self]; exact le_top), ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp hBQ
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨X.top.act ⟨b, hBH hb⟩, ⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, ?_⟩
    intro h1
    apply hbQ
    have h2 : X.top.act ⟨b, hBH hb⟩ = 1 := congrArg Subtype.val h1
    rw [X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334] at h2
    exact h2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hBe.1
    have h1 : (x : G) * y = y * x := congrArg Subtype.val
      (mul_comm (⟨x, Subgroup.mem_subgroupOf.mp hx⟩ : ↥B) ⟨y, Subgroup.mem_subgroupOf.mp hy⟩)
    exact Subtype.ext h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h2 : x ^ 2 = 1 := Subtype.ext (hBe.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [h2, map_one]

theorem index_fixV_img_le_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V (A6.g1 T V) B) :
    (fixV (X.img B)).index ≤ Nat.card (X.img B) ^ 2 := by
  obtain ⟨hBH, -, -, -, hidx⟩ := hB
  set U := conjClosure V (A6.g1 T V) with hU
  set q := InternalSec.secMk (W.subgroupOf U) with hq
  set Z := (centralizerMod (fsuV1 T V) U B).subgroupOf U with hZ
  have hZf : Z.map q ≤ fixV (X.img B) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨f, hf, rfl⟩
    have hz' : (z : G) ∈ centralizerMod (fsuV1 T V) U B := hz
    have hf' : (f : G) ∈ B := hf
    have hc := (mem_centralizerMod.mp hz').2.2 (f : G) hf'
    rw [X.top.act_secMk]
    have h1 : (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ ∈ W := by
      apply X.top.hV₁W
      have := inv_mem hc
      rwa [show ((z : G) * f * (z : G)⁻¹ * (f : G)⁻¹)⁻¹ = (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ by
        group] at this
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    exact h1
  have hpos : ∀ Y : Subgroup (Hat V (A6.g1 T V) W), 0 < Y.index := fun Y =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hposU : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (fixV (X.img B)).index ≤ (Z.map q).index :=
    Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le hZf)
  have h2 : (Z.map q).index ≤ Z.index :=
    Nat.le_of_dvd hposU (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
  calc (fixV (X.img B)).index ≤ Z.index := h1.trans h2
    _ = (centralizerMod (fsuV1 T V) U B).relIndex U := rfl
    _ ≤ ((B ⊓ pCoreOf 2 (A6.g1 T V)).relIndex B) ^ 2 := hidx
    _ = Nat.card (X.img B) ^ 2 := by
        rw [X.card_img_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hBH]

theorem qOff_img_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V (A6.g1 T V) B) (hBT : B ≤ T) :
    QOff (X.img (conjClosure K T)) (X.img T) (X.img B) ⊤ := by
  have hA := X.isA2_img_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hB
  have hV : ∀ w : Hat V (A6.g1 T V) W, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact X.top.sec_sq w
  have hinj := X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  refine ⟨Subgroup.map_mono fun x hx => hBT hx, hA.2.1, hA.2.2, X.quad_img hB, ?_, ?_, ?_⟩
  · rw [rAV_le_two_iff hV hA]
    have h1 := X.index_fixV_img_le_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hB
    rw [← (fixV (X.img B)).index_mul_card]
    exact Nat.mul_le_mul_right _ h1
  · rintro _ ⟨b, hb, rfl⟩ hc
    have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
      rintro _ ⟨k, hk, rfl⟩
      simpa using mem_conjClosure X.C.ht₀ hk
    have key : ∀ (A : Subgroup G), A ≤ conjClosure K T →
        ∀ a ∈ modO2Image (A6.g1 T V) A,
          QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) b * a =
            a * QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) b := by
      intro A hA a ha
      obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
      apply hinj
      rw [map_mul, map_mul, actDot_mk, actDot_mk]
      exact hc _ ⟨κ, Subgroup.mem_subgroupOf.mpr (hA hκ), rfl⟩
    have h1 := eq_one_of_centralizes_F4 hA37 hA38 h76 h33 h36 hlist X.R X.C
      (key K (le_conjClosure K T)) (key _ hKt)
    rw [← X.actDot_mk b, h1, map_one]
  · rw [eq_bot_iff]
    rintro g ⟨-, hg⟩
    rw [Subgroup.mem_bot]
    exact MulEquiv.ext fun u => hg u trivial

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
