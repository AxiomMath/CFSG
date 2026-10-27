module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04y
public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

@[expose] def Dg : Subgroup G := C.A ⊓ Subgroup.centralizer (R' : Set G)

theorem A_le_S : C.A ≤ (S : Subgroup G) := fun _ h => ((C.mem_A).mp h).1

theorem A_le_centralizer_W : C.A ≤ Subgroup.centralizer (W : Set G) :=
  fun _ h => ((C.mem_A).mp h).2.1

theorem Dg_le_A : C.Dg ≤ C.A := inf_le_left

theorem A_le_normalizer_R' : C.A ≤ Subgroup.normalizer (R' : Set G) := by
  intro a ha
  obtain ⟨haS, -, -, haK', -⟩ := (C.mem_A).mp ha
  rw [← C.inf_S_eq_R']
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyK, hyS⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp haK' y).mp hyK,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ haS hyS) (Subgroup.inv_mem _ haS)⟩
  · rintro ⟨hyK, hyS⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp haK' y).mpr hyK, ?_⟩
    have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haS) hyS) haS

theorem A_le_centralizer_x₂ : C.A ≤ Subgroup.centralizer ({C.D.x₂} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (C.A_le_centralizer_W ha) _ C.D.x₂_mem).symm

theorem A_le_centralizer_x₃ : C.A ≤ Subgroup.centralizer ({C.D.x₃} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (C.A_le_centralizer_W ha) _ C.D.x₃_mem).symm

@[expose] noncomputable def lam : ↥C.A →* ↥(Subgroup.zpowers C.D.x₂) :=
  qHom (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R' C.t_not_mem_zpowers
    C.A_le_normalizer_R' C.A_le_centralizer_x₂

theorem lam_apply (a : ↥C.A) :
    (C.lam a : G) = C.D.F.ρ'.r⁻¹ * ((a : G) * C.D.F.ρ'.r * (a : G)⁻¹) := rfl

theorem lam_eq_one_iff (a : ↥C.A) : C.lam a = 1 ↔ (a : G) ∈ C.Dg := by
  rw [lam, qHom_eq_one_iff]
  constructor
  · intro h
    refine ⟨a.2, ?_⟩
    show (a : G) ∈ Subgroup.centralizer (R' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (h hy)
  · intro h y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h.2 y hy

theorem x₂_mem_A : C.D.x₂ ∈ C.A := by
  refine (C.mem_A).mpr ⟨C.hd.hWS C.D.x₂_mem, ?_, ?_, Subgroup.le_normalizer C.x₂_mem_K', ?_⟩
  · rw [Subgroup.mem_centralizer_iff]; intro w hw
    exact Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW w hw _ C.D.x₂_mem
  · rw [Subgroup.mem_centralizer_iff]; intro y hy
    exact (C.commutes_R_R' y hy _ C.x₂_mem_R')
  · exact C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃
      C.D.x₂_mem

theorem lam_x₂ : (C.lam ⟨_, C.x₂_mem_A⟩ : G) = z := by
  rw [lam_apply]
  have h1 : C.D.F.ρ'.r * C.D.x₂ * C.D.F.ρ'.r⁻¹ = C.D.x₂⁻¹ := C.D.t₂
  have h3 : C.D.F.ρ'.r * C.D.x₂⁻¹ * C.D.F.ρ'.r⁻¹ = C.D.x₂ := by
    rw [show C.D.F.ρ'.r * C.D.x₂⁻¹ * C.D.F.ρ'.r⁻¹ = (C.D.F.ρ'.r * C.D.x₂ * C.D.F.ρ'.r⁻¹)⁻¹ by
      group, h1, inv_inv]
  have h2 : C.D.F.ρ'.r⁻¹ * C.D.x₂ * C.D.F.ρ'.r = C.D.x₂⁻¹ := by
    conv_lhs => rw [← h3]
    group
  calc C.D.F.ρ'.r⁻¹ * (C.D.x₂ * C.D.F.ρ'.r * C.D.x₂⁻¹)
      = (C.D.F.ρ'.r⁻¹ * C.D.x₂ * C.D.F.ρ'.r) * C.D.x₂⁻¹ := by group
    _ = (C.D.x₂ ^ 2)⁻¹ := by rw [h2]; group
    _ = z := by rw [C.x₂_sq]; exact inv_eq_of_mul_eq_one_right C.hzK.sq

theorem exists_T3 : ∃ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K ∧ C.D.x₃ ∈ T₃ ∧
    T₃ ≤ Subgroup.normalizer (W : Set G) ∧ C.Dg ≤ Subgroup.normalizer (T₃ : Set G) := by
  set J := C.D.F.ρ₃.K with hJdef
  set H₁ := J ⊓ Subgroup.normalizer (W : Set G) with hH₁
  set Q := C.Dg ⊔ Subgroup.zpowers C.D.x₃ with hQdef
  have hx₃N : C.D.x₃ ∈ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer C.D.x₃_mem
  have hx₃H : C.D.x₃ ∈ H₁ := ⟨C.x₃_mem_J, hx₃N⟩
  have hQS : Q ≤ (S : Subgroup G) :=
    sup_le (C.Dg_le_A.trans C.A_le_S) (Subgroup.zpowers_le.mpr (C.hd.hWS C.D.x₃_mem))
  have hQ2 : IsPGroup 2 ↥Q := S.isPGroup'.to_le hQS
  have hDH : C.Dg ≤ Subgroup.normalizer (H₁ : Set G) := by
    intro d hd
    have hdA := C.Dg_le_A hd
    have hdJ : d ∈ Subgroup.normalizer (J : Set G) := ((C.mem_A).mp hdA).2.2.2.2
    have hdW : d ∈ Subgroup.normalizer (W : Set G) :=
      (Subgroup.centralizer_le_normalizer (W : Set G)) (C.A_le_centralizer_W hdA)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyJ, hyW⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hdJ y).mp hyJ,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hdW hyW) (Subgroup.inv_mem _ hdW)⟩
    · rintro ⟨hyJ, hyW⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hdJ y).mpr hyJ, ?_⟩
      have e : y = d⁻¹ * (d * y * d⁻¹) * d := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hdW) hyW) hdW
  have hQN : Q ≤ Subgroup.normalizer (H₁ : Set G) :=
    sup_le hDH (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hx₃H))
  have hNN : H₁ ⊔ Q ≤ Subgroup.normalizer (H₁ : Set G) := sup_le Subgroup.le_normalizer hQN
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ2 (le_sup_right : Q ≤ H₁ ⊔ Q)
  have hVH : IsSylow2In (V ⊓ H₁) H₁ := isSylow2In_inf_of_le_normalizer hV le_sup_left hNN
  have hR₃H : IsSylow2In C.D.F.ρ₃.R H₁ :=
    ⟨le_inf C.D.F.ρ₃.hRK.1 C.D.F.ρ₃.hR.2, C.D.F.ρ₃.hRK.2.1,
      fun T hTH hT2 hRT => C.D.F.ρ₃.hRK.2.2 T (hTH.trans inf_le_left) hT2 hRT⟩
  have hTJ : IsSylow2In (V ⊓ H₁) J :=
    IsSylow2In.of_natCard_le C.D.F.ρ₃.hRK hVH.2.1 (hVH.1.trans inf_le_left)
      (le_of_eq (hR₃H.natCard_eq hVH))
  refine ⟨V ⊓ H₁, hTJ, ⟨hQV (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), hx₃H⟩,
    fun y hy => hy.2.2, ?_⟩
  intro d hd
  have hdV : d ∈ V := hQV (Subgroup.mem_sup_left hd)
  have hdH : d ∈ Subgroup.normalizer (H₁ : Set G) := hQN (Subgroup.mem_sup_left hd)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyV, hyH⟩
    exact ⟨V.mul_mem (V.mul_mem hdV hyV) (V.inv_mem hdV),
      (Subgroup.mem_normalizer_iff.mp hdH y).mp hyH⟩
  · rintro ⟨hyV, hyH⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hdH y).mpr hyH⟩
    have e : y = d⁻¹ * (d * y * d⁻¹) * d := by group
    rw [e]
    exact V.mul_mem (V.mul_mem (V.inv_mem hdV) hyV) hdV

include C in
theorem pow_four_of_mem_W {w : G} (hw : w ∈ W) : w ^ 4 = 1 := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  have h1 : C.D.x₁ ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← C.orderOf_x₁,
      pow_orderOf_eq_one]
  have h3 : C.D.x₃ ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← C.orderOf_x₃,
      pow_orderOf_eq_one]
  rw [(C.D.comm13.zpow_zpow a b).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul, mul_comm a, mul_comm b, zpow_mul, zpow_mul]
  push_cast
  rw [h1, h3, one_zpow, one_zpow, mul_one]

theorem pow_four_ne_z {a : G} (ha : a ∈ C.A) : a ^ 4 ≠ z := by
  intro h4
  obtain ⟨-, haW, haR, haK', haJ⟩ := (C.mem_A).mp ha
  have haN : a ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (W : Set G)) haW
  have haK : conjSub a C.D.F.ρ.K = C.D.F.ρ.K := by
    rw [C.hK]
    exact conjSub_eq_of_commute C.hyp C.mem C.x₁_mem_K C.orderOf_x₁
      (Subgroup.mem_centralizer_iff.mp haR _ C.x₁_mem_R).symm
  have hT : TrivMu Ω W a := C.trivMu_of_fix haN haK
    (by rw [C.hK']; exact mem_normalizer_iff_conjSub_eq.mp haK')
    (mem_normalizer_iff_conjSub_eq.mp haJ)
  set s := C.D.F.ρ₃.r with hsdef
  have hsM : s ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ₃.hR C.D.F.ρ₃.hr
  have hn := hT s hsM
  obtain ⟨w, hw, o, ho, hwo⟩ := Thompson.mem_sup_OCW_iff.mp (Subgroup.inv_mem _ hn)
  have hsa : s * a * s⁻¹ = w * o * a := by
    rw [hwo]; group
  have h1 : (s * a * s⁻¹) ^ 4 = z * C.D.F.j := by rw [conj_pow, h4]; exact C.s_conj_z
  have haON : a ∈ Subgroup.normalizer (OCW W : Set G) := Thompson.normalizer_le_normalizer_OCW W haN
  have hconj : ∀ k : ℕ, a ^ k * o * (a ^ k)⁻¹ ∈ OCW W := fun k =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ haON k) o).mp ho
  set o' := o * (a * o * a⁻¹) * (a ^ 2 * o * (a ^ 2)⁻¹) * (a ^ 3 * o * (a ^ 3)⁻¹) with ho'
  have ho'O : o' ∈ OCW W := by
    have h2 := hconj 1
    rw [pow_one] at h2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ho h2) (hconj 2)) (hconj 3)
  have hwc : Commute w (o * a) := by
    refine Commute.mul_right ?_ ?_
    · exact (Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W ho) w hw)
    · exact (Subgroup.mem_centralizer_iff.mp haW w hw)
  have hkey : (o * a) ^ 4 = o * (a * o * a⁻¹) * (a ^ 2 * o * (a ^ 2)⁻¹) *
      (a ^ 3 * o * (a ^ 3)⁻¹) * a ^ 4 := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    group
  have h2 : (w * o * a) ^ 4 = o' * a ^ 4 := by
    rw [mul_assoc, hwc.mul_pow, C.pow_four_of_mem_W hw, one_mul, hkey]
  rw [hsa, h2, h4] at h1
  have hj : C.D.F.j = o' := by
    have hzc : z * C.D.F.j = C.D.F.j * z := by
      have := Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW z C.hd.hzW
        C.D.F.j (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2)
      exact this
    calc C.D.F.j = C.D.F.j * z * z⁻¹ := by group
      _ = z * C.D.F.j * z⁻¹ := by rw [hzc]
      _ = o' * z * z⁻¹ := by rw [h1]
      _ = o' := by group
  have hj1 : C.D.F.j = 1 := by
    refine Asc77.eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) (hj ▸ ho'O) ?_
    exact (Thompson.isPGroup_of_mem_WSet C.hd.hW).to_le
      (Subgroup.zpowers_le.mpr (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2))
  exact C.hjJ.ne_one hj1

include C in
theorem mem_W_of_mem_P_A {a : G} (haP : a ∈ (S : Subgroup G) ⊓ MGrp Ω W) (haA : a ∈ C.A) :
    a ∈ W := by
  obtain ⟨haS, haW, haR, haK', haJ⟩ := (C.mem_A).mp haA
  have haN : a ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (W : Set G)) haW
  have haK : conjSub a C.D.F.ρ.K = C.D.F.ρ.K := by
    rw [C.hK]
    exact conjSub_eq_of_commute C.hyp C.mem C.x₁_mem_K C.orderOf_x₁
      (Subgroup.mem_centralizer_iff.mp haR _ C.x₁_mem_R).symm
  have hT : TrivMu Ω W a := C.trivMu_of_fix haN haK
    (by rw [C.hK']; exact mem_normalizer_iff_conjSub_eq.mp haK')
    (mem_normalizer_iff_conjSub_eq.mp haJ)
  have hcent : ∀ y : ↥(muGroup Ω W), piM Ω W ⟨a, haP.2⟩ * y = y * piM Ω W ⟨a, haP.2⟩ := by
    intro y
    obtain ⟨m, rfl⟩ := piM_surjective W y
    have h1 : piM Ω W (⟨a, haP.2⟩ * m * (⟨a, haP.2⟩)⁻¹ * m⁻¹) = 1 := by
      apply Subtype.ext
      rw [piM_apply]
      exact Thompson.piG_of_mem_sup (hT m m.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    calc piM Ω W ⟨a, haP.2⟩ * piM Ω W m
        = piM Ω W ⟨a, haP.2⟩ * piM Ω W m * (piM Ω W ⟨a, haP.2⟩)⁻¹ * piM Ω W ⟨a, haP.2⟩ := by
          group
      _ = piM Ω W m * piM Ω W ⟨a, haP.2⟩ := by rw [h2]
  have hφ : ∀ σ : Equiv.Perm (Fin 4),
      C.D.φ (piM Ω W ⟨a, haP.2⟩) * σ = σ * C.D.φ (piM Ω W ⟨a, haP.2⟩) := by
    intro σ
    have h2 := congrArg C.D.φ (hcent (C.D.φ.symm σ))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have hq1 : piM Ω W ⟨a, haP.2⟩ = 1 := by
    have h := perm4_center _ (hφ _) (hφ _) (hφ _)
    exact C.D.φ.injective (h.trans (map_one C.D.φ).symm)
  have hpa : Thompson.piG W a = 1 := by
    have h := congrArg Subtype.val hq1
    rw [piM_apply] at h
    exact h
  have hmem := (Thompson.piG_eq_one_iff haN).mp hpa
  exact Thompson.mem_of_isPGroup_of_mem_sup_OCW (Thompson.isPGroup_of_mem_WSet C.hd.hW)
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS)) hmem

theorem eq_one_or_eq_z_of_mem_W {w : G} (hw : w ∈ W)
    (hr : C.D.F.ρ.r * w * C.D.F.ρ.r⁻¹ = w) (ht : C.D.F.ρ'.r * w * C.D.F.ρ'.r⁻¹ = w) :
    w = 1 ∨ w = z := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.conj_r_nf] at hr
  rw [C.conj_t_nf] at ht
  have h1 : C.D.x₁ ^ (b - a - a) = 1 := by
    have e : C.D.x₁ ^ (b - a) = C.D.x₁ ^ a := mul_right_cancel hr
    rw [zpow_sub, e, mul_inv_cancel]
  have h2 : C.D.x₁ ^ b * C.D.x₃ ^ (2 * b) = 1 := by
    have e := C.mul_nf a b b (2 * b)
    rw [show b + 2 * b = 3 * b by ring, ht] at e
    exact mul_left_cancel (e.trans (mul_one _).symm)
  have hb := C.four_dvd_of_x₁ (C.eq_one_of_nf b (2 * b) h2).1
  have hab := C.four_dvd_of_x₁ h1
  have h3 : C.D.x₃ ^ b = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [C.orderOf_x₃]; exact_mod_cast hb)
  rw [h3, mul_one]
  have h4 : a % 4 = 0 ∨ a % 4 = 2 := by omega
  rcases h4 with h4 | h4
  · left
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [C.orderOf_x₁]; push_cast; omega)
  · right
    have h5 : C.D.x₁ ^ (a - 2) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [C.orderOf_x₁]; push_cast; omega)
    calc C.D.x₁ ^ a = C.D.x₁ ^ (a - 2) * C.D.x₁ ^ (2 : ℤ) := by
          rw [← zpow_add, sub_add_cancel]
      _ = z := by rw [h5, one_mul, zpow_two, ← sq, C.x₁_sq]

include C in
theorem z_mem_Dg : z ∈ C.Dg := by
  have hzW : z ∈ W := C.hd.hzW
  refine ⟨(C.mem_A).mpr ⟨C.hd.hWS hzW, ?_, ?_, Subgroup.le_normalizer C.hzK'.mem, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW v hv z hzW
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (e189_commute_of_mem C.hzK (C.hd.hR.2.1 hv)).symm
  · exact C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃ hzW
  · show z ∈ Subgroup.centralizer (R' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (e189_commute_of_mem C.hzK' (C.hd.hR'.2.1 hv)).symm

include C in
theorem z_mem_P : z ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.hd.hzW

include C in
theorem P_normal {g : G} (hg : g ∈ (S : Subgroup G)) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ MGrp Ω W) : g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  refine ⟨S.mul_mem (S.mul_mem hg hx.1) (S.inv_mem hg), ?_⟩
  have hgN : g ∈ Subgroup.normalizer (MGrp Ω W : Set G) :=
    le_normalizer_MGrp C.hyp (C.le_normalizer_W hg)
  exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx.2

theorem Dg_mem_P {d : G} (hd : d ∈ C.Dg) (hdP : d ∈ (S : Subgroup G) ⊓ MGrp Ω W) :
    d = 1 ∨ d = z := by
  have hdA := C.Dg_le_A hd
  have hdW := C.mem_W_of_mem_P_A hdP hdA
  have hdR := ((C.mem_A).mp hdA).2.2.1
  have hdR' : d ∈ Subgroup.centralizer (R' : Set G) := hd.2
  refine C.eq_one_or_eq_z_of_mem_W hdW ?_ ?_
  · have h := Subgroup.mem_centralizer_iff.mp hdR _ C.r_mem_R
    calc C.D.F.ρ.r * d * C.D.F.ρ.r⁻¹ = d * C.D.F.ρ.r * C.D.F.ρ.r⁻¹ := by rw [h]
      _ = d := by group
  · have h := Subgroup.mem_centralizer_iff.mp hdR' _ C.t_mem_R'
    calc C.D.F.ρ'.r * d * C.D.F.ρ'.r⁻¹ = d * C.D.F.ρ'.r * C.D.F.ρ'.r⁻¹ := by rw [h]
      _ = d := by group

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
