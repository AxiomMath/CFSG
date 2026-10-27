module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf34Frame
public import CFSG.ClassicalInvolution.Asc77.AscS24BSwap

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.S24
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)

include C in
theorem x₃_zpow_four : C.D.x₃ ^ (4 : ℤ) = 1 := by
  have := pow_orderOf_eq_one C.D.x₃
  rw [C.orderOf_x₃] at this
  exact_mod_cast this

include C in
theorem cent_W_r_le {w : G} (hw : w ∈ W) (h : C.D.F.ρ.r * w * C.D.F.ρ.r⁻¹ = w) :
    w ∈ Subgroup.zpowers C.D.x₂ := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.conj_r_nf a b] at h
  have h1 : C.D.x₁ ^ (b - a) = C.D.x₁ ^ a := mul_right_cancel h
  have h2 : C.D.x₁ ^ (b - 2 * a) = 1 := by
    rw [show b - 2 * a = (b - a) - a by ring, zpow_sub, h1, mul_inv_cancel]
  obtain ⟨k, hk⟩ := C.four_dvd_of_x₁ h2
  have hb : b = 2 * a + 4 * k := by omega
  refine ⟨a, ?_⟩
  have h4k : C.D.x₃ ^ ((4 : ℤ) * k) = 1 := by
    rw [zpow_mul, C.x₃_zpow_four, one_zpow]
  have e : C.D.x₃ ^ b = (C.D.x₃ ^ (2 : ℕ)) ^ a := by
    rw [hb, zpow_add, h4k, mul_one, ← zpow_natCast, ← zpow_mul]
    norm_cast
  show C.D.x₂ ^ a = _
  rw [C.x₂_eq, Commute.mul_zpow (C.D.comm13.pow_right 2), e]

include C in
theorem cent_W_t_le {w : G} (hw : w ∈ W) (h : C.D.F.ρ'.r * w * C.D.F.ρ'.r⁻¹ = w) :
    w ∈ Subgroup.zpowers C.D.x₁ := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.conj_t_nf a b] at h
  have e1 : (C.D.x₁ ^ a * C.D.x₃ ^ b) * (C.D.x₁ ^ b * C.D.x₃ ^ (2 * b)) =
      C.D.x₁ ^ (a + b) * C.D.x₃ ^ (3 * b) := by
    rw [C.mul_nf]
    congr 2
    ring
  have h1 : C.D.x₁ ^ b * C.D.x₃ ^ (2 * b) = 1 := by
    have := e1.trans h
    exact mul_left_cancel (this.trans (mul_one _).symm)
  obtain ⟨h1a, -⟩ := C.eq_one_of_nf b (2 * b) h1
  obtain ⟨k, hk⟩ := C.four_dvd_of_x₁ h1a
  refine ⟨a, ?_⟩
  have h4k : C.D.x₃ ^ b = 1 := by
    rw [hk, zpow_mul, C.x₃_zpow_four, one_zpow]
  rw [h4k, mul_one]

include C in
theorem P_cent_R_le {f : G} (hfP : f ∈ (S : Subgroup G) ⊓ MGrp Ω W)
    (hfR : ∀ y ∈ R, f * y = y * f) : f ∈ R' := by
  have hfS := hfP.1
  have hfM := hfP.2
  have hfN : f ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hfM
  have hrM : C.D.F.ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr
  have htM : C.D.F.ρ'.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr
  have hrN := Thompson.MGrp_le_normalizer Ω W hrM
  have htN := Thompson.MGrp_le_normalizer Ω W htM
  have hW2 := Thompson.isPGroup_of_mem_WSet C.hd.hW
  have two_elt : ∀ {x : G}, x ∈ (S : Subgroup G) → x ∈ W ⊔ OCW W → x ∈ W := fun hx hxs =>
    Thompson.mem_of_isPGroup_of_mem_sup_OCW hW2
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx)) hxs
  have hrS : C.D.F.ρ.r ∈ (S : Subgroup G) := C.hd.hR.2.2 C.r_mem_R
  have htS : C.D.F.ρ'.r ∈ (S : Subgroup G) := C.hd.hR'.2.2 C.t_mem_R'
  have hx₁inv : C.D.x₁⁻¹ ≠ C.D.x₁ := by
    intro h
    have e2 : C.D.x₁ ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e2
    rw [C.orderOf_x₁] at this
    omega
  have hwx₁ : ∀ w ∈ W, w * C.D.x₁ = C.D.x₁ * w := fun w hw =>
    Q3.Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW w hw _ C.D.x₁_mem
  have hfx₁ := hfR _ C.x₁_mem_R
  have hfr := hfR _ C.r_mem_R
  have hfr' : C.D.F.ρ.r * f * C.D.F.ρ.r⁻¹ = f := by rw [← hfr]; group
  have hra : T7D.imgQ C.D.F.ρ = piM Ω W ⟨_, hrM⟩ := Subtype.ext rfl
  have hta : T7D.imgQ C.D.F.ρ' = piM Ω W ⟨_, htM⟩ := Subtype.ext rfl
  have hab : C.D.φ (T7D.imgQ C.D.F.ρ) ≠ C.D.φ (T7D.imgQ C.D.F.ρ') :=
    fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : C.D.φ (T7D.imgQ C.D.F.ρ) * C.D.φ (T7D.imgQ C.D.F.ρ') =
      C.D.φ (T7D.imgQ C.D.F.ρ') * C.D.φ (T7D.imgQ C.D.F.ρ) := by
    rw [← map_mul, ← map_mul, C.D.hcomm]
  have hfb : piM Ω W ⟨f, hfM⟩ * T7D.imgQ C.D.F.ρ = T7D.imgQ C.D.F.ρ * piM Ω W ⟨f, hfM⟩ := by
    rw [hra, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hfr
  have hc : C.D.φ (piM Ω W ⟨f, hfM⟩) * C.D.φ (T7D.imgQ C.D.F.ρ) =
      C.D.φ (T7D.imgQ C.D.F.ρ) * C.D.φ (piM Ω W ⟨f, hfM⟩) := by
    rw [← map_mul, ← map_mul, hfb]
  have hpf : (piM Ω W ⟨f, hfM⟩ : NQuot (W ⊔ OCW W)) = Thompson.piG W f := rfl
  have hpr : (T7D.imgQ C.D.F.ρ : NQuot (W ⊔ OCW W)) = Thompson.piG W C.D.F.ρ.r := rfl
  have hpt : (T7D.imgQ C.D.F.ρ' : NQuot (W ⊔ OCW W)) = Thompson.piG W C.D.F.ρ'.r := rfl
  rcases perm4_cent_swap (C.D.φ (piM Ω W ⟨f, hfM⟩)) _ (C.φ_imgQ_mem C.D.F.ρ) _
      (C.φ_imgQ_mem C.D.F.ρ') hab hcomm hc with e | e | e | e
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = 1 := C.D.φ.injective (e.trans (map_one _).symm)
    have h1 : Thompson.piG W f = 1 := congrArg Subtype.val hfb1
    have hfW : f ∈ W := two_elt hfS ((Thompson.piG_eq_one_iff hfN).mp h1)
    exact Subgroup.zpowers_le.mpr C.x₂_mem_R' (C.cent_W_r_le hfW hfr')
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = T7D.imgQ C.D.F.ρ := C.D.φ.injective e
    have h1 : Thompson.piG W f = Thompson.piG W C.D.F.ρ.r := by
      rw [← hpf, hfb1, hpr]
    have hw : C.D.F.ρ.r⁻¹ * f ∈ W :=
      two_elt (S.mul_mem (S.inv_mem hrS) hfS) ((Thompson.piG_eq_iff hrN hfN).mp h1.symm)
    obtain ⟨w, hwW, hfw⟩ : ∃ w ∈ W, f = C.D.F.ρ.r * w := ⟨_, hw, by group⟩
    exfalso
    have hw' : w * C.D.x₁ * w⁻¹ = C.D.x₁ := by rw [hwx₁ w hwW]; group
    have key : f * C.D.x₁ * f⁻¹ = C.D.x₁⁻¹ := by
      calc f * C.D.x₁ * f⁻¹ = C.D.F.ρ.r * (w * C.D.x₁ * w⁻¹) * C.D.F.ρ.r⁻¹ := by
            rw [hfw]; group
        _ = C.D.F.ρ.r * C.D.x₁ * C.D.F.ρ.r⁻¹ := by rw [hw']
        _ = C.D.x₁⁻¹ := C.D.r₁
    apply hx₁inv
    rw [← key, hfx₁]; group
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = T7D.imgQ C.D.F.ρ' := C.D.φ.injective e
    have h1 : Thompson.piG W f = Thompson.piG W C.D.F.ρ'.r := by
      rw [← hpf, hfb1, hpt]
    have hw : C.D.F.ρ'.r⁻¹ * f ∈ W :=
      two_elt (S.mul_mem (S.inv_mem htS) hfS) ((Thompson.piG_eq_iff htN hfN).mp h1.symm)
    obtain ⟨w, hwW, hfw⟩ : ∃ w ∈ W, f = C.D.F.ρ'.r * w := ⟨_, hw, by group⟩
    have hrw : C.D.F.ρ.r * w * C.D.F.ρ.r⁻¹ = w := by
      have hrt := C.commute_r_t.eq
      have h2 : C.D.F.ρ'.r * (w * C.D.F.ρ.r) = C.D.F.ρ'.r * (C.D.F.ρ.r * w) := by
        calc C.D.F.ρ'.r * (w * C.D.F.ρ.r) = f * C.D.F.ρ.r := by rw [hfw]; group
          _ = C.D.F.ρ.r * f := hfr
          _ = C.D.F.ρ.r * (C.D.F.ρ'.r * w) := by rw [hfw]
          _ = (C.D.F.ρ.r * C.D.F.ρ'.r) * w := by group
          _ = (C.D.F.ρ'.r * C.D.F.ρ.r) * w := by rw [hrt]
          _ = C.D.F.ρ'.r * (C.D.F.ρ.r * w) := by group
      have h3 := mul_left_cancel h2
      rw [← h3]; group
    rw [hfw]
    exact R'.mul_mem C.t_mem_R' (Subgroup.zpowers_le.mpr C.x₂_mem_R' (C.cent_W_r_le hwW hrw))
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' :=
      C.D.φ.injective (e.trans (map_mul _ _ _).symm)
    have h1 : Thompson.piG W f = Thompson.piG W (C.D.F.ρ.r * C.D.F.ρ'.r) := by
      rw [Thompson.piG_mul hrN htN, ← hpr, ← hpt, ← hpf, hfb1]
      rfl
    have hrtS : C.D.F.ρ.r * C.D.F.ρ'.r ∈ (S : Subgroup G) := S.mul_mem hrS htS
    have hw : (C.D.F.ρ.r * C.D.F.ρ'.r)⁻¹ * f ∈ W :=
      two_elt (S.mul_mem (S.inv_mem hrtS) hfS)
        ((Thompson.piG_eq_iff (Subgroup.mul_mem _ hrN htN) hfN).mp h1.symm)
    obtain ⟨w, hwW, hfw⟩ : ∃ w ∈ W, f = (C.D.F.ρ.r * C.D.F.ρ'.r) * w := ⟨_, hw, by group⟩
    exfalso
    have hw' : w * C.D.x₁ * w⁻¹ = C.D.x₁ := by rw [hwx₁ w hwW]; group
    have key : f * C.D.x₁ * f⁻¹ = C.D.x₁⁻¹ := by
      calc f * C.D.x₁ * f⁻¹ = C.D.F.ρ.r * (C.D.F.ρ'.r * (w * C.D.x₁ * w⁻¹) * C.D.F.ρ'.r⁻¹) *
            C.D.F.ρ.r⁻¹ := by rw [hfw]; group
        _ = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.x₁ * C.D.F.ρ'.r⁻¹) * C.D.F.ρ.r⁻¹ := by rw [hw']
        _ = C.D.F.ρ.r * C.D.x₁ * C.D.F.ρ.r⁻¹ := by rw [C.D.t₁]
        _ = C.D.x₁⁻¹ := C.D.r₁
    apply hx₁inv
    rw [← key, hfx₁]; group


include C in
theorem P_cent_R'_le {f : G} (hfP : f ∈ (S : Subgroup G) ⊓ MGrp Ω W)
    (hfR' : ∀ y ∈ R', f * y = y * f) : f ∈ R := by
  have hfS := hfP.1
  have hfM := hfP.2
  have hfN : f ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hfM
  have hrM : C.D.F.ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr
  have htM : C.D.F.ρ'.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr
  have hrN := Thompson.MGrp_le_normalizer Ω W hrM
  have htN := Thompson.MGrp_le_normalizer Ω W htM
  have hW2 := Thompson.isPGroup_of_mem_WSet C.hd.hW
  have two_elt : ∀ {x : G}, x ∈ (S : Subgroup G) → x ∈ W ⊔ OCW W → x ∈ W := fun hx hxs =>
    Thompson.mem_of_isPGroup_of_mem_sup_OCW hW2
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx)) hxs
  have hrS : C.D.F.ρ.r ∈ (S : Subgroup G) := C.hd.hR.2.2 C.r_mem_R
  have htS : C.D.F.ρ'.r ∈ (S : Subgroup G) := C.hd.hR'.2.2 C.t_mem_R'
  have hx₂inv : C.D.x₂⁻¹ ≠ C.D.x₂ := by
    intro h
    have e2 : C.D.x₂ ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e2
    rw [C.orderOf_x₂] at this
    omega
  have hwx₂ : ∀ w ∈ W, w * C.D.x₂ = C.D.x₂ * w := fun w hw =>
    Q3.Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW w hw _ C.D.x₂_mem
  have hfx₂ := hfR' _ C.x₂_mem_R'
  have hft := hfR' _ C.t_mem_R'
  have hft' : C.D.F.ρ'.r * f * C.D.F.ρ'.r⁻¹ = f := by rw [← hft]; group
  have hra : T7D.imgQ C.D.F.ρ = piM Ω W ⟨_, hrM⟩ := Subtype.ext rfl
  have hta : T7D.imgQ C.D.F.ρ' = piM Ω W ⟨_, htM⟩ := Subtype.ext rfl
  have hab : C.D.φ (T7D.imgQ C.D.F.ρ') ≠ C.D.φ (T7D.imgQ C.D.F.ρ) :=
    fun h => C.D.hab (C.D.φ.injective h).symm
  have hcomm : C.D.φ (T7D.imgQ C.D.F.ρ') * C.D.φ (T7D.imgQ C.D.F.ρ) =
      C.D.φ (T7D.imgQ C.D.F.ρ) * C.D.φ (T7D.imgQ C.D.F.ρ') := by
    rw [← map_mul, ← map_mul, C.D.hcomm]
  have hfb : piM Ω W ⟨f, hfM⟩ * T7D.imgQ C.D.F.ρ' = T7D.imgQ C.D.F.ρ' * piM Ω W ⟨f, hfM⟩ := by
    rw [hta, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hft
  have hc : C.D.φ (piM Ω W ⟨f, hfM⟩) * C.D.φ (T7D.imgQ C.D.F.ρ') =
      C.D.φ (T7D.imgQ C.D.F.ρ') * C.D.φ (piM Ω W ⟨f, hfM⟩) := by
    rw [← map_mul, ← map_mul, hfb]
  have hpf : (piM Ω W ⟨f, hfM⟩ : NQuot (W ⊔ OCW W)) = Thompson.piG W f := rfl
  have hpr : (T7D.imgQ C.D.F.ρ : NQuot (W ⊔ OCW W)) = Thompson.piG W C.D.F.ρ.r := rfl
  have hpt : (T7D.imgQ C.D.F.ρ' : NQuot (W ⊔ OCW W)) = Thompson.piG W C.D.F.ρ'.r := rfl
  rcases perm4_cent_swap (C.D.φ (piM Ω W ⟨f, hfM⟩)) _ (C.φ_imgQ_mem C.D.F.ρ') _
      (C.φ_imgQ_mem C.D.F.ρ) hab hcomm hc with e | e | e | e
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = 1 := C.D.φ.injective (e.trans (map_one _).symm)
    have h1 : Thompson.piG W f = 1 := congrArg Subtype.val hfb1
    have hfW : f ∈ W := two_elt hfS ((Thompson.piG_eq_one_iff hfN).mp h1)
    exact Subgroup.zpowers_le.mpr C.x₁_mem_R (C.cent_W_t_le hfW hft')
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = T7D.imgQ C.D.F.ρ' := C.D.φ.injective e
    have h1 : Thompson.piG W f = Thompson.piG W C.D.F.ρ'.r := by
      rw [← hpf, hfb1, hpt]
    have hw : C.D.F.ρ'.r⁻¹ * f ∈ W :=
      two_elt (S.mul_mem (S.inv_mem htS) hfS) ((Thompson.piG_eq_iff htN hfN).mp h1.symm)
    obtain ⟨w, hwW, hfw⟩ : ∃ w ∈ W, f = C.D.F.ρ'.r * w := ⟨_, hw, by group⟩
    exfalso
    have hw' : w * C.D.x₂ * w⁻¹ = C.D.x₂ := by rw [hwx₂ w hwW]; group
    have key : f * C.D.x₂ * f⁻¹ = C.D.x₂⁻¹ := by
      calc f * C.D.x₂ * f⁻¹ = C.D.F.ρ'.r * (w * C.D.x₂ * w⁻¹) * C.D.F.ρ'.r⁻¹ := by
            rw [hfw]; group
        _ = C.D.F.ρ'.r * C.D.x₂ * C.D.F.ρ'.r⁻¹ := by rw [hw']
        _ = C.D.x₂⁻¹ := C.D.t₂
    apply hx₂inv
    rw [← key, hfx₂]; group
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = T7D.imgQ C.D.F.ρ := C.D.φ.injective e
    have h1 : Thompson.piG W f = Thompson.piG W C.D.F.ρ.r := by
      rw [← hpf, hfb1, hpr]
    have hw : C.D.F.ρ.r⁻¹ * f ∈ W :=
      two_elt (S.mul_mem (S.inv_mem hrS) hfS) ((Thompson.piG_eq_iff hrN hfN).mp h1.symm)
    obtain ⟨w, hwW, hfw⟩ : ∃ w ∈ W, f = C.D.F.ρ.r * w := ⟨_, hw, by group⟩
    have htw : C.D.F.ρ'.r * w * C.D.F.ρ'.r⁻¹ = w := by
      have hrt := C.commute_r_t.eq
      have h2 : C.D.F.ρ.r * (C.D.F.ρ'.r * w) = C.D.F.ρ.r * (w * C.D.F.ρ'.r) := by
        calc C.D.F.ρ.r * (C.D.F.ρ'.r * w) = C.D.F.ρ'.r * (C.D.F.ρ.r * w) := by
              rw [← mul_assoc, hrt, mul_assoc]
          _ = C.D.F.ρ'.r * f := by rw [hfw]
          _ = f * C.D.F.ρ'.r := hft.symm
          _ = C.D.F.ρ.r * (w * C.D.F.ρ'.r) := by rw [hfw]; group
      have h3 := mul_left_cancel h2
      rw [h3]; group
    rw [hfw]
    exact R.mul_mem C.r_mem_R (Subgroup.zpowers_le.mpr C.x₁_mem_R (C.cent_W_t_le hwW htw))
  ·
    have hfb1 : piM Ω W ⟨f, hfM⟩ = T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ :=
      C.D.φ.injective (e.trans (map_mul _ _ _).symm)
    have h1 : Thompson.piG W f = Thompson.piG W (C.D.F.ρ'.r * C.D.F.ρ.r) := by
      rw [Thompson.piG_mul htN hrN, ← hpr, ← hpt, ← hpf, hfb1]
      rfl
    have htrS : C.D.F.ρ'.r * C.D.F.ρ.r ∈ (S : Subgroup G) := S.mul_mem htS hrS
    have hw : (C.D.F.ρ'.r * C.D.F.ρ.r)⁻¹ * f ∈ W :=
      two_elt (S.mul_mem (S.inv_mem htrS) hfS)
        ((Thompson.piG_eq_iff (Subgroup.mul_mem _ htN hrN) hfN).mp h1.symm)
    obtain ⟨w, hwW, hfw⟩ : ∃ w ∈ W, f = (C.D.F.ρ'.r * C.D.F.ρ.r) * w := ⟨_, hw, by group⟩
    exfalso
    have hw' : w * C.D.x₂ * w⁻¹ = C.D.x₂ := by rw [hwx₂ w hwW]; group
    have key : f * C.D.x₂ * f⁻¹ = C.D.x₂⁻¹ := by
      calc f * C.D.x₂ * f⁻¹ = C.D.F.ρ'.r * (C.D.F.ρ.r * (w * C.D.x₂ * w⁻¹) * C.D.F.ρ.r⁻¹) *
            C.D.F.ρ'.r⁻¹ := by rw [hfw]; group
        _ = C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.x₂ * C.D.F.ρ.r⁻¹) * C.D.F.ρ'.r⁻¹ := by rw [hw']
        _ = C.D.F.ρ'.r * C.D.x₂ * C.D.F.ρ'.r⁻¹ := by rw [C.D.r₂]
        _ = C.D.x₂⁻¹ := C.D.t₂
    apply hx₂inv
    rw [← key, hfx₂]; group


include C in
theorem conj_R_mem_P {g : G} (hRS : ∀ y ∈ R, g⁻¹ * y * g ∈ (S : Subgroup G)) :
    ∀ y ∈ R, g⁻¹ * y * g ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  intro y hy
  have hx1sq : C.D.x₁ * C.D.x₁ = z := by rw [← pow_two]; exact C.x₁_sq
  have hx1 : C.D.x₁ ≠ 1 := by
    intro h; apply C.hzK.ne_one; rw [← hx1sq, h, one_mul]
  have hx1z : C.D.x₁ ≠ z := by
    intro h
    apply C.hzK.ne_one
    have h1 : z * z = z * 1 := by
      calc z * z = C.D.x₁ * C.D.x₁ := by rw [h]
        _ = z := hx1sq
        _ = z * 1 := (mul_one z).symm
    exact mul_left_cancel h1
  by_cases hy1 : y = 1
  · rw [hy1]; simpa using (⟨(S : Subgroup G).one_mem, (MGrp Ω W).one_mem⟩ :
      (1 : G) ∈ (S : Subgroup G) ⊓ MGrp Ω W)
  by_cases hyz : y = z
  · have hgP := C.conj_mem_P_of_R C.x₁_mem_R hx1 hx1z (hRS _ C.x₁_mem_R)
    have hsq : g⁻¹ * y * g = (g⁻¹ * C.D.x₁ * g) ^ 2 := by
      calc g⁻¹ * y * g = g⁻¹ * (C.D.x₁ * C.D.x₁) * g := by rw [hx1sq, hyz]
        _ = (g⁻¹ * C.D.x₁ * g) ^ 2 := by rw [pow_two]; group
    rw [hsq]; exact ((S : Subgroup G) ⊓ MGrp Ω W).pow_mem hgP 2
  · exact C.conj_mem_P_of_R hy hy1 hyz (hRS y hy)

include C in
theorem not_mem_P_conj {e : G} (heS : e ∈ (S : Subgroup G))
    (heR : ∀ y ∈ R, e * y = y * e) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hne : ∀ g : G, g * z * g⁻¹ ≠ e) {g : G}
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({e} : Set G),
      g⁻¹ * y * g ∈ (S : Subgroup G)) :
    g⁻¹ * e * g ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
  intro hfP
  have hΩ : HypOmegaGen Ω := C.hs.stand.hyp
  have hf2 : (g⁻¹ * e * g) * (g⁻¹ * e * g) = 1 := by
    calc _ = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [he2]; group
  have hf1 : g⁻¹ * e * g ≠ 1 := by
    intro h; apply he1
    have : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    rw [this, h]; group
  have hfz : g⁻¹ * e * g ≠ z := by
    intro h; apply hne g
    calc g * z * g⁻¹ = g * (g⁻¹ * e * g) * g⁻¹ := by rw [h]
      _ = e := by group
  have hRS : ∀ y ∈ R, g⁻¹ * y * g ∈ (S : Subgroup G) := fun y hy =>
    hg y ⟨C.hd.hR.2.2 hy, Subgroup.mem_centralizer_singleton_iff.mpr (heR y hy).symm⟩
  have hRP := C.conj_R_mem_P hRS
  have hmemT : ∀ x, x ∈ conjSub g⁻¹ R ↔ g * x * g⁻¹ ∈ R := fun x => by
    rw [mem_conjSub_iff, inv_inv]
  have hxe : ∀ x : G, g * x * g⁻¹ ∈ R → g⁻¹ * (g * x * g⁻¹) * g = x := fun x _ => by group
  have hTP : ∀ x ∈ conjSub g⁻¹ R, x ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro x hx
    have := hRP _ ((hmemT x).mp hx)
    rwa [hxe x ((hmemT x).mp hx)] at this
  have hfc : ∀ x ∈ conjSub g⁻¹ R, (g⁻¹ * e * g) * x = x * (g⁻¹ * e * g) := by
    intro x hx
    have hy := (hmemT x).mp hx
    have := heR _ hy
    calc (g⁻¹ * e * g) * x = g⁻¹ * (e * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * e) * g := by rw [this]
      _ = x * (g⁻¹ * e * g) := by group
  have hT : conjSub g⁻¹ R ∈ RSet Ω := RSet.conj hΩ.conjInvariant C.hd.hR.1 g⁻¹
  have hTS : conjSub g⁻¹ R ≤ (S : Subgroup G) := fun x hx => (hTP x hx).1
  by_cases hTR : conjSub g⁻¹ R = R
  · have hfR : ∀ y ∈ R, (g⁻¹ * e * g) * y = y * (g⁻¹ * e * g) := fun y hy =>
      hfc y (by rw [hTR]; exact hy)
    have hfR' := C.P_cent_R_le hfP hfR
    rcases C.hzK'.unique _ (C.hd.hR'.2.1 hfR') hf2 with h | h
    · exact hf1 h
    · exact hfz h
  · have hcomm := l6_7_proved G Ω hΩ S _ hT R C.hd.hR.1 hTS C.hd.hR.2.2 hTR
    have hTle : conjSub g⁻¹ R ≤ R' := fun x hx =>
      C.P_cent_R_le (hTP x hx) (fun y hy => hcomm x hx y hy)
    have hcard : Nat.card ↥R' ≤ Nat.card ↥(conjSub g⁻¹ R) := by
      rw [natCard_conjSub, C.h8, C.card_R', Nat.card_zpowers, C.orderOf_x₂]
    have hTR' : conjSub g⁻¹ R = R' := Subgroup.eq_of_le_of_card_ge hTle hcard
    have hfR' : ∀ y ∈ R', (g⁻¹ * e * g) * y = y * (g⁻¹ * e * g) := fun y hy =>
      hfc y (by rw [hTR']; exact hy)
    have hfR := C.P_cent_R'_le hfP hfR'
    rcases C.hzK.unique _ (C.hd.hR.2.1 hfR) hf2 with h | h
    · exact hf1 h
    · exact hfz h

end Ctx8F
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q8P
