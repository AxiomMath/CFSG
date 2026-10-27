module

public import CFSG.ClassicalInvolution.Asc77.AscS24BTor
public import CFSG.ClassicalInvolution.Asc77.AscS24BDec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

open Equiv in
theorem perm4_center : ∀ x : Perm (Fin 4), x * swap 0 1 = swap 0 1 * x →
    x * swap 1 2 = swap 1 2 * x → x * swap 2 3 = swap 2 3 * x → x = 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem fix_of_trivMu {t : G} (htN : t ∈ Subgroup.normalizer (W : Set G)) (hT : TrivMu Ω W t)
    (ρ : Thompson.Rep Ω W) : conjSub t ρ.K = ρ.K := by
  have hrM : ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D ρ.hR ρ.hr
  have h := hT ρ.r hrM
  have hN1 : t * ρ.r * t⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN ρ.r_mem_normalizer) (Subgroup.inv_mem _ htN)
  have h1 := Thompson.piG_of_mem_sup h
  rw [Thompson.piG_mul hN1 (Subgroup.inv_mem _ ρ.r_mem_normalizer),
    Thompson.piG_mul (Subgroup.mul_mem _ htN ρ.r_mem_normalizer) (Subgroup.inv_mem _ htN),
    Thompson.piG_mul htN ρ.r_mem_normalizer, Thompson.piG_inv htN,
    Thompson.piG_inv ρ.r_mem_normalizer] at h1
  refine (T7D.conj_stable C.D.c htN ρ ?_).1
  unfold Thompson.Rep.img
  exact mul_inv_eq_one.mp h1

theorem x₁_mem_MGrp : C.D.x₁ ∈ MGrp Ω W :=
  Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR ((congrArg (fun X => C.D.x₁ ∈ X) C.hR).mpr C.x₁_mem_R)

theorem x₃_mem_MGrp : C.D.x₃ ∈ MGrp Ω W :=
  Thompson.le_MGrp_of_mem_D C.D.F.ρ₃.hR C.x₃_mem_R₃

include C in
theorem W_le_P : W ≤ (S : Subgroup G) ⊓ MGrp Ω W := by
  intro w hw
  refine ⟨C.hd.hWS hw, ?_⟩
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ C.x₁_mem_MGrp a)
    (Subgroup.zpow_mem _ C.x₃_mem_MGrp b)

theorem conj_x₃_zpow_r (n : ℤ) :
    C.D.x₃ ^ n * C.D.F.ρ.r * (C.D.x₃ ^ n)⁻¹ = C.D.x₁ ^ (-n) * C.D.F.ρ.r := by
  have h1 : C.D.F.ρ.r * C.D.x₃ ^ (-n) * C.D.F.ρ.r⁻¹ = C.D.x₃ ^ (-n) * C.D.x₁ ^ (-n) := by
    rw [← conj_zpow, C.D.r₃, C.D.comm13.symm.mul_zpow]
  calc C.D.x₃ ^ n * C.D.F.ρ.r * (C.D.x₃ ^ n)⁻¹
      = C.D.x₃ ^ n * (C.D.F.ρ.r * C.D.x₃ ^ (-n) * C.D.F.ρ.r⁻¹) * C.D.F.ρ.r := by group
    _ = C.D.x₁ ^ (-n) * C.D.F.ρ.r := by rw [h1]; group

theorem r_mul_x₁_zpow (k : ℤ) : C.D.F.ρ.r * C.D.x₁ ^ k = C.D.x₁ ^ (-k) * C.D.F.ρ.r := by
  have h : C.D.F.ρ.r * C.D.x₁ ^ k * C.D.F.ρ.r⁻¹ = C.D.x₁ ^ (-k) := by
    rw [← conj_zpow, C.D.r₁, inv_zpow, zpow_neg]
  calc C.D.F.ρ.r * C.D.x₁ ^ k = C.D.F.ρ.r * C.D.x₁ ^ k * C.D.F.ρ.r⁻¹ * C.D.F.ρ.r := by group
    _ = C.D.x₁ ^ (-k) * C.D.F.ρ.r := by rw [h]

include C in
theorem inf_S_eq_R : K ⊓ (S : Subgroup G) = R :=
  C.hRsyl.2.2 _ inf_le_left S.isPGroup'.to_inf_right (le_inf C.hd.hR.2.1 C.hd.hR.2.2)

theorem card_R : Nat.card ↥R = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₁) := by
  have h := Thompson.D_card C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
  rw [← C.D.h₁] at h
  exact (congrArg (fun X : Subgroup G => Nat.card ↥X) C.hR).symm.trans h

theorem r_not_mem_zpowers : C.D.F.ρ.r ∉ Subgroup.zpowers C.D.x₁ := fun h =>
  C.D.F.ρ.hrW ((Subgroup.zpowers_le.mpr C.D.x₁_mem) h)

include C in
theorem exists_W_mul_mem_centralizer {t : G} (htS : t ∈ (S : Subgroup G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) (htK : conjSub t K = K) :
    ∃ w ∈ W, w * t ∈ Subgroup.centralizer (R : Set G) := by
  obtain ⟨r, hr⟩ : ∃ r, r = C.D.F.ρ.r := ⟨_, rfl⟩
  have hrR : r ∈ R := hr ▸ C.r_mem_R
  have hrU : r ∉ Subgroup.zpowers C.D.x₁ := hr ▸ C.r_not_mem_zpowers
  have hU : Subgroup.zpowers C.D.x₁ ≤ R := Subgroup.zpowers_le.mpr C.x₁_mem_R
  have htx : t * C.D.x₁ = C.D.x₁ * t :=
    (Subgroup.mem_centralizer_iff.mp htW _ C.D.x₁_mem).symm
  have htR : t * r * t⁻¹ ∈ R := by
    rw [← C.inf_S_eq_R]
    refine ⟨?_, S.mul_mem (S.mul_mem htS (C.hd.hR.2.2 hrR)) (S.inv_mem htS)⟩
    have h := conj_mem_conjSub (n := t) (hr ▸ C.r_mem_K : r ∈ K)
    rwa [htK] at h
  have hux : ∀ k : ℤ, t * C.D.x₁ ^ k * t⁻¹ = C.D.x₁ ^ k := fun k => by
    rw [← conj_zpow, htx, mul_inv_cancel_right]
  rcases mem_or_inv_mul_mem hU C.card_R hrR hrU htR with h | h
  · exfalso
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hrU
    have e : r = t⁻¹ * (t * r * t⁻¹) * t := by group
    rw [e, ← hk]
    have e2 : t⁻¹ * C.D.x₁ ^ k * t = C.D.x₁ ^ k := by
      calc t⁻¹ * C.D.x₁ ^ k * t = t⁻¹ * (t * C.D.x₁ ^ k * t⁻¹) * t := by rw [hux]
        _ = C.D.x₁ ^ k := by group
    rw [e2]
    exact Subgroup.zpow_mem_zpowers _ _
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have htr : t * r * t⁻¹ = r * C.D.x₁ ^ k := by
      rw [hk]; group
    obtain ⟨w, hw⟩ : ∃ w, w = C.D.x₃ ^ (-k) := ⟨_, rfl⟩
    have hwx : ∀ i : ℤ, w * C.D.x₁ ^ i = C.D.x₁ ^ i * w := fun i => by
      rw [hw]; exact (C.D.comm13.symm.zpow_zpow (-k) i).eq
    have hwr : w * r * w⁻¹ = C.D.x₁ ^ k * r := by
      have h2 := C.conj_x₃_zpow_r (-k)
      rw [neg_neg, ← hw, ← hr] at h2
      exact h2
    have hrk : r * C.D.x₁ ^ k = C.D.x₁ ^ (-k) * r := by rw [hr]; exact C.r_mul_x₁_zpow k
    have hc : (w * t) * r * (w * t)⁻¹ = r := by
      calc (w * t) * r * (w * t)⁻¹ = w * (t * r * t⁻¹) * w⁻¹ := by group
        _ = w * r * w⁻¹ * (w * C.D.x₁ ^ k * w⁻¹) := by rw [htr]; group
        _ = C.D.x₁ ^ k * (r * C.D.x₁ ^ k) := by rw [hwr, hwx k]; group
        _ = r := by rw [hrk]; group
    have hwW : w ∈ W := hw ▸ W.zpow_mem C.D.x₃_mem _
    refine ⟨w, hwW, ?_⟩
    have hax : (w * t) * C.D.x₁ = C.D.x₁ * (w * t) := by
      have h1 := hwx 1
      rw [zpow_one] at h1
      rw [mul_assoc, htx, ← mul_assoc, h1, mul_assoc]
    have has : (w * t) * r = r * (w * t) := by
      calc (w * t) * r = (w * t) * r * (w * t)⁻¹ * (w * t) := by group
        _ = r * (w * t) := by rw [hc]
    have hle := commute_of_index_two hU C.card_R hrR hrU hax has
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

include C in
theorem exists_mem_A [IsSimpleGroup G] (hng : NoGraph p f) {y : G}
    (hy : y ∈ (S : Subgroup G)) : ∃ x ∈ (S : Subgroup G) ⊓ MGrp Ω W, ∃ a ∈ C.A, y = x * a := by
  obtain ⟨x, hxP, t, htS, hT, rfl⟩ := C.exists_decomp hy
  have htW : t ∈ Subgroup.centralizer (W : Set G) :=
    hng G Ω K K' W S R R' z u C.hs C.hd C.h8 t htS hT
  have htN : t ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (W : Set G)) htW
  have hK : conjSub t K = K := by
    have h := C.fix_of_trivMu htN hT C.D.F.ρ
    rwa [C.hK] at h
  have hK' : conjSub t K' = K' := by
    have h := C.fix_of_trivMu htN hT C.D.F.ρ'
    rwa [C.hK'] at h
  have hJ := C.fix_of_trivMu htN hT C.D.F.ρ₃
  obtain ⟨w, hw, hwt⟩ := C.exists_W_mul_mem_centralizer htS htW hK
  have hwP := C.W_le_P hw
  refine ⟨x * w⁻¹, Subgroup.mul_mem _ hxP (Subgroup.inv_mem _ hwP), w * t, ?_, by group⟩
  refine (C.mem_A).mpr ⟨S.mul_mem (C.hd.hWS hw) htS, ?_, hwt, ?_, ?_⟩
  · refine Subgroup.mul_mem _ ?_ htW
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW v hv w hw
  · exact Subgroup.mul_mem _ (C.W_le_normalizer K' C.hs.hK'.1 ⟨C.x₂_mem_K', C.D.x₂_mem⟩
      C.orderOf_x₂ hw) (mem_normalizer_iff_conjSub_eq.mpr hK')
  · exact Subgroup.mul_mem _ (C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK
      ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃ hw) (mem_normalizer_iff_conjSub_eq.mpr hJ)

include C in
theorem mem_W_of_mem_P_A {a : G} (haP : a ∈ (S : Subgroup G) ⊓ MGrp Ω W) (haA : a ∈ C.A) :
    a ∈ W := by
  obtain ⟨haS, haW, haR, haK', haJ⟩ := (C.mem_A).mp haA
  have haN : a ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (W : Set G)) haW
  have haK : conjSub a C.D.F.ρ.K = C.D.F.ρ.K := by
    rw [C.hK]
    exact conjSub_eq_of_commute C.hs.stand.hyp C.hs.stand.mem C.x₁_mem_K C.orderOf_x₁
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
    exact Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW v hv z hzW
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (e189_commute_of_mem C.hzK (C.hd.hR.2.1 hv)).symm
  · exact C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃ hzW
  · show z ∈ Subgroup.centralizer (R' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (e189_commute_of_mem C.hzK' (C.hd.hR'.2.1 hv)).symm

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
