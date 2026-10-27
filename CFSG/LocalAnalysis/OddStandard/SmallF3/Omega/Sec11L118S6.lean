module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118DS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118K1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118K2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118W

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_118_S6 [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) (h116 : Asc82Lemma116)
    (h117 : Asc82Lemma117) {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hC8 : IsD8 (secCTQ K1 K2 T)) {d q h : G}
    (hd : d ∈ secD K1 K2 R) (hq : q ∈ secQ K1 K2) (hdq : d * q = q * d) (hd2 : d * d = 1)
    (hq2 : q * q = 1) (hqz : q ∉ zpowers z) (hh : h ∈ centralizer ({z} : Set G))
    (hs : h⁻¹ * t * h = d * q) : False := by
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hP5 := hp.facts.pockets5
  have hC5 := hp.facts.centZ5
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  obtain ⟨ht2, hz2, htz, ht1, hz1⟩ := sec11_invols h10
  obtain ⟨hzQ, hQS, hQL, hQz, hQt⟩ := sec11_Q_facts hp h10
  have hzL : z ∈ L := hQL hzQ
  have htne : t ≠ z := by
    intro h0
    exact (hp.basic G t L S z hctx.toSec10Z).2.2.1 (by rw [h0]; exact hzL)
  have hzD : z ∈ secD K1 K2 R := sec11_z_mem_D hp hctx
  have hDQ : ∀ x ∈ secD K1 K2 R, ∀ y ∈ secQ K1 K2, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1 y hy).symm
  have hCQ : ∀ x ∈ secCTQ K1 K2 T, ∀ y ∈ secQ K1 K2, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1 y hy).symm
  have hCD : secCTQ K1 K2 T ≤ secD K1 K2 R := inf_le_inf_left _ hctx.T_le
  have hzC : z ∈ secCTQ K1 K2 T :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => hQz y hy,
      hctx.S_le hctx.mem_S⟩
  have htC : t ∈ secCTQ K1 K2 T :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => (hQt y hy).symm,
      hctx.S_le (sec11_t_mem_S hp h10)⟩
  have hdz : d ∉ zpowers z := by
    intro hdz'
    rcases sec11_eq_one_or_of_mem_zpowers hz2 hdz' with h1 | h1
    · exact hp.r10.l108 G t L S z K1 K2 h10 h (by rw [hs, h1, one_mul]; exact hQL hq)
    · exact hp.r10.l108 G t L S z K1 K2 h10 h
        (by rw [hs, h1]; exact hQL (Subgroup.mul_mem _ hzQ hq))
  have hDsd := r.l114 G t L S z K1 K2 T R hctx
  obtain ⟨Y, hYD, hYc, hYi⟩ := sec11_isDihSd_exists_cyclic hDsd
  obtain ⟨a0, ha0, b0, hb0, hab0⟩ := sec11_isD8_nonabelian hC8
  obtain ⟨X, hXD, hdX, hzX, hXel, hX8⟩ := sec11_exists_X_of_cyclic
    (sec11_isDihSd_isPGroup hDsd) hYD hYc hYi hzD hz2 hz1 (fun x hx => hDQ x hx z hzQ)
    ⟨a0, hCD ha0, b0, hCD hb0, hab0⟩ hd hd2 hdz
  have hXQ : ∀ x ∈ X, ∀ y ∈ secQ K1 K2, x * y = y * x := fun x hx y hy => hDQ x (hXD hx) y hy
  have hQel : IsElemAbelianMod z (secQ K1 K2) := (sec10KS_Q_elem hP5 hC5 hpsp h10).2
  have hUel : IsElemAbelianMod z (X ⊔ secQ K1 K2) :=
    sec11_isElemAbelianMod_sup hXQ (fun a ha => hDQ a (hXD ha) z hzQ) hQz hXel hQel
  have hzU : z ∈ X ⊔ secQ K1 K2 := Subgroup.mem_sup_left hzX
  have hcard : Nat.card ↥(secCTQ K1 K2 T ⊔ secQ K1 K2) ≤ Nat.card ↥(X ⊔ secQ K1 K2) :=
    sec11_card_CQ_le_card_XQ hCQ hXQ (sec10KS_Q_center hP5 hC5 hpsp h10) hzC hzX hzQ hz2 hz1
      (sec11_isD8_card hC8) hX8
  obtain ⟨hWel, hJT, -⟩ := h117 G t L S z K1 K2 T R hctx
  have hWT : secCTQ K1 K2 T ⊔ secQ K1 K2 ≤ T := sup_le inf_le_right (hQS.trans hctx.S_le)
  have hzW : z ∈ secCTQ K1 K2 T ⊔ secQ K1 K2 := Subgroup.mem_sup_right hzQ
  have hLB : ∀ V : Subgroup G, V ≤ T → z ∈ V → IsElemAbelianMod z V →
      Nat.card ↥(secCTQ K1 K2 T ⊔ secQ K1 K2) ≤ Nat.card ↥V →
        V ≤ secCTQ K1 K2 T ⊔ secQ K1 K2 :=
    fun V hVT hzV hV hc => sec11_lemmaB hWT hzW hWel hJT hVT hzV hV hc
  have hCW : ∀ w ∈ secCTQ K1 K2 T ⊔ secQ K1 K2, w * t = t * w → w ∈ secW t K1 K2 := by
    intro w hw hwt
    obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hCQ hw
    have hct : c * t = t * c := by
      have h1 : c * t * y = t * c * y := by
        calc c * t * y = c * (t * y) := by group
          _ = c * (y * t) := by rw [hQt y hy]
          _ = c * y * t := by group
          _ = t * (c * y) := hwt
          _ = t * c * y := by group
      exact mul_right_cancel h1
    have hcz : c ∈ zpowers t ⊔ zpowers z :=
      sec11_isD8_centralizer hC8 htC hzC ht2 hz2 (fun c hc => hCQ c hc z hzQ) ht1 hz1 htne hc hct
    have hle : (zpowers t ⊔ zpowers z : Subgroup G) ≤ secW t K1 K2 := by
      refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hzQ)
    exact Subgroup.mul_mem _ (hle hcz) (Subgroup.mem_sup_left hy)
  obtain ⟨g, hg, hgcomm, hgne, hgnez⟩ := sec11_exists_swap_conj hP5 hC5 hpsp h10 hq hq2 hqz
  obtain ⟨k, hk, hkq⟩ := sec11_exists_KD_conj hp r.l115c hctx hg
  have hkc : ∀ x ∈ secD K1 K2 R, k * x = x * k := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (sec11_KD_le_centralizer _ hk) x hx).symm
  have hkz : k * z = z * k := hkc z hzD
  have hgq : g * q * g⁻¹ ∈ secQ K1 K2 := sec11_conj_mem_Q hg hq
  have hdq' : d * (g * q * g⁻¹) = (g * q * g⁻¹) * d := hDQ d hd _ hgq
  have hh' : h * k⁻¹ ∈ centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp hh
    calc h * k⁻¹ * z = h * (k⁻¹ * z * k) * k⁻¹ := by group
      _ = h * z * k⁻¹ := by
          have : k⁻¹ * z * k = z := by
            calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
              _ = k⁻¹ * (k * z) := by rw [hkz]
              _ = z := by group
          rw [this]
      _ = z * h * k⁻¹ := by rw [h1]
      _ = z * (h * k⁻¹) := by group
  have hu' : (h * k⁻¹)⁻¹ * t * (h * k⁻¹) = d * (g * q * g⁻¹) := by
    calc (h * k⁻¹)⁻¹ * t * (h * k⁻¹) = k * (h⁻¹ * t * h) * k⁻¹ := by group
      _ = k * (d * q) * k⁻¹ := by rw [hs]
      _ = (k * d) * q * k⁻¹ := by group
      _ = (d * k) * q * k⁻¹ := by rw [hkc d hd]
      _ = d * (k * q * k⁻¹) := by group
      _ = d * (g * q * g⁻¹) := by rw [hkq q hq]
  have hdU : d ∈ X ⊔ secQ K1 K2 := Subgroup.mem_sup_left hdX
  have hu : h⁻¹ * t * h ∈ X ⊔ secQ K1 K2 := by
    rw [hs]
    exact Subgroup.mul_mem _ hdU (Subgroup.mem_sup_right hq)
  have hu'U : (h * k⁻¹)⁻¹ * t * (h * k⁻¹) ∈ X ⊔ secQ K1 K2 := by
    rw [hu']
    exact Subgroup.mul_mem _ hdU (Subgroup.mem_sup_right hgq)
  have hcomm : (h⁻¹ * t * h) * ((h * k⁻¹)⁻¹ * t * (h * k⁻¹)) =
      ((h * k⁻¹)⁻¹ * t * (h * k⁻¹)) * (h⁻¹ * t * h) := by
    rw [hs, hu']
    calc d * q * (d * (g * q * g⁻¹)) = d * (q * d) * (g * q * g⁻¹) := by group
      _ = d * (d * q) * (g * q * g⁻¹) := by rw [← hdq]
      _ = d * d * (q * (g * q * g⁻¹)) := by group
      _ = d * d * ((g * q * g⁻¹) * q) := by rw [hgcomm]
      _ = d * (d * (g * q * g⁻¹)) * q := by group
      _ = d * ((g * q * g⁻¹) * d) * q := by rw [hdq']
      _ = d * (g * q * g⁻¹) * (d * q) := by group
  rcases sec11_fusion hp h116 hctx hLB hCW hzU hUel hcard hh hh' hu hu'U hcomm with e | e
  · rw [hu', hs] at e
    exact hgne (mul_left_cancel e)
  · rw [hu', hs] at e
    have e' : d * (g * q * g⁻¹) = d * (q * z) := by rw [e, mul_assoc]
    exact hgnez (mul_left_cancel e')

end CFSG.OddStandard.SmallF3.Omega
