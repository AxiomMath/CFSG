module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118DS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118F

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11d2_final {d d' q q' z : G} (hz2 : z * z = 1) (hqz : q * z = z * q)
    (hd' : d' = d ∨ d' = d * z) (hqne : q' ≠ q) (hqnez : q' ≠ q * z) :
    d' * q' ≠ d * q ∧ d' * q' ≠ d * q * z := by
  constructor
  · intro e
    rcases hd' with h | h
    · rw [h] at e
      exact hqne (mul_left_cancel e)
    · rw [h] at e
      have e1 : z * q' = q := mul_left_cancel (a := d) (by rw [← mul_assoc]; exact e)
      apply hqnez
      calc q' = z * (z * q') := by rw [← mul_assoc, hz2, one_mul]
        _ = z * q := by rw [e1]
        _ = q * z := hqz.symm
  · intro e
    rcases hd' with h | h
    · rw [h] at e
      exact hqnez (mul_left_cancel (a := d) (by rw [e, mul_assoc]))
    · rw [h] at e
      have e1 : z * q' = z * q := by
        apply mul_left_cancel (a := d)
        calc d * (z * q') = d * z * q' := by rw [mul_assoc]
          _ = d * q * z := e
          _ = d * (q * z) := by rw [mul_assoc]
          _ = d * (z * q) := by rw [hqz]
      exact hqne (mul_left_cancel e1)

theorem sec11d2_S6 [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) (h116 : Asc82Lemma116)
    (h117 : Asc82Lemma117) {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hC8 : IsD8 (secCTQ K1 K2 T)) {d q h : G}
    (hd : d ∈ secD K1 K2 R) (hq : q ∈ secQ K1 K2) (hd2 : d * d = z) (hq2 : q * q = z)
    (hh : h ∈ centralizer ({z} : Set G)) (hs : h⁻¹ * t * h = d * q) : False := by
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
  have hzDc : ∀ x ∈ secD K1 K2 R, x * z = z * x := fun x hx => hDQ x hx z hzQ
  have hdzc : d * z = z * d := hzDc d hd
  have hqzc : q * z = z * q := hQz q hq
  obtain ⟨a, x, hax⟩ := r.l113 G t L S z K1 K2 T R hctx
  obtain ⟨haR, haa, haN, haz, haD⟩ := sec11d2_a_facts hp hax
  have ainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hDsd := r.l114 G t L S z K1 K2 T R hctx
  have hD2 : IsPGroup 2 (secD K1 K2 R) := sec11_isDihSd_isPGroup hDsd
  obtain ⟨Y, hYD, hYc, hYi⟩ := sec11_isDihSd_exists_cyclic hDsd
  obtain ⟨c, hcC, hcY, hc4, hcc, t0, ht0C, ht0Y, ht0c⟩ :=
    sec11d2_setup hD2 hCD hYD hYc hYi hC8 hzC hz2 hz1 (fun x hx => hCQ x hx z hzQ)
  have hcomm_mod := sec11d2_comm_mod_z hD2 hYD hYc hYi hcY hc4 hcc (hCD ht0C) ht0Y ht0c haD haa
    (hax.a_comm c hcC) (hax.a_comm t0 ht0C) hzDc
  obtain ⟨X, hXD, hdX, hzX, hXel, hX8⟩ := sec11d2_exists_X_of_sq hCD hYD hYc hYi hC8 hzC hz2 hz1
    hcC hcY hc4 hcc hd hd2 hzDc
  have hXQ : ∀ x ∈ X, ∀ y ∈ secQ K1 K2, x * y = y * x := fun x hx y hy => hDQ x (hXD hx) y hy
  have hQel : IsElemAbelianMod z (secQ K1 K2) := (sec10KS_Q_elem hP5 hC5 hpsp h10).2
  have hUel : IsElemAbelianMod z (X ⊔ secQ K1 K2) :=
    sec11_isElemAbelianMod_sup hXQ (fun x' hx' => hDQ x' (hXD hx') z hzQ) hQz hXel hQel
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
    fun V hVT hzV hV hc' => sec11_lemmaB hWT hzW hWel hJT hVT hzV hV hc'
  have hCW : ∀ w ∈ secCTQ K1 K2 T ⊔ secQ K1 K2, w * t = t * w → w ∈ secW t K1 K2 := by
    intro w hw hwt
    obtain ⟨c1, hc1, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hCQ hw
    have hct : c1 * t = t * c1 := by
      have h1 : c1 * t * y = t * c1 * y := by
        calc c1 * t * y = c1 * (t * y) := by group
          _ = c1 * (y * t) := by rw [hQt y hy]
          _ = c1 * y * t := by group
          _ = t * (c1 * y) := hwt
          _ = t * c1 * y := by group
      exact mul_right_cancel h1
    have hcz : c1 ∈ zpowers t ⊔ zpowers z :=
      sec11_isD8_centralizer hC8 htC hzC ht2 hz2 (fun c2 hc2 => hCQ c2 hc2 z hzQ) ht1 hz1 htne
        hc1 hct
    have hle : (zpowers t ⊔ zpowers z : Subgroup G) ≤ secW t K1 K2 := by
      refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hzQ)
    exact Subgroup.mul_mem _ (hle hcz) (Subgroup.mem_sup_left hy)
  have hqa : a⁻¹ * q * a ∈ secQ K1 K2 := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) q).mp hq
    simpa using h1
  obtain ⟨hqq', hqne, hqnez⟩ := sec11d2_swap_Q hP5 hC5 hpsp h10 hax.swap haa hq hq2 hQz
  have hd'cases : a⁻¹ * d * a = d ∨ a⁻¹ * d * a = d * z := by
    have e : a⁻¹ * d * a = (a * d * a⁻¹ * d⁻¹) * d := by rw [ainv]; group
    rcases sec11d2_zpowers_cases hz2 (hcomm_mod d hd) with h1 | h1
    · left
      rw [e, h1, one_mul]
    · right
      rw [e, h1]
      exact hdzc.symm
  obtain ⟨d', hd'def⟩ : ∃ d' : G, d' = a⁻¹ * d * a := ⟨_, rfl⟩
  obtain ⟨q', hq'def⟩ : ∃ q' : G, q' = a⁻¹ * q * a := ⟨_, rfl⟩
  rw [← hd'def] at hd'cases
  rw [← hq'def] at hqa hqq' hqne hqnez
  have hd'D : d' ∈ secD K1 K2 R := by
    rcases hd'cases with h1 | h1
    · rw [h1]
      exact hd
    · rw [h1]
      exact Subgroup.mul_mem _ hd hzD
  have hd'X : d' ∈ X := by
    rcases hd'cases with h1 | h1
    · rw [h1]
      exact hdX
    · rw [h1]
      exact Subgroup.mul_mem _ hdX hzX
  have hdd' : d * d' = d' * d := by
    rcases hd'cases with h1 | h1
    · rw [h1]
    · rw [h1]
      calc d * (d * z) = d * (z * d) := by rw [hdzc]
        _ = (d * z) * d := by group
  have hd'q : q * d' = d' * q := (hDQ d' hd'D q hq).symm
  have hdq' : d * q' = q' * d := hDQ d hd q' hqa
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hh' : h * a ∈ centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc h * a * z = h * (a * z) := by group
      _ = h * (z * a) := by rw [haz]
      _ = (h * z) * a := by group
      _ = (z * h) * a := by rw [hhz]
      _ = z * (h * a) := by group
  have hu' : (h * a)⁻¹ * t * (h * a) = d' * q' := by
    calc (h * a)⁻¹ * t * (h * a) = a⁻¹ * (h⁻¹ * t * h) * a := by group
      _ = a⁻¹ * (d * q) * a := by rw [hs]
      _ = (a⁻¹ * d * a) * (a⁻¹ * q * a) := by group
      _ = d' * q' := by rw [hd'def, hq'def]
  have hdU : d ∈ X ⊔ secQ K1 K2 := Subgroup.mem_sup_left hdX
  have hu : h⁻¹ * t * h ∈ X ⊔ secQ K1 K2 := by
    rw [hs]
    exact Subgroup.mul_mem _ hdU (Subgroup.mem_sup_right hq)
  have hu'U : (h * a)⁻¹ * t * (h * a) ∈ X ⊔ secQ K1 K2 := by
    rw [hu']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd'X) (Subgroup.mem_sup_right hqa)
  have hcomm : (h⁻¹ * t * h) * ((h * a)⁻¹ * t * (h * a)) =
      ((h * a)⁻¹ * t * (h * a)) * (h⁻¹ * t * h) := by
    rw [hs, hu']
    calc d * q * (d' * q') = d * (q * d') * q' := by group
      _ = d * (d' * q) * q' := by rw [hd'q]
      _ = (d * d') * (q * q') := by group
      _ = (d' * d) * (q' * q) := by rw [hdd', ← hqq']
      _ = d' * (d * q') * q := by group
      _ = d' * (q' * d) * q := by rw [hdq']
      _ = d' * q' * (d * q) := by group
  obtain ⟨hne1, hne2⟩ := sec11d2_final hz2 hqzc hd'cases hqne hqnez
  rcases sec11_fusion hp h116 hctx hLB hCW hzU hUel hcard hh hh' hu hu'U hcomm with e | e
  · rw [hu', hs] at e
    exact hne1 e
  · rw [hu', hs] at e
    exact hne2 e

end CFSG.OddStandard.SmallF3.Omega
