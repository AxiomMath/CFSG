module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111Na
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_cube_comm [Finite G] (hK0 : Asc82Lemma10K0) (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) {x : G}
    (hx : x ∈ normalizer (secK0 t z : Set G)) (hxQ : ∀ q ∈ secQ K1 K2, q * x = x * q)
    {c : G} (hcK : c ∈ K1 ⊔ K2) (hc3 : c ^ 3 = 1) :
    x * c * x⁻¹ * c⁻¹ ∈ oddCoreIn (secK0 t z) := by
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hK0 hctx
  have hcK0 : c ∈ secK0 t z := hKle hcK
  have hxc : x * c * x⁻¹ ∈ secK0 t z := (Subgroup.mem_normalizer_iff.mp hx c).mp hcK0
  have hxq : ∀ q ∈ secQ K1 K2, x⁻¹ * q * x = q := by
    intro q hq
    calc x⁻¹ * q * x = x⁻¹ * (q * x) := by group
      _ = x⁻¹ * (x * q) := by rw [hxQ q hq]
      _ = q := by group
  have hxq' : ∀ q ∈ secQ K1 K2, x * q * x⁻¹ = q := by
    intro q hq
    calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [← hxQ q hq]
      _ = q := by group
  have hg : c⁻¹ * (x * c * x⁻¹) ∈ secK0 t z :=
    (secK0 t z).mul_mem ((secK0 t z).inv_mem hcK0) hxc
  have hgc : ∀ q ∈ secQ K1 K2,
      (c⁻¹ * (x * c * x⁻¹)) * q = q * (c⁻¹ * (x * c * x⁻¹)) := by
    intro q hq
    have hq1 : c * q * c⁻¹ ∈ secQ K1 K2 := sec11_conj_mem_Q hcK hq
    have e2 : x * (c * q * c⁻¹) * x⁻¹ = c * q * c⁻¹ := hxq' _ hq1
    have hconj : (c⁻¹ * (x * c * x⁻¹)) * q * (c⁻¹ * (x * c * x⁻¹))⁻¹ = q := by
      calc (c⁻¹ * (x * c * x⁻¹)) * q * (c⁻¹ * (x * c * x⁻¹))⁻¹
          = c⁻¹ * x * c * (x⁻¹ * q * x) * c⁻¹ * x⁻¹ * c := by group
        _ = c⁻¹ * x * c * q * c⁻¹ * x⁻¹ * c := by rw [hxq q hq]
        _ = c⁻¹ * (x * (c * q * c⁻¹) * x⁻¹) * c := by group
        _ = c⁻¹ * (c * q * c⁻¹) * c := by rw [e2]
        _ = q := by group
    calc (c⁻¹ * (x * c * x⁻¹)) * q
        = ((c⁻¹ * (x * c * x⁻¹)) * q * (c⁻¹ * (x * c * x⁻¹))⁻¹) * (c⁻¹ * (x * c * x⁻¹)) := by
          group
      _ = q * (c⁻¹ * (x * c * x⁻¹)) := by rw [hconj]
  obtain ⟨n, hn, e, he, hge⟩ := sec11_cent_K0_Q hK0 hP5 hC5 hpsp hctx hg hgc
  have hxc_eq : x * c * x⁻¹ = c * (n * e) := by
    calc x * c * x⁻¹ = c * (c⁻¹ * (x * c * x⁻¹)) := by group
      _ = c * (n * e) := by rw [hge]
  have hcube : (x * c * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hc3]
    group
  have hnK0 : n ∈ secK0 t z := CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hn
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzc : ∀ y ∈ secK0 t z, Commute z y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (sec11_K0_le t z hy).2 z (Set.mem_singleton z)
  have he2 : e ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers he).trans (by rw [hz2]))
  have he3 : e ^ 3 = e := by rw [pow_succ, he2, one_mul]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp he
  have hec : Commute e c := by
    rw [← hj]
    exact (hzc c hcK0).zpow_left j
  have hen : Commute e n := by
    rw [← hj]
    exact (hzc n hnK0).zpow_left j
  have hcn3 : (c * n) ^ 3 ∈ oddCoreIn (secK0 t z) := by
    have hc2K0 : c ^ 2 ∈ secK0 t z := (secK0 t z).pow_mem hcK0 2
    have h1 : c * n * c⁻¹ ∈ oddCoreIn (secK0 t z) :=
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hcK0 hn
    have h2 : c ^ 2 * n * (c ^ 2)⁻¹ ∈ oddCoreIn (secK0 t z) :=
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hc2K0 hn
    have heq : (c * n) ^ 3 = (c * n * c⁻¹) * (c ^ 2 * n * (c ^ 2)⁻¹) * n := by
      calc (c * n) ^ 3 = c * n * c * n * c * n := by rw [pow_succ, pow_succ, pow_one]; group
        _ = (c * n * c⁻¹) * (c ^ 2 * n * (c ^ 2)⁻¹) * (c ^ 3 * n * (c ^ 3)⁻¹) * c ^ 3 := by
          group
        _ = (c * n * c⁻¹) * (c ^ 2 * n * (c ^ 2)⁻¹) * n := by rw [hc3]; group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) hn
  have hprod : (c * n) ^ 3 * e = 1 := by
    calc (c * n) ^ 3 * e = (c * n) ^ 3 * e ^ 3 := by rw [he3]
      _ = (c * n * e) ^ 3 := ((hec.symm.mul_left hen.symm).mul_pow 3).symm
      _ = (c * (n * e)) ^ 3 := by rw [mul_assoc]
      _ = (x * c * x⁻¹) ^ 3 := by rw [hxc_eq]
      _ = 1 := hcube
  have heN : e ∈ oddCoreIn (secK0 t z) := by
    rw [eq_inv_of_mul_eq_one_right hprod]
    exact Subgroup.inv_mem _ hcn3
  have hzQ : z ∈ secQ K1 K2 := (sec10KS_Q_elem hP5 hC5 hpsp hctx).1
  have heQ : e ∈ secQ K1 K2 := (Subgroup.zpowers_le.mpr hzQ) he
  have he1 : e = 1 := sec11_Q_inf_oddCore heQ heN
  have hfin : x * c * x⁻¹ * c⁻¹ = c * n * c⁻¹ := by
    calc x * c * x⁻¹ * c⁻¹ = c * (n * e) * c⁻¹ := by rw [hxc_eq]
      _ = c * n * c⁻¹ := by rw [he1]; group
  rw [hfin]
  exact CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hcK0 hn

theorem asc82Lemma111N_of (hp : Asc82Pre11) (hT : Asc82Step111T) : Asc82Lemma111N := by
  intro G _ _ t L S z K1 K2 T R hctx
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hK0 : Asc82Lemma10K0 := hp.r10.lK0
  have hP5 : Asc82FactPockets5 := hp.facts.pockets5
  have hC5 : Asc82FactCentZ5 := hp.facts.centZ5
  obtain ⟨h1, h2, h3, h4⟩ := hT G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp hctx.sylowT hctx.S_le
  refine ⟨h1, h2, h3, fun x hxT => ⟨fun hxQ k hk => ?_, fun hx => ?_⟩⟩
  · have hx0 : x ∈ normalizer (secK0 t z : Set G) := h3 hxT
    have hxQ' : ∀ q ∈ secQ K1 K2, q * x = x * q := Subgroup.mem_centralizer_iff.mp hxQ
    have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hK0 hctx.toSec10Ctx
    have hNle : oddCoreIn (secK0 t z) ≤ secK0 t z := CFSG.ClassicalInvolution.Balance.oddCoreIn_le _
    let P : Subgroup G :=
      { carrier := {k | k ∈ secK0 t z ∧ x * k * x⁻¹ * k⁻¹ ∈ oddCoreIn (secK0 t z)}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨(secK0 t z).mul_mem ha hb, ?_⟩
          have heq : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
              (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
          rw [heq]
          exact Subgroup.mul_mem _ ha'
            (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn ha hb')
        one_mem' := ⟨(secK0 t z).one_mem, by simp⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨(secK0 t z).inv_mem ha, ?_⟩
          have heq : x * a⁻¹ * x⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by
            group
          rw [heq]
          exact CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn ((secK0 t z).inv_mem ha)
            (Subgroup.inv_mem _ ha') }
    have hmemP : ∀ k, k ∈ P ↔ k ∈ secK0 t z ∧ x * k * x⁻¹ * k⁻¹ ∈ oddCoreIn (secK0 t z) :=
      fun k => Iff.rfl
    have hN : oddCoreIn (secK0 t z) ≤ P := by
      intro n hn
      refine (hmemP n).mpr ⟨hNle hn, ?_⟩
      exact Subgroup.mul_mem _ (sec11_conj_mem_oddCoreIn hx0 hn) (Subgroup.inv_mem _ hn)
    have hQP : secQ K1 K2 ≤ P := by
      intro q hq
      refine (hmemP q).mpr ⟨hKle (sec11_Q_le_sup K1 K2 hq), ?_⟩
      have : x * q * x⁻¹ * q⁻¹ = 1 := by
        rw [show x * q = q * x from (hxQ' q hq).symm]
        group
      rw [this]
      exact Subgroup.one_mem _
    have hcP : ∀ c, c ∈ K1 ⊔ K2 → c ^ 3 = 1 → c ∈ P := fun c hc hc3 =>
      (hmemP c).mpr ⟨hKle hc, sec11_cube_comm hK0 hP5 hC5 hpsp hctx.toSec10Ctx hx0 hxQ' hc hc3⟩
    have hK1 : K1 ≤ P := by
      intro k hk
      obtain ⟨q, c, hq, hc, hc3, rfl⟩ := sec11_pocket_decomp hP5 hC5 hpsp hctx.toSec10Ctx hk
      exact P.mul_mem (hQP hq) (hcP c (Subgroup.mem_sup_left hc) hc3)
    have hK2 : K2 ≤ P := by
      intro k hk
      obtain ⟨q, c, hq, hc, hc3, rfl⟩ := sec11_pocket_decomp2 hP5 hC5 hpsp hctx.toSec10Ctx hk
      exact P.mul_mem (hQP hq) (hcP c (Subgroup.mem_sup_right hc) hc3)
    have hK0P : secK0 t z ≤ P := by
      rw [sec11_K0_eq_sup hK0 hctx.toSec10Ctx]
      exact sup_le (sup_le hN hK1) hK2
    exact ((hmemP k).mp (hK0P hk)).2
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hK0 hctx.toSec10Ctx
    have hqK0 : q ∈ secK0 t z := hKle (sec11_Q_le_sup K1 K2 hq)
    have hcN := hx q hqK0
    have hxqQ : x * q * x⁻¹ ∈ secQ K1 K2 := (Subgroup.mem_normalizer_iff.mp (h4 hxT) q).mp hq
    have hcQ : x * q * x⁻¹ * q⁻¹ ∈ secQ K1 K2 :=
      (secQ K1 K2).mul_mem hxqQ ((secQ K1 K2).inv_mem hq)
    have hone := sec11_Q_inf_oddCore hcQ hcN
    have h5 : x * q * x⁻¹ = q := mul_inv_eq_one.mp hone
    calc q * x = (x * q * x⁻¹) * x := by rw [h5]
      _ = x * q := by group

end CFSG.OddStandard.SmallF3.Omega
