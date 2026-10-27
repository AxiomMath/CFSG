module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111Na
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_KD_le_centralizer (D : Subgroup G) : secKD D ≤ centralizer (D : Set G) := by
  unfold secKD oTwoRes
  exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)

private theorem sec11_K0_conj_mem_Q [Finite G] (hp : Asc82Pre11) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) {x q : G} (hx : x ∈ secK0 t z)
    (hq : q ∈ secQ K1 K2) : x * q * x⁻¹ ∈ secQ K1 K2 := by
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hqK0 : q ∈ secK0 t z :=
    sec11_K_le_K0 hp.r10.lK0 h10 (sec11_Q_le_sup K1 K2 hq)
  have hxqK0 : x * q * x⁻¹ ∈ secK0 t z :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hqK0) (Subgroup.inv_mem _ hx)
  obtain ⟨m, hm⟩ := (sec11_Q_isPGroup K1 K2).exists_orderOf_eq_pow (⟨q, hq⟩ : secQ K1 K2)
  have hqpow : q ^ (2 ^ m) = 1 := by
    rw [← hm, ← Subgroup.orderOf_coe (⟨q, hq⟩ : secQ K1 K2)]
    exact pow_orderOf_eq_one q
  have hcp : (MulAut.conj x) q = x * q * x⁻¹ := MulAut.conj_apply x q
  have hconjpow : (x * q * x⁻¹) ^ (2 ^ m) = 1 := by
    rw [← hcp, ← map_pow, hqpow, map_one]
  exact sec10T_two_elem_K0 hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5 hp.basic
    h10 hxqK0 ⟨m, hconjpow⟩

theorem sec11_exists_KD_conj [Finite G] (hp : Asc82Pre11) (h115c : Asc82Lemma115c) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) {g : G} (hg : g ∈ K1 ⊔ K2) :
    ∃ k ∈ secKD (secD K1 K2 R), ∀ q ∈ secQ K1 K2, k * q * k⁻¹ = g * q * g⁻¹ := by
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hdec : secK0 t z = secKD (secD K1 K2 R) ⊔ oddCoreIn (secK0 t z) :=
    (h115c G t L S z K1 K2 T R hctx).2
  have hKD_le_K0 : secKD (secD K1 K2 R) ≤ secK0 t z := by
    rw [hdec]; exact le_sup_left
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hp.r10.lK0 h10
  have hgK0 : g ∈ secK0 t z := hKle hg
  have hnorm : secKD (secD K1 K2 R) ≤ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    hKD_le_K0.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  have hg' : g ∈ oddCoreIn (secK0 t z) ⊔ secKD (secD K1 K2 R) := by
    rw [sup_comm, ← hdec]
    exact hgK0
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
  obtain ⟨n, hn, k0, hk0, rfl⟩ := Set.mem_mul.mp hg'
  refine ⟨k0, hk0, fun q hq => ?_⟩
  set q1 : G := k0 * q * k0⁻¹ with hq1def
  have hq1 : q1 ∈ secQ K1 K2 := by
    rw [hq1def]
    exact sec11_K0_conj_mem_Q hp hctx (hKD_le_K0 hk0) hq
  have hnK0 : n ∈ secK0 t z := (CFSG.ClassicalInvolution.Balance.oddCoreIn_le (secK0 t z)) hn
  have hq1K0 : q1 ∈ secK0 t z := hKle (sec11_Q_le_sup K1 K2 hq1)
  have hcQ : (n * q1 * n⁻¹) * q1⁻¹ ∈ secQ K1 K2 :=
    Subgroup.mul_mem _ (sec11_K0_conj_mem_Q hp hctx hnK0 hq1) (Subgroup.inv_mem _ hq1)
  have hcN : (n * q1 * n⁻¹) * q1⁻¹ ∈ oddCoreIn (secK0 t z) := by
    have h1 : q1 * n⁻¹ * q1⁻¹ ∈ oddCoreIn (secK0 t z) :=
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hq1K0 (Subgroup.inv_mem _ hn)
    have h2 : n * (q1 * n⁻¹ * q1⁻¹) ∈ oddCoreIn (secK0 t z) :=
      Subgroup.mul_mem _ hn h1
    simpa [mul_assoc] using h2
  have hfinal : n * q1 * n⁻¹ = q1 := mul_inv_eq_one.mp (sec11_Q_inf_oddCore hcQ hcN)
  have hgq : (n * k0) * q * (n * k0)⁻¹ = n * q1 * n⁻¹ := by
    rw [hq1def]; group
  rw [hgq, hfinal]

end CFSG.OddStandard.SmallF3.Omega
