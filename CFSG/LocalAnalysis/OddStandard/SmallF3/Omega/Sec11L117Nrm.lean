module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Fact
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111Na
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_twoCoreIn_conj_mem (X : Subgroup G) {k q : G} (hk : k ∈ X) (hq : q ∈ twoCoreIn X) :
    k * q * k⁻¹ ∈ twoCoreIn X := by
  have hmem : (⟨k, hk⟩ : ↥X) * ⟨q, twoCoreIn_le_self X hq⟩ * (⟨k, hk⟩ : ↥X)⁻¹ ∈
      (twoCoreIn X).subgroupOf X :=
    (normal_subgroupOf_twoCoreIn X).conj_mem ⟨q, twoCoreIn_le_self X hq⟩
      (Subgroup.mem_subgroupOf.mpr hq) ⟨k, hk⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem sec11_K0_normQ [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {k q : G} (hk : k ∈ secK0 t z)
    (hq : q ∈ secQ K1 K2) : k * q * k⁻¹ ∈ secQ K1 K2 := by
  have hqK0 : q ∈ secK0 t z :=
    sec11_K_le_K0 hp.r10.lK0 hctx (sec11_Q_le_sup K1 K2 hq)
  have hkqK0 : k * q * k⁻¹ ∈ secK0 t z :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hqK0) (Subgroup.inv_mem _ hk)
  obtain ⟨m, hm⟩ := (sec11_Q_isPGroup K1 K2).exists_orderOf_eq_pow (⟨q, hq⟩ : secQ K1 K2)
  have hqpow : q ^ (2 ^ m) = 1 := by
    rw [← hm, ← Subgroup.orderOf_coe (⟨q, hq⟩ : secQ K1 K2)]
    exact pow_orderOf_eq_one q
  have hcp : (MulAut.conj k) q = k * q * k⁻¹ := MulAut.conj_apply k q
  have hconjpow : (k * q * k⁻¹) ^ (2 ^ m) = 1 := by
    rw [← hcp, ← map_pow, hqpow, map_one]
  exact sec10T_two_elem_K0 hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5 hp.basic
    hctx hkqK0 ⟨m, hconjpow⟩

theorem sec11_N_centQ [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {n q : G}
    (hn : n ∈ oddCoreIn (secK0 t z)) (hq : q ∈ secQ K1 K2) : n * q = q * n := by
  have hnK0 : n ∈ secK0 t z := CFSG.ClassicalInvolution.Balance.oddCoreIn_le (secK0 t z) hn
  have hqK0 : q ∈ secK0 t z :=
    sec11_K_le_K0 hp.r10.lK0 hctx (sec11_Q_le_sup K1 K2 hq)
  have hcQ : (n * q * n⁻¹) * q⁻¹ ∈ secQ K1 K2 :=
    Subgroup.mul_mem _ (sec11_K0_normQ hp hctx hnK0 hq) (Subgroup.inv_mem _ hq)
  have hcN : (n * q * n⁻¹) * q⁻¹ ∈ oddCoreIn (secK0 t z) := by
    have h1 : q * n⁻¹ * q⁻¹ ∈ oddCoreIn (secK0 t z) :=
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hqK0 (Subgroup.inv_mem _ hn)
    have h2 : n * (q * n⁻¹ * q⁻¹) ∈ oddCoreIn (secK0 t z) := Subgroup.mul_mem _ hn h1
    simpa [mul_assoc] using h2
  have h1 : n * q * n⁻¹ = q := mul_inv_eq_one.mp (sec11_Q_inf_oddCore hcQ hcN)
  calc n * q = (n * q * n⁻¹) * n := by group
    _ = q * n := by rw [h1]

theorem sec11_K1_inf_N [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {k : G} (hk : k ∈ K1)
    (hkN : k ∈ oddCoreIn (secK0 t z)) : k = 1 := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hcent : ∀ b ∈ twoCoreIn K1, k * b = b * k := by
    intro b hb
    have hbQ : b ∈ secQ K1 K2 := by
      rw [sec11_Q_eq_sup hp hctx]
      exact Subgroup.mem_sup_left hb
    exact sec11_N_centQ hp hctx hkN hbQ
  have hkz : k ∈ zpowers z :=
    sec10KS_cent_Qi hp.facts.pockets5 hp.facts.centZ5 hpsp hctx k hk hcent
  have hzQ : z ∈ secQ K1 K2 := (sec11_Q_facts hp hctx).1
  have hkQ : k ∈ secQ K1 K2 := Subgroup.zpowers_le.mpr hzQ hkz
  exact sec11_Q_inf_oddCore hkQ hkN

theorem sec11_K2_inf_N [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {k : G} (hk : k ∈ K2)
    (hkN : k ∈ oddCoreIn (secK0 t z)) : k = 1 := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hcent : ∀ b ∈ twoCoreIn K2, k * b = b * k := by
    intro b hb
    have hbQ : b ∈ secQ K1 K2 := by
      rw [sec11_Q_eq_sup hp hctx]
      exact Subgroup.mem_sup_right hb
    exact sec11_N_centQ hp hctx hkN hbQ
  have hkz : k ∈ zpowers z :=
    sec10KS_cent_Qi hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.swap k hk hcent
  have hzQ : z ∈ secQ K1 K2 := (sec11_Q_facts hp hctx).1
  have hkQ : k ∈ secQ K1 K2 := Subgroup.zpowers_le.mpr hzQ hkz
  exact sec11_Q_inf_oddCore hkQ hkN

private theorem sec11_pow_mul_normalizer {N : Subgroup G} {y n : G}
    (hy : y ∈ normalizer (N : Set G)) (hn : n ∈ N) (j : ℕ) :
    ∃ m ∈ N, (y * n) ^ j = y ^ j * m := by
  induction j with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ j ih =>
      obtain ⟨m, hm, hjm⟩ := ih
      refine ⟨(y⁻¹ * m * y) * n, Subgroup.mul_mem _ ?_ hn, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * m * y)).mpr ?_
        rwa [show y * (y⁻¹ * m * y) * y⁻¹ = m by group]
      · rw [pow_succ, hjm]
        group

theorem sec11_Q_inf_K1N [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {y : G} (hy : y ∈ secQ K1 K2)
    (hyX : y ∈ K1 ⊔ oddCoreIn (secK0 t z)) : y ∈ twoCoreIn K1 := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hp.r10.lK0 hctx
  have hK1norm : K1 ≤ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    (le_sup_left.trans hKle).trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K1
    (oddCoreIn (secK0 t z)) hK1norm] at hyX
  obtain ⟨k, hk, n, hn, hkny⟩ := Set.mem_mul.mp hyX
  obtain ⟨m, hm⟩ := (sec11_Q_isPGroup K1 K2).exists_orderOf_eq_pow (⟨y, hy⟩ : secQ K1 K2)
  have hy1 : y ^ (2 ^ m) = 1 := by
    rw [← hm, ← Subgroup.orderOf_coe (⟨y, hy⟩ : secQ K1 K2)]
    exact pow_orderOf_eq_one y
  have hyK0 : y ∈ secK0 t z := hKle (sec11_Q_le_sup K1 K2 hy)
  have hynorm : y ∈ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hyK0
  obtain ⟨m', hm'N, hpow⟩ := sec11_pow_mul_normalizer (N := oddCoreIn (secK0 t z))
    hynorm (Subgroup.inv_mem _ hn) (2 ^ m)
  have hk_eq : y * n⁻¹ = k := by rw [← hkny]; group
  have hpow' : k ^ (2 ^ m) = m' := by rw [← hk_eq, hpow, hy1, one_mul]
  have hk_pow_N : k ^ (2 ^ m) ∈ oddCoreIn (secK0 t z) := by rw [hpow']; exact hm'N
  have hk_pow_one : k ^ (2 ^ m) = 1 :=
    sec11_K1_inf_N hp hctx (K1.pow_mem hk (2 ^ m)) hk_pow_N
  have hkQ1 : k ∈ twoCoreIn K1 :=
    sec10T_two_elem_Q1 hp.facts.pockets5 hp.facts.centZ5 hpsp hctx hk ⟨m, hk_pow_one⟩
  have hkQ : k ∈ secQ K1 K2 := by
    rw [sec11_Q_eq_sup hp hctx]
    exact Subgroup.mem_sup_left hkQ1
  have hnQ : n ∈ secQ K1 K2 := by
    have hn_eq : k⁻¹ * y = n := by rw [← hkny]; group
    rw [← hn_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkQ) hy
  have hn1 : n = 1 := sec11_Q_inf_oddCore hnQ hn
  rw [← hkny, hn1, mul_one]
  exact hkQ1

theorem sec11_Q_inf_K2N [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {y : G} (hy : y ∈ secQ K1 K2)
    (hyX : y ∈ K2 ⊔ oddCoreIn (secK0 t z)) : y ∈ twoCoreIn K2 := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hp.r10.lK0 hctx
  have hK2norm : K2 ≤ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    (le_sup_right.trans hKle).trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K2
    (oddCoreIn (secK0 t z)) hK2norm] at hyX
  obtain ⟨k, hk, n, hn, hkny⟩ := Set.mem_mul.mp hyX
  obtain ⟨m, hm⟩ := (sec11_Q_isPGroup K1 K2).exists_orderOf_eq_pow (⟨y, hy⟩ : secQ K1 K2)
  have hy1 : y ^ (2 ^ m) = 1 := by
    rw [← hm, ← Subgroup.orderOf_coe (⟨y, hy⟩ : secQ K1 K2)]
    exact pow_orderOf_eq_one y
  have hyK0 : y ∈ secK0 t z := hKle (sec11_Q_le_sup K1 K2 hy)
  have hynorm : y ∈ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hyK0
  obtain ⟨m', hm'N, hpow⟩ := sec11_pow_mul_normalizer (N := oddCoreIn (secK0 t z))
    hynorm (Subgroup.inv_mem _ hn) (2 ^ m)
  have hk_eq : y * n⁻¹ = k := by rw [← hkny]; group
  have hpow' : k ^ (2 ^ m) = m' := by rw [← hk_eq, hpow, hy1, one_mul]
  have hk_pow_N : k ^ (2 ^ m) ∈ oddCoreIn (secK0 t z) := by rw [hpow']; exact hm'N
  have hk_pow_one : k ^ (2 ^ m) = 1 :=
    sec11_K2_inf_N hp hctx (K2.pow_mem hk (2 ^ m)) hk_pow_N
  have hkQ2 : k ∈ twoCoreIn K2 :=
    sec10T_two_elem_Q1 hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.swap hk ⟨m, hk_pow_one⟩
  have hkQ : k ∈ secQ K1 K2 := by
    rw [sec11_Q_eq_sup hp hctx]
    exact Subgroup.mem_sup_right hkQ2
  have hnQ : n ∈ secQ K1 K2 := by
    have hn_eq : k⁻¹ * y = n := by rw [← hkny]; group
    rw [← hn_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkQ) hy
  have hn1 : n = 1 := sec11_Q_inf_oddCore hnQ hn
  rw [← hkny, hn1, mul_one]
  exact hkQ2

theorem sec11_x_normQ1 [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) {x : G} (hxT : x ∈ T)
    (hx : IsOuterOn x (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))) :
    ∀ q ∈ twoCoreIn K1, x * q * x⁻¹ ∈ twoCoreIn K1 := by
  intro q hq
  have hqQ : q ∈ secQ K1 K2 := by
    rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]
    exact Subgroup.mem_sup_left hq
  have hxqQ : x * q * x⁻¹ ∈ secQ K1 K2 := sec11_T_normQ hctx x hxT q hqQ
  have hq_sup : q ∈ K1 ⊔ oddCoreIn (secK0 t z) :=
    Subgroup.mem_sup_left (twoCoreIn_le_self K1 hq)
  have hxq_sup : x * q * x⁻¹ ∈ K1 ⊔ oddCoreIn (secK0 t z) :=
    (Subgroup.mem_normalizer_iff.mp hx.1 q).mp hq_sup
  exact sec11_Q_inf_K1N hp hctx.toSec10Ctx hxqQ hxq_sup

theorem sec11_x_normQ2 [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) {x : G} (hxT : x ∈ T)
    (hx : IsOuterOn x (K2 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))) :
    ∀ q ∈ twoCoreIn K2, x * q * x⁻¹ ∈ twoCoreIn K2 := by
  intro q hq
  have hqQ : q ∈ secQ K1 K2 := by
    rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]
    exact Subgroup.mem_sup_right hq
  have hxqQ : x * q * x⁻¹ ∈ secQ K1 K2 := sec11_T_normQ hctx x hxT q hqQ
  have hq_sup : q ∈ K2 ⊔ oddCoreIn (secK0 t z) :=
    Subgroup.mem_sup_left (twoCoreIn_le_self K2 hq)
  have hxq_sup : x * q * x⁻¹ ∈ K2 ⊔ oddCoreIn (secK0 t z) :=
    (Subgroup.mem_normalizer_iff.mp hx.1 q).mp hq_sup
  exact sec11_Q_inf_K2N hp hctx.toSec10Ctx hxqQ hxq_sup

end CFSG.OddStandard.SmallF3.Omega
