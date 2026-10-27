module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuatSylow
public import CFSG.Milestones.LR_Brauer_Suzuki_central_involution
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem rankOne_sylow_dihedral {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hO : oddCore K = ⊥) (hev : Even (Nat.card K)) (hr : CFSG.pRank 2 K ≤ 1) :
    center K ≠ ⊥ ∧ ∃ n : ℕ, 2 ≤ n ∧ ∃ P : Sylow 2 (K ⧸ center K),
      Nonempty (↥(P : Subgroup (K ⧸ center K)) ≃* DihedralGroup (2 ^ (n - 1))) := by
  haveI h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hperf : Group.IsPerfect K := hK.1
  obtain ⟨T, r, hr3, ⟨eT⟩⟩ := exists_quaternion_sylow hperf hev hr
  let m : ℕ := 2 ^ (r - 2)
  have hm : 2 ≤ m := by
    have h1 : 1 ≤ r - 2 := by omega
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := pow_le_pow_right₀ (by norm_num) h1
  let c : QuaternionGroup m := QuaternionGroup.a (m : ZMod (2 * m))
  have hc_ord : orderOf c = 2 :=
    orderOf_eq_prime (CFSG.Semidihedral.QuaternionAutomorphismLifting.centralHalf_sq m)
      (CFSG.Semidihedral.QuaternionAutomorphismLifting.centralHalf_ne_one m (by omega))
  let t₀ : ↥(T : Subgroup K) := eT.symm c
  have ht₀_ord : orderOf t₀ = 2 := by
    have h := MulEquiv.orderOf_eq eT.symm c
    rw [hc_ord] at h
    exact h
  let t : K := (t₀ : K)
  have ht_ord : orderOf t = 2 := by
    change orderOf ((t₀ : ↥(T : Subgroup K)) : K) = 2
    rw [Subgroup.orderOf_coe]
    exact ht₀_ord
  have ht_mem : t ∈ (T : Subgroup K) := t₀.2
  have hbs := CFSG.Milestones.brauer_suzuki_central_involution r hr3 T ⟨eT⟩ t ht_mem ht_ord
  let eO : K ⧸ oddCore K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hesymm : eO.symm t = QuotientGroup.mk t := by
    change (QuotientGroup.quotientMulEquivOfEq hO).symm
      (QuotientGroup.quotientBot.symm t) = _
    rw [QuotientGroup.quotientBot_symm_apply]
    exact QuotientGroup.quotientMulEquivOfEq_mk hO.symm t
  have hq : eO (QuotientGroup.mk t) = t := by
    rw [← hesymm, eO.apply_symm_apply]
  have hmapped : eO (QuotientGroup.mk t) ∈ center K := by
    have hm : eO (QuotientGroup.mk t) ∈ (center (K ⧸ oddCore K)).map eO :=
      ⟨QuotientGroup.mk t, hbs.2, rfl⟩
    rwa [Subgroup.map_center_eq eO] at hm
  have hcenter_mem : t ∈ center K := by
    simpa only [hq] using hmapped
  have ht_ne_one : t ≠ 1 := by
    intro h
    apply hbs.1
    apply eO.injective
    rw [hq, h, map_one eO]
  have hcenter_ne_bot : center K ≠ ⊥ := by
    intro hbot
    have ht_bot : t ∈ (⊥ : Subgroup K) := by
      rw [hbot] at hcenter_mem
      exact hcenter_mem
    exact ht_ne_one (Subgroup.mem_bot.mp ht_bot)
  let ZK : Subgroup K := center K
  haveI hZK_normal : ZK.Normal := by
    change (center K).Normal
    infer_instance
  have hZK_pgroup : IsPGroup 2 ZK := by
    have hO2 : pPrimeCore 2 K = ⊥ := by
      rw [← oddCore_eq_pPrimeCore_two K]; exact hO
    exact CFSG.ComponentClassification.Sol78.center_isPGroup_two hO2
  have hZK_le_T : ZK ≤ (T : Subgroup K) := IsPGroup.le_sylow_of_normal hZK_pgroup T
  have ht₀_mem : t₀ ∈ ZK.subgroupOf (T : Subgroup K) := by
    rw [Subgroup.mem_subgroupOf]
    exact hcenter_mem
  have hmap : (ZK.subgroupOf (T : Subgroup K)).map eT = center (QuaternionGroup m) := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := eT.surjective q
      have hyx : y * x = x * y := by
        apply Subtype.ext
        show (y : K) * (x : K) = (x : K) * (y : K)
        rw [Subgroup.mem_subgroupOf] at hx
        exact Subgroup.mem_center_iff.mp hx (y : K)
      calc eT y * eT x = eT (y * x) := (eT.map_mul y x).symm
        _ = eT (x * y) := by rw [hyx]
        _ = eT x * eT y := eT.map_mul x y
    · intro q hq
      rw [Subgroup.mem_map]
      rw [CFSG.Semidihedral.QuaternionAutomorphismLifting.center_iff m hm] at hq
      rcases hq with rfl | rfl
      · exact ⟨1, one_mem _, map_one eT⟩
      · exact ⟨t₀, ht₀_mem, eT.apply_symm_apply c⟩
  let φ : ↥(T : Subgroup K) →* K ⧸ ZK :=
    (QuotientGroup.mk' ZK).comp (T : Subgroup K).subtype
  let P : Sylow 2 (K ⧸ center K) := T.mapSurjective (QuotientGroup.mk'_surjective ZK)
  have hker : φ.ker = ZK.subgroupOf (T : Subgroup K) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange : φ.range = (P : Subgroup (K ⧸ center K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  refine ⟨hcenter_ne_bot, r - 1, by omega, P, ?_⟩
  have hpow : 2 ^ ((r - 1) - 1) = m := by
    rw [show (r - 1) - 1 = r - 2 by omega]
  rw [hpow]
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        ((QuotientGroup.congr (ZK.subgroupOf (T : Subgroup K))
            (center (QuaternionGroup m)) eT hmap).trans
          (CFSG.Semidihedral.QuaternionAutomorphismLifting.centerQuotientEquivDihedral m hm))))⟩

end CFSG.OddStandard.SmallF3.HypA2
