module

public import CFSG.GH74.Uniqueness.Bender.Models
import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SzComm
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitaryCoord

public section

namespace CFSG.GH74.Uniqueness.Bender

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.AschbacherToolkit.Bender (UnitaryCoord.mul_comm_iff
  UnitaryCoord.hermitianTorusAction_fst_eq)

variable {K : Type} [Group K] [Finite K]

theorem BenderType.exists_conj_not_commute_of_sq_ne {n i e : ℕ}
    (h : BenderType K n i e) (S : Sylow 2 K) {s s' : K} (hs : s ∈ (S : Subgroup K))
    (hs' : s' ∈ (S : Subgroup K)) (hs4 : orderOf s = 4) (hs'4 : orderOf s' = 4)
    (hne : s ^ 2 ≠ s' ^ 2) :
    ∃ c ∈ Subgroup.centralizer ({s ^ 2} : Set K), ¬ Commute (c * s * c⁻¹) s' := by
  obtain ⟨t, hc⟩ := h.exists_benderCore S
  have hnotZ : ∀ {x : K}, orderOf x = 4 → x ∉ rootCenter (S : Subgroup K) := by
    intro x hx hxZ
    have h2 := orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [pow_two]; exact hc.center_sq x hxZ)
    rw [hx] at h2
    norm_num at h2
  cases h with
  | linear n hn e₁ =>
    exfalso
    have hSZ : rootCenter (S : Subgroup K) = (S : Subgroup K) :=
      Subgroup.eq_of_le_of_card_ge (rootCenter_le _) (by rw [hc.card_center, hc.card_eq, pow_one])
    exact hnotZ hs4 (by rw [hSZ]; exact hs)
  | suzuki a ha e₁ =>
    refine ⟨1, Subgroup.one_mem _, fun hcomm => hne ?_⟩
    have hss' : s * s' = s' * s := by simpa using hcomm.eq
    let e₂ : K ≃* CFSG.Open.Sz a :=
      e₁.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a))
    have hzZ : s⁻¹ * s' ∈ rootCenter (S : Subgroup K) :=
      CFSG.ComponentClassification.GMS78.inv_mul_mem_sylowCenter_of_commute_of_sz ha e₂ S hs hs'
        hss' (hnotZ hs4) (hnotZ hs'4)
    have hzs : Commute s (s⁻¹ * s') :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 s hs
    have hz2 : (s⁻¹ * s') ^ 2 = 1 := by rw [pow_two]; exact hc.center_sq _ hzZ
    calc s ^ 2 = s ^ 2 * (s⁻¹ * s') ^ 2 := by rw [hz2, mul_one]
      _ = (s * (s⁻¹ * s')) ^ 2 := (hzs.mul_pow 2).symm
      _ = s' ^ 2 := by rw [mul_inv_cancel_left]
  | unitary n hn e₁ =>
    obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
    have : Fintype E := Fintype.ofFinite E
    have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul])
    obtain ⟨⟨ε, hεR, -⟩, -⟩ :=
      CFSG.ProperTwoGeneratedCore.RootCenter.even_unitary_root_center_automorphisms_of_mulEquiv
        J n hn hcard hfixed hJ (e₁.trans e') S (rootCenter (S : Subgroup K))
        hc.omega₁_map_eq_rootCenter.symm
    set ψ := hermitianUnipotentPSU J hJ with hψ
    have hsR : s ∈ (unitaryCoverRoot J hJ).map ε.toMonoidHom := hεR ▸ hs
    have hs'R : s' ∈ (unitaryCoverRoot J hJ).map ε.toMonoidHom := hεR ▸ hs'
    obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hsR
    obtain ⟨_, ⟨z', rfl⟩, rfl⟩ := hs'R
    have hinj : ∀ {w w' : hermitianUnipotentCoord J},
        Commute (ε (ψ w)) (ε (ψ w')) → w' * w = w * w' := by
      intro w w' hww
      apply CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
      apply ε.injective
      simpa [map_mul] using hww.eq.symm
    have hfst : ∀ {w : hermitianUnipotentCoord J}, orderOf (ε (ψ w)) = 4 → w.1.1 ≠ 0 := by
      intro w hw hw0
      apply hnotZ hw
      refine Subgroup.mem_inf.mpr ⟨hεR ▸ ⟨ψ w, ⟨w, rfl⟩, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hεR] at hy
      obtain ⟨_, ⟨w', rfl⟩, rfl⟩ := hy
      have hc' : w * w' = w' * w := by
        rw [UnitaryCoord.mul_comm_iff, hw0, map_zero, mul_zero, zero_mul]
      change ε (ψ w') * ε (ψ w) = ε (ψ w) * ε (ψ w')
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc']
    have hz1 := hfst hs4
    have hz'1 := hfst hs'4
    by_cases hcomm : Commute (ε (ψ z)) (ε (ψ z'))
    ·
      have hrel := (UnitaryCoord.mul_comm_iff J z z').mp (hinj hcomm)
      obtain ⟨h₀, hh₀1, hh₀N⟩ :=
        unitaryCoverScalarImage_exists_norm_one_ne_one J (2 ^ n) hcard hfixed hJ
          (by
            have : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
            omega)
      obtain ⟨k, hk⟩ := h₀.2
      have hkN : (J.conj (k : E))⁻¹ * (k : E)⁻¹ = 1 := by
        rw [← unitaryCoverScalar_norm, hk]
        exact hh₀N
      set c := hermitianTorusPSU J hJ k
      have hconj : ∀ w, c * ψ w * c⁻¹ = ψ (hermitianTorusAction J k w) :=
        fun w => unitaryCoverTorus_conj_root J hJ k w
      have hfix : hermitianTorusAction J k (z * z) = z * z := by
        apply Subtype.ext
        apply Prod.ext
        · rw [hermitianTorusAction_fst]
          change (z.1.1 + z.1.1) * (k : E) * (J.conj (k : E))⁻¹ ^ 2 = z.1.1 + z.1.1
          rw [CharTwo.add_self_eq_zero, zero_mul, zero_mul]
        · rw [hermitianTorusAction_snd, mul_assoc, hkN, mul_one]
      refine ⟨ε c, Subgroup.mem_centralizer_singleton_iff.mpr ?_, fun hcc => ?_⟩
      · have h1 : c * ψ (z * z) * c⁻¹ = ψ (z * z) := by rw [hconj, hfix]
        have h2 : ε c * (ε (ψ z)) ^ 2 * (ε c)⁻¹ = (ε (ψ z)) ^ 2 := by
          rw [pow_two, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, h1]
        calc ε c * ε (ψ z) ^ 2 = ε c * ε (ψ z) ^ 2 * (ε c)⁻¹ * ε c := by group
          _ = ε (ψ z) ^ 2 * ε c := by rw [h2]
      ·
        have hcs : ε c * ε (ψ z) * (ε c)⁻¹ = ε (ψ (hermitianTorusAction J k z)) := by
          rw [← map_inv, ← map_mul, ← map_mul, hconj]
        have hcc' : Commute (ε (ψ (hermitianTorusAction J k z))) (ε (ψ z')) := by
          rw [← hcs]
          exact hcc
        have hrel' := (UnitaryCoord.mul_comm_iff J (hermitianTorusAction J k z) z').mp (hinj hcc')
        rw [UnitaryCoord.hermitianTorusAction_fst_eq, hk, map_mul] at hrel'
        have hz1c : J.conj z'.1.1 ≠ 0 := (map_ne_zero J.conj).mpr hz'1
        have hfixed₀ : J.conj (h₀.val : E) = h₀.val := by
          have hmul : (z.1.1 * J.conj z'.1.1) * (J.conj (h₀.val : E) - h₀.val) = 0 := by
            linear_combination hrel' - J.conj (h₀.val : E) * hrel
          rcases mul_eq_zero.mp hmul with h0 | h0
          · exact absurd h0 (mul_ne_zero hz1 hz1c)
          · exact sub_eq_zero.mp h0
        apply hh₀1
        have hsq : (h₀.val : E) * h₀.val = 1 := by rw [← hh₀N, hfixed₀]
        have h0 : ((h₀.val : E) - 1) * ((h₀.val : E) - 1) = 0 := by
          linear_combination hsq + (1 - (h₀.val : E)) * (CharTwo.two_eq_zero (R := E))
        exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
    · exact ⟨1, Subgroup.one_mem _, by simpa using hcomm⟩

end CFSG.GH74.Uniqueness.Bender
