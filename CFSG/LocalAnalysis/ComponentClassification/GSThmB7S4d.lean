module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4c

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

namespace Setting

variable (s : Setting X)

structure Swap (u z : X) : Prop where
  hu : u ∈ normalizer (s.h.S : Set X)
  hua : u⁻¹ * s.h.a * u = z
  huz : u⁻¹ * z * u = s.h.a
  huu : u * u ∈ s.h.S

theorem conj_mem_center {u : X} (hu : u ∈ normalizer (s.h.S : Set X)) {w : X} (hwS : w ∈ s.h.S)
    (hwZ : ∀ t ∈ s.h.S, t * w = w * t) :
    u⁻¹ * w * u ∈ s.h.S ∧ ∀ t ∈ s.h.S, t * (u⁻¹ * w * u) = (u⁻¹ * w * u) * t := by
  have hu' : u⁻¹ ∈ normalizer (s.h.S : Set X) := inv_mem hu
  refine ⟨?_, fun t ht => ?_⟩
  · have := (mem_normalizer_iff.mp hu' w).mp hwS
    rwa [inv_inv] at this
  · have htu : u * t * u⁻¹ ∈ s.h.S := (mem_normalizer_iff.mp hu t).mp ht
    have h1 := hwZ _ htu
    calc t * (u⁻¹ * w * u) = u⁻¹ * ((u * t * u⁻¹) * w) * u := by group
      _ = u⁻¹ * (w * (u * t * u⁻¹)) * u := by rw [h1]
      _ = u⁻¹ * w * u * t := by group

theorem exists_u (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) (hC : CFL2C)
    (hNS : ¬ normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) :
    ∃ u : X, s.Swap u (s.toData hConj hComp hOut hCent).z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨u₀, hu₀N, hu₀a⟩ := Set.not_subset.mp hNS
  have hu₀a' : u₀⁻¹ * s.h.a * u₀ ≠ s.h.a := by
    intro h1
    apply hu₀a
    show u₀ ∈ centralizer ({s.h.a} : Set X)
    rw [mem_centralizer_singleton_iff]
    calc u₀ * s.h.a = u₀ * (u₀⁻¹ * s.h.a * u₀) := by rw [h1]
      _ = s.h.a * u₀ := by group
  have hzZ : ∀ t ∈ s.h.S, t * d.z = d.z * t := d.hzS
  have haZ : ∀ t ∈ s.h.S, t * s.h.a = s.h.a * t := fun t ht => s.h.comm_a ht
  have hza : d.z ≠ s.h.a := by
    intro h1
    have := d.hDP ▸ mem_inf.mpr ⟨h1 ▸ d.hzD, s.h.a_mem_P⟩
    exact d.a_ne_one (mem_bot.mp this)
  obtain ⟨hwS, hwZ⟩ := s.conj_mem_center hu₀N s.h.a_mem_S haZ
  have hw : u₀⁻¹ * s.h.a * u₀ = d.z := by
    rcases s.center_cases hConj hComp hOut hCent hwS hwZ with h1 | h1 | h1 | h1
    · exfalso
      apply d.a_ne_one
      calc s.h.a = u₀ * (u₀⁻¹ * s.h.a * u₀) * u₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact absurd h1 hu₀a'
    · exact h1
    · exact absurd h1 (s.not_conj_a_az hConj hComp hOut hCent hD hA hC u₀)
  obtain ⟨hw'S, hw'Z⟩ := s.conj_mem_center hu₀N d.z_mem_S hzZ
  have hw' : u₀⁻¹ * d.z * u₀ = s.h.a := by
    rcases s.center_cases hConj hComp hOut hCent hw'S hw'Z with h1 | h1 | h1 | h1
    · exfalso
      apply d.z_ne_one
      calc d.z = u₀ * (u₀⁻¹ * d.z * u₀) * u₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact h1
    · exfalso
      apply hza
      calc d.z = u₀⁻¹ * s.h.a * u₀ := hw.symm
        _ = s.h.a := by
          have : u₀⁻¹ * s.h.a * u₀ = u₀⁻¹ * d.z * u₀ := by rw [hw, h1]
          have h2 : s.h.a = d.z := by
            have := congrArg (fun v => u₀ * v * u₀⁻¹) this
            simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
            exact this
          rw [hw, ← h2]
    · exfalso
      have haz : (u₀⁻¹)⁻¹ * s.h.a * u₀⁻¹ = s.h.a * d.z := by
        have h2 : u₀⁻¹ * (s.h.a * d.z) * u₀ = s.h.a := by
          rw [show u₀⁻¹ * (s.h.a * d.z) * u₀ = (u₀⁻¹ * s.h.a * u₀) * (u₀⁻¹ * d.z * u₀) by group,
            hw, h1, ← mul_assoc, ← hzZ _ s.h.a_mem_S, mul_assoc, d.z_mul_z, mul_one]
        calc (u₀⁻¹)⁻¹ * s.h.a * u₀⁻¹ = u₀ * (u₀⁻¹ * (s.h.a * d.z) * u₀) * u₀⁻¹ := by
              rw [h2, inv_inv]
          _ = s.h.a * d.z := by group
      exact s.not_conj_a_az hConj hComp hOut hCent hD hA hC u₀⁻¹ haz
  set N₀ := normalizer (s.h.S : Set X) ⊓ centralizer ({s.h.a} : Set X) with hN₀
  have hSN₀ : s.h.S ≤ N₀ := le_inf le_normalizer s.hSa.1
  have hN₀C : N₀ ≤ centralizer ({s.h.a} : Set X) := inf_le_right
  have hu₂ : u₀ * u₀ ∈ N₀ := by
    refine mem_inf.mpr ⟨mul_mem hu₀N hu₀N, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : (u₀ * u₀)⁻¹ * s.h.a * (u₀ * u₀) = s.h.a := by
      rw [show (u₀ * u₀)⁻¹ * s.h.a * (u₀ * u₀) = u₀⁻¹ * (u₀⁻¹ * s.h.a * u₀) * u₀ by group, hw, hw']
    calc u₀ * u₀ * s.h.a = u₀ * u₀ * ((u₀ * u₀)⁻¹ * s.h.a * (u₀ * u₀)) := by rw [h1]
      _ = s.h.a * (u₀ * u₀) := by group
  have hodd : ¬ 2 ∣ s.h.S.relIndex N₀ := by
    obtain ⟨-, R, hR⟩ := s.hSa
    have h1 : ¬ 2 ∣ (s.h.S.subgroupOf (centralizer ({s.h.a} : Set X))).index := by
      rw [← hR]; exact R.not_dvd_index
    have h2 := Subgroup.relIndex_mul_relIndex s.h.S N₀ (centralizer ({s.h.a} : Set X)) hSN₀ hN₀C
    intro h3
    apply h1
    change 2 ∣ s.h.S.relIndex (centralizer ({s.h.a} : Set X))
    rw [← h2]
    exact Dvd.dvd.mul_right h3 _
  set m := s.h.S.relIndex N₀ with hm
  have hmS : (u₀ * u₀) ^ m ∈ s.h.S := by
    have : (s.h.S.subgroupOf N₀).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hSN₀).mpr inf_le_left
    have h1 : (QuotientGroup.mk' (s.h.S.subgroupOf N₀) ⟨u₀ * u₀, hu₂⟩) ^ m = 1 := by
      rw [hm, Subgroup.relIndex, Subgroup.index]
      exact pow_card_eq_one'
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1
  obtain ⟨k, hk⟩ : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hu₂z : u₀ * u₀ ∈ centralizer ({d.z} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (u₀ * u₀)⁻¹ * d.z * (u₀ * u₀) = d.z := by
      rw [show (u₀ * u₀)⁻¹ * d.z * (u₀ * u₀) = u₀⁻¹ * (u₀⁻¹ * d.z * u₀) * u₀ by group, hw', hw]
    calc u₀ * u₀ * d.z = u₀ * u₀ * ((u₀ * u₀)⁻¹ * d.z * (u₀ * u₀)) := by rw [h1]
      _ = d.z * (u₀ * u₀) := by group
  set v := (u₀ * u₀) ^ k with hv
  have hva : v ∈ centralizer ({s.h.a} : Set X) := pow_mem (hN₀C hu₂) k
  have hvz : v ∈ centralizer ({d.z} : Set X) := pow_mem hu₂z k
  rw [mem_centralizer_singleton_iff] at hva hvz
  have hcv : v * u₀ = u₀ * v := by
    have hcomm : Commute u₀ (u₀ * u₀) := (Commute.refl u₀).mul_right (Commute.refl u₀)
    exact ((hcomm.pow_right k).eq).symm
  refine ⟨u₀ * v, mul_mem hu₀N (pow_mem (mul_mem hu₀N hu₀N) k), ?_, ?_, ?_⟩
  · calc (u₀ * v)⁻¹ * s.h.a * (u₀ * v) = v⁻¹ * (u₀⁻¹ * s.h.a * u₀) * v := by group
      _ = d.z := by rw [hw, mul_assoc, ← hvz, inv_mul_cancel_left]
  · calc (u₀ * v)⁻¹ * d.z * (u₀ * v) = v⁻¹ * (u₀⁻¹ * d.z * u₀) * v := by group
      _ = s.h.a := by rw [hw', mul_assoc, ← hva, inv_mul_cancel_left]
  · have huu : u₀ * v * (u₀ * v) = (u₀ * u₀) ^ m := by
      calc u₀ * v * (u₀ * v) = u₀ * (v * u₀) * v := by group
        _ = u₀ * (u₀ * v) * v := by rw [hcv]
        _ = (u₀ * u₀) * (v * v) := by group
        _ = (u₀ * u₀) ^ (k + k + 1) := by rw [hv, ← pow_add, ← pow_succ']
        _ = (u₀ * u₀) ^ m := by rw [hk]; ring_nf
    rw [huu]
    exact hmS

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB
