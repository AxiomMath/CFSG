module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

theorem z_mem_J : d.z ∈ h.J := (mem_inf.mp d.z_D).2

theorem orderOf_zbar :
    orderOf (((⟨d.z, d.z_mem_J⟩ : ↥h.J) : ↥h.J ⧸ pPrimeCore 2 ↥h.J)) = 2 := by
  have hzS : d.z ∈ h.S := (mem_inf.mp d.z_D).1
  have hzN : d.z ∈ normalizer (h.J : Set H) := le_normalizer d.z_mem_J
  have hzP : d.z ∉ h.P := fun hP => by
    have h1 : d.z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨d.z_D, hP⟩
    rw [h.D_inf_P_eq_bot H₁.center_J, mem_bot] at h1
    have h2 := d.z_ord
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow]
    have : (⟨d.z, d.z_mem_J⟩ : ↥h.J) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← d.z_ord]
      exact pow_orderOf_eq_one _)
    rw [this, QuotientGroup.mk_one]
  · intro h1
    apply hzP
    refine mem_inf.mpr ⟨hzS, (rhoE_eq_one_iff hzN).mp ?_⟩
    rw [rhoE_of_mem_J d.z_mem_J, h1, map_one]

theorem S_le_W : h.S ≤ centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) := by
  intro s hs
  have hsa : s ∈ centralizer ({h.a} : Set H) := (mem_inf.mp (h.S_le hs)).1
  refine mem_inf.mpr ⟨hsa, mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := mem_centralizer_singleton_iff.mp hsa
  have h2 : s * d.z = d.z * s := mem_centralizer_iff.mp d.z_S s hs
  rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

theorem comm_z_of_mem_W {x : H}
    (hx : x ∈ centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) :
    x * d.z = d.z * x := by
  have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).1
  have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
  have h1' : x * h.a⁻¹ = h.a⁻¹ * x := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, inv_mul_cancel_left]
  calc x * d.z = (x * h.a⁻¹) * (h.a * d.z) := by group
    _ = h.a⁻¹ * (x * (h.a * d.z)) := by rw [h1']; group
    _ = h.a⁻¹ * (h.a * d.z * x) := by rw [h2]
    _ = d.z * x := by group

theorem exists_oddCore_Y9 {v : H} (hst : d.Stage7 v) :
    ∃ N : Subgroup H, N ≤ oddCoreIn (centralizer ({h.a} : Set H)) ∧
      centralizer ({h.a} : Set H) ≤ normalizer (N : Set H) ∧
      ∀ y ∈ Y9 h, Odd (orderOf y) → y ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN⟩ := (CFSG.GroupTheory.hasNormalPComplement_iff_exists 2).mp
    (d.hasNormalPComplement_kernel hst)
  have hchar := CFSG.GroupTheory.FrobeniusNormalComplement.IsNormalPComplement.characteristic hN
  obtain ⟨hNn, hNc, k, hk⟩ := hN
  have hJN := H₁.centralizer_le_normalizer_J
  have hYN : centralizer ({h.a} : Set H) ≤ normalizer ((Y9 h : Subgroup H) : Set H) :=
    fun g hg => mem_normalizer_inf (le_normalizer hg)
      (Eight2.mem_normalizer_of_conj_mem_fin fun x hx =>
        UnbalancedLayer.conj_mem_coreActionKernel (hJN hg) hx)
  have hNN : centralizer ({h.a} : Set H) ≤
      normalizer ((N.map (Y9 h).subtype : Subgroup H) : Set H) := fun g hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (Y9 h) N (hYN hg)
  refine ⟨N.map (Y9 h).subtype, ?_, hNN, ?_⟩
  · have hNC : N.map (Y9 h).subtype ≤ centralizer ({h.a} : Set H) :=
      (map_subtype_le N).trans inf_le_left
    have hnorm : ((N.map (Y9 h).subtype).subgroupOf (centralizer ({h.a} : Set H))).Normal :=
      (normal_subgroupOf_iff hNC).mpr fun x g hx hg => (mem_normalizer_iff.mp (hNN hg) x).mp hx
    have hcard : Nat.card ((N.map (Y9 h).subtype).subgroupOf (centralizer ({h.a} : Set H))) =
        Nat.card N := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv,
        card_map_of_injective (Y9 h).subtype_injective]
    have hle : (N.map (Y9 h).subtype).subgroupOf (centralizer ({h.a} : Set H)) ≤
        pPrimeCore 2 ↥(centralizer ({h.a} : Set H)) :=
      le_sSup ⟨hnorm, by rw [hcard]; exact hNc.symm⟩
    intro x hx
    exact ⟨⟨x, hNC hx⟩, hle (show (⟨x, hNC hx⟩ : ↥(centralizer ({h.a} : Set H))) ∈
      (N.map (Y9 h).subtype).subgroupOf _ from hx), rfl⟩
  ·
    intro y hy ho
    have hq : IsPGroup 2 (↥(Y9 h) ⧸ N) := IsPGroup.of_card (n := k) (by
      rw [← hk, Subgroup.index])
    obtain ⟨j, hj⟩ := hq (QuotientGroup.mk ⟨y, hy⟩)
    have h1 : orderOf (QuotientGroup.mk (s := N) (⟨y, hy⟩ : ↥(Y9 h))) ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf (QuotientGroup.mk (s := N) (⟨y, hy⟩ : ↥(Y9 h))) ∣ orderOf y := by
      rw [← Subgroup.orderOf_mk y hy]
      exact orderOf_map_dvd (QuotientGroup.mk' N) _
    have h3 : orderOf (QuotientGroup.mk (s := N) (⟨y, hy⟩ : ↥(Y9 h))) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr ho)))
        h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact ⟨⟨y, hy⟩, h3, rfl⟩

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
