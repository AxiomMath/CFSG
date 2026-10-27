module

public import CFSG.LocalAnalysis.ComponentInitial.FixedLayerNormalizes
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 (Zsub)

variable {G : Type} [Group G] [Finite G]

theorem exists_noncentral_commute_of_odd_center {K : Subgroup G} (hK : CFSG.IsQuasisimple K)
    (hZ : Odd (Nat.card (center K))) {v : G} (hv : v * v = 1)
    (hvK : v ∈ normalizer (K : Set G)) :
    ∃ k ∈ K, k ∉ Zsub K ∧ v * k = k * v := by
  obtain ⟨k, hk, hkZ, hz⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_noncentral_fixed_mod_center hK hv hvK
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  change k ∉ Zsub K at hkZ
  change k⁻¹ * (v⁻¹ * k * v) ∈ Zsub K at hz
  have hZK : Zsub K = K ⊓ centralizer (K : Set G) := CFSG.center_map_subtype_eq_inf_centralizer K
  obtain ⟨z, hzdef⟩ : ∃ z, z = k⁻¹ * (v⁻¹ * k * v) := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have hvz : v⁻¹ * z * v = z⁻¹ := by
    rw [hzdef, hvinv]
    have e1 : v * (k⁻¹ * (v * k * v)) * v = v * k⁻¹ * v * k * (v * v) := by group
    have e2 : (k⁻¹ * (v * k * v))⁻¹ = v⁻¹ * k⁻¹ * v⁻¹ * k := by group
    rw [e1, e2, hv, mul_one, hvinv]
  have hcardZ : Nat.card (Zsub K) = Nat.card (center K) := by
    rw [Zsub, Subgroup.card_map_of_injective K.subtype_injective]
  have hzodd : Odd (orderOf z) := by
    have hdvd : orderOf z ∣ Nat.card (Zsub K) := Subgroup.orderOf_dvd_natCard (Zsub K) hz
    rw [hcardZ] at hdvd
    exact Odd.of_dvd_nat hZ hdvd
  obtain ⟨m, hm⟩ := hzodd
  have hconj : ∀ n : ℕ, v⁻¹ * z ^ n * v = (z⁻¹) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih, ← hvz]
      group
  obtain ⟨w, hwdef⟩ : ∃ w, w = z ^ (m + 1) := ⟨_, rfl⟩
  have hw2 : w * w = z := by
    rw [hwdef, ← pow_add, show m + 1 + (m + 1) = orderOf z + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hwZ : w ∈ Zsub K := by
    rw [hwdef]
    exact (Zsub K).pow_mem hz _
  have hvw : v⁻¹ * w * v = w⁻¹ := by
    rw [hwdef, hconj, inv_pow]
  have hwK : w ∈ K := (Subgroup.mem_inf.mp (hZK ▸ hwZ)).1
  refine ⟨k * w, K.mul_mem hk hwK, ?_, ?_⟩
  · intro hkw
    exact hkZ (by simpa using (Zsub K).mul_mem hkw ((Zsub K).inv_mem hwZ))
  · have hfix : v⁻¹ * (k * w) * v = k * w := by
      have h1 : v⁻¹ * (k * w) * v = (v⁻¹ * k * v) * (v⁻¹ * w * v) := by group
      have h2 : v⁻¹ * k * v = k * z := by rw [hzdef]; group
      rw [h1, h2, hvw, ← hw2]
      group
    rw [hvinv] at hfix
    calc v * (k * w) = v * (k * w) * v * v := by
          rw [mul_assoc (v * (k * w)) v v, hv, mul_one]
      _ = k * w * v := by rw [hfix]

theorem le_of_normal_inf_of_noncentral_mem {K M : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hn : ((K ⊓ M).subgroupOf K).Normal) {k : G}
    (hk : k ∈ K) (hkZ : k ∉ Zsub K) (hkM : k ∈ M) : K ≤ M := by
  by_cases htop : (K ⊓ M).subgroupOf K = ⊤
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥K) ∈ (K ⊓ M).subgroupOf K := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
  · exfalso
    have hle := @CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top ↥K _
      hK ((K ⊓ M).subgroupOf K) hn htop
    apply hkZ
    have hmem : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ M).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hk, hkM⟩)
    exact ⟨⟨k, hk⟩, hle hmem, rfl⟩

end CFSG.GroupTheory
