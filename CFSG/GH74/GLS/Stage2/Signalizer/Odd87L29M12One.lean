module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Finite.Perm

public section

open Subgroup
open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem m12_card_eq_192 {Y : Type} [Group Y] [Finite Y] {W : Subgroup Y} [W.Normal]
    (hWc : Nat.card ↥W = 32) (hquot : Nonempty ((Y ⧸ W) ≃* Equiv.Perm (Fin 3))) :
    Nat.card Y = 192 := by
  obtain ⟨φ⟩ := hquot
  have h1 : Nat.card (Y ⧸ W) = 6 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  rw [W.card_eq_card_quotient_mul_card_subgroup, h1, hWc]

theorem m12_exists_conj_card_three {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 192)
    {A B : Subgroup Y} (hA : Nat.card ↥A = 3) (hB : Nat.card ↥B = 3) :
    ∃ g : Y, ∀ a ∈ A, g * a * g⁻¹ ∈ B := by
  have hsyl : ∀ H : Subgroup Y, Nat.card ↥H = 3 → ∃ P : Sylow 3 Y, (P : Subgroup Y) = H := by
    intro H hH
    refine ⟨(IsPGroup.of_card (n := 1) (by simpa using hH)).toSylow ?_, rfl⟩
    have h := H.card_mul_index
    rw [hH, hY] at h
    have : H.index = 64 := by omega
    rw [this]
    decide
  obtain ⟨P, hP⟩ := hsyl A hA
  obtain ⟨Q, hQ⟩ := hsyl B hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P Q
  refine ⟨g, fun a ha => ?_⟩
  have h1 : MulAut.conj g • a ∈ MulAut.conj g • (P : Subgroup Y) :=
    Subgroup.smul_mem_pointwise_smul a _ _ (hP ▸ ha)
  rw [← Sylow.coe_subgroup_smul, hg, hQ] at h1
  simpa [MulAut.smul_def] using h1

theorem m12_perm3_not_commute :
    ∀ τ α : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → α * α * α = 1 → α ≠ 1 → τ * α ≠ α * τ := by
  decide

theorem m12_no_order_three {Y : Type} [Group Y] [Finite Y] {zb : Y}
    (hzb : ∀ y : Y, y * zb = zb * y) {W A : Subgroup Y} [W.Normal]
    (hW2 : IsPGroup 2 ↥W) (hWc : Nat.card ↥W = 32) (hA : Nat.card ↥A = 3)
    (hquot : Nonempty ((Y ⧸ W) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ w ∈ W, (∀ a ∈ A, a * w = w * a) → w ∈ zpowers zb)
    {v : Y} (hv2 : v * v = 1) (hv1 : v ∉ zpowers zb) {c : Y}
    (hc : c ∈ centralizer ({v} : Set Y)) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) : False := by
  have hY := m12_card_eq_192 hWc hquot
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcW : c ∉ W := by
    intro hcW
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hW2 ⟨c, hcW⟩
    rw [Subgroup.orderOf_mk, hord] at hk
    rcases k with _ | k
    · omega
    · rw [pow_succ] at hk
      omega
  have hcv : c * v = v * c := mem_centralizer_singleton_iff.1 hc
  by_cases hvW : v ∈ W
  · obtain ⟨g, hg⟩ := m12_exists_conj_card_three hY hA (B := zpowers c)
      (by rw [Nat.card_zpowers, hord])
    have hle : zpowers c ≤ centralizer ({v} : Set Y) := zpowers_le.2 hc
    have hw : g⁻¹ * v * g ∈ zpowers zb := by
      refine hfix _ ?_ ?_
      · simpa using (inferInstance : W.Normal).conj_mem v hvW g⁻¹
      · intro a ha
        have h1 : g * a * g⁻¹ * v = v * (g * a * g⁻¹) :=
          mem_centralizer_singleton_iff.1 (hle (hg a ha))
        calc a * (g⁻¹ * v * g) = g⁻¹ * (g * a * g⁻¹ * v) * g := by group
          _ = g⁻¹ * (v * (g * a * g⁻¹)) * g := by rw [h1]
          _ = g⁻¹ * v * g * a := by group
    obtain ⟨n, hn⟩ := hw
    apply hv1
    have hcomm : g * zb ^ n = zb ^ n * g :=
      Commute.zpow_right (show Commute g zb from hzb g) n
    have hv : v = zb ^ n := by
      calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
        _ = g * zb ^ n * g⁻¹ := by rw [← hn]
        _ = zb ^ n := mul_inv_eq_iff_eq_mul.2 hcomm
    exact ⟨n, hv.symm⟩
  · obtain ⟨φ⟩ := hquot
    have hc3' : c * c * c = 1 := by simpa [pow_succ] using hc3
    refine m12_perm3_not_commute (φ (QuotientGroup.mk v)) (φ (QuotientGroup.mk c)) ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, ← QuotientGroup.mk_mul, hv2, QuotientGroup.mk_one, map_one]
    · intro h
      apply hvW
      rw [map_eq_one_iff φ φ.injective] at h
      exact (QuotientGroup.eq_one_iff v).1 h
    · rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc3',
        QuotientGroup.mk_one, map_one]
    · intro h
      apply hcW
      rw [map_eq_one_iff φ φ.injective] at h
      exact (QuotientGroup.eq_one_iff c).1 h
    · rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcv.symm]

theorem m12_centralizer_isPGroup {Y : Type} [Group Y] [Finite Y] {zb : Y}
    (hzb : ∀ y : Y, y * zb = zb * y) {W A : Subgroup Y} [W.Normal]
    (hW2 : IsPGroup 2 ↥W) (hWc : Nat.card ↥W = 32) (hA : Nat.card ↥A = 3)
    (hquot : Nonempty ((Y ⧸ W) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ w ∈ W, (∀ a ∈ A, a * w = w * a) → w ∈ zpowers zb)
    {v : Y} (hv2 : v * v = 1) (hv1 : v ∉ zpowers zb) :
    IsPGroup 2 ↥(centralizer ({v} : Set Y)) := by
  have hY := m12_card_eq_192 hWc hquot
  rw [IsPGroup.iff_card]
  have hdvd : Nat.card (centralizer ({v} : Set Y)) ∣ 2 ^ 6 * 3 := by
    have := Subgroup.card_subgroup_dvd_card (centralizer ({v} : Set Y))
    rwa [hY] at this
  have h3 : ¬ 3 ∣ Nat.card (centralizer ({v} : Set Y)) := by
    intro h3
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine m12_no_order_three hzb hW2 hWc hA hquot hfix hv2 hv1 c.2 ?_ ?_
    · have := pow_orderOf_eq_one c
      rw [hc] at this
      simpa using congrArg Subtype.val this
    · intro h1
      have : c = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hc
      omega
  have hcop : Nat.Coprime (Nat.card (centralizer ({v} : Set Y))) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hcop.dvd_of_dvd_mul_right hdvd)
  exact ⟨k, hk⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
