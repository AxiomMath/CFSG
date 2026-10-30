module

public import CFSG.GF2Type.CenterFour.Basic

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem orderOf_conj_eq' (x g : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulEquiv.injective _) x
  simpa [MulAut.conj_apply] using h

private theorem ne_one_of_config (hC : Config z n) : z ≠ 1 := by
  intro h
  have h2 := hC.orderOf_eq
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem eq_or_sq_of_mem_center (hC : Config z n) {y : G} (hy : y ∈ centerAt z)
    (hy1 : y ≠ 1) : y = z ∨ y ^ 2 = z := by
  obtain ⟨k, hZk, hk4, hk2⟩ := hC.exists_generator
  rw [hZk] at hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hred : k ^ (j % 4) = k ^ j := by
    have := zpow_mod_orderOf k j
    rwa [hk4, Nat.cast_ofNat] at this
  have h0 : 0 ≤ j % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : j % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = j % 4 := ⟨_, rfl⟩
  rw [← hr] at hred h0 h4
  have h4' : k ^ 4 = 1 := by rw [← hk4]; exact pow_orderOf_eq_one k
  interval_cases r
  · exact absurd (by rw [← hred, zpow_zero] : k ^ j = 1) hy1
  · right
    rw [← hred, zpow_one, hk2]
  · left
    rw [← hred]
    simpa using hk2
  · right
    rw [← hred, zpow_ofNat, ← pow_mul, show 3 * 2 = 2 + 4 from rfl, pow_add, h4', mul_one, hk2]

theorem Config.eq_of_inf_conj_ne_bot (hC : Config z n) (g : G)
    (h : centerAt z ⊓ CFSG.conjugate (centerAt z) g ≠ ⊥) : g⁻¹ * z * g = z := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
  obtain ⟨hyZ, hyW⟩ := Subgroup.mem_inf.mp hy
  have hzW : z ∈ CFSG.conjugate (centerAt z) g := by
    rcases eq_or_sq_of_mem_center hC hyZ hy1' with hyz | hsq
    · rw [hyz] at hyW
      exact hyW
    · have h2 : y ^ 2 ∈ CFSG.conjugate (centerAt z) g := pow_mem hyW 2
      rwa [hsq] at h2
  rw [mem_conjugate_iff'] at hzW
  have hx : orderOf (g * z * g⁻¹) = 2 := by
    have h3 := orderOf_conj_eq' z g⁻¹
    rw [inv_inv] at h3
    rw [h3, hC.orderOf_eq]
  have hxz : g * z * g⁻¹ = z := hC.eq_of_mem_center hzW hx
  calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hxz]
    _ = z := by group

theorem Config.exists_conj_eq_mul (hC : Config z n) {a : G} (ha : a ∈ coreAt z) (ha2 : a ^ 2 = 1)
    (haZ : a ∉ centerAt z) : ∃ q ∈ coreAt z, q⁻¹ * a * q = a * z := by
  have hnc : ∃ x ∈ coreAt z, a * x ≠ x * a := by
    by_contra hcon
    push Not at hcon
    apply haZ
    have hmem : (⟨a, ha⟩ : coreAt z) ∈ center (coreAt z) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨x, hx⟩
      exact Subtype.ext (hcon x hx).symm
    show a ∈ (center (coreAt z)).map (coreAt z).subtype
    exact Subgroup.mem_map_of_mem _ hmem
  obtain ⟨x, hx, hax⟩ := hnc
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have ainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hnot1 : ⁅a, x⁆ ≠ 1 := by
    intro h1
    rw [commutatorElement_def] at h1
    apply hax
    calc a * x = a * x * a⁻¹ * x⁻¹ * x * a := by group
      _ = x * a := by rw [h1]; group
  have hcomm : ⁅a, x⁆ = z := (hC.comm_eq a ha x hx).resolve_left hnot1
  rw [commutatorElement_def, ainv] at hcomm
  refine ⟨x⁻¹, inv_mem hx, ?_⟩
  calc (x⁻¹)⁻¹ * a * x⁻¹ = (a * a) * (x * a * x⁻¹) := by rw [haa]; group
    _ = a * (a * x * a * x⁻¹) := by group
    _ = a * z := by rw [hcomm]

theorem Config.exists_conj_eq_mul_z (hC : Config z n) {g : G}
    (hu : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) (hne : g⁻¹ * z * g ≠ z) :
    ∃ g' : G, g'⁻¹ * z * g' = g⁻¹ * z * g * z := by
  obtain ⟨k, hZk, hk4, hk2⟩ := hC.exists_generator
  have hkZ : k ∈ centerAt z := by
    rw [hZk]
    exact Subgroup.mem_zpowers k
  have huz : g⁻¹ * z * g * z = z * (g⁻¹ * z * g) :=
    Subgroup.mem_centralizer_singleton_iff.1 hu
  have hz2 : z ^ 2 = 1 := by
    rw [← hC.orderOf_eq]
    exact pow_orderOf_eq_one z
  have hz2' : z * z = 1 := by
    rw [← sq]
    exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2'
  by_cases hA : g⁻¹ * z * g ∈ centralizer (centerAt z : Set G)
  · have huQ : g⁻¹ * z * g ∈ coreAt z := hC.mem_core_of_centralizes g hA
    have hu2 : (g⁻¹ * z * g) ^ 2 = 1 := by
      calc (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by simp only [sq]; group
        _ = 1 := by rw [hz2]; group
    have huZ : g⁻¹ * z * g ∉ centerAt z := by
      intro hmem
      apply hne
      exact hC.eq_of_mem_center hmem (by rw [orderOf_conj_eq', hC.orderOf_eq])
    obtain ⟨q, hq, hq'⟩ := hC.exists_conj_eq_mul huQ hu2 huZ
    refine ⟨g * q, ?_⟩
    calc (g * q)⁻¹ * z * (g * q) = q⁻¹ * (g⁻¹ * z * g) * q := by group
      _ = g⁻¹ * z * g * z := hq'
  · have hu_k' : g⁻¹ * z * g * k * (g⁻¹ * z * g)⁻¹ = k⁻¹ :=
      hC.inv_of_not_mem_centralizer hu hA hkZ
    have hu_k : g⁻¹ * z * g * k = k⁻¹ * (g⁻¹ * z * g) := by
      calc g⁻¹ * z * g * k
          = (g⁻¹ * z * g * k * (g⁻¹ * z * g)⁻¹) * (g⁻¹ * z * g) := by group
        _ = k⁻¹ * (g⁻¹ * z * g) := by rw [hu_k']
    have hkinv2 : k⁻¹ * k⁻¹ = z := by
      calc k⁻¹ * k⁻¹ = (k * k)⁻¹ := by group
        _ = (k ^ 2)⁻¹ := by rw [sq]
        _ = z⁻¹ := by rw [hk2]
        _ = z := hzinv
    refine ⟨g * k, ?_⟩
    calc (g * k)⁻¹ * z * (g * k) = k⁻¹ * (g⁻¹ * z * g * k) := by group
      _ = k⁻¹ * (k⁻¹ * (g⁻¹ * z * g)) := by rw [hu_k]
      _ = (k⁻¹ * k⁻¹) * (g⁻¹ * z * g) := by group
      _ = z * (g⁻¹ * z * g) := by rw [hkinv2]
      _ = g⁻¹ * z * g * z := huz.symm

theorem Config.conj_center_not_le_core (hC : Config z n) {g : G}
    (ha : g⁻¹ * z * g ∈ coreAt z) (hne : g⁻¹ * z * g ≠ z) :
    ¬ CFSG.conjugate (centerAt z) g ≤ coreAt z := by
  intro hle
  obtain ⟨k, hZk, hk4, hk2⟩ := hC.exists_generator
  have hkZ : k ∈ centerAt z := by
    rw [hZk]
    exact Subgroup.mem_zpowers k
  have ht : g⁻¹ * k * g ∈ CFSG.conjugate (centerAt z) g := by
    rw [mem_conjugate_iff']
    have e : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
    rw [e]
    exact hkZ
  have ht2 : (g⁻¹ * k * g) ^ 2 = g⁻¹ * z * g := by
    calc (g⁻¹ * k * g) ^ 2 = g⁻¹ * k ^ 2 * g := by simp only [sq]; group
      _ = g⁻¹ * z * g := by rw [hk2]
  have hmem : g⁻¹ * k * g ∈ coreAt z := hle ht
  rcases hC.sq_eq _ hmem with h1 | h1
  · apply ne_one_of_config hC
    have h2 : g⁻¹ * z * g = 1 := ht2.symm.trans h1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · exact hne (ht2.symm.trans h1)

end CFSG.GF2Type.CenterFour
