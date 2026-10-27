module

public import CFSG.GH74.Uniqueness.Bender.Aut

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

variable {K : Type*} [Group K]

theorem exists_fixed_of_odd_card {X : Type*} [Finite X] (f : X → X) (hf : Function.Involutive f)
    (hodd : Odd (Nat.card X)) : ∃ x, f x = x := by
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) (σ := hf.toPerm f) ?_ ?_
  · rw [← Nat.card_eq_fintype_card]
    exact Nat.not_even_iff_odd.mpr hodd ∘ even_iff_two_dvd.mpr
  · ext x
    simp [pow_one, sq, hf x]

theorem exists_second_fixed_of_even_card {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Involutive f) (heven : Even (Nat.card X)) {x₀ : X} (hx₀ : f x₀ = x₀) :
    ∃ x, x ≠ x₀ ∧ f x = x := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : Function.End X := f
  have hg : g ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact funext hf
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := X) (f := g) (p := 2) (n := 1) hg
  rw [← Nat.card_eq_fintype_card] at hmod
  have hpos : 0 < Fintype.card (Function.fixedPoints g) :=
    Fintype.card_pos_iff.mpr ⟨⟨x₀, hx₀⟩⟩
  have hev : (Nat.card X) % 2 = 0 := Nat.even_iff.mp heven
  have h1 : 1 < Fintype.card (Function.fixedPoints g) := by
    have : (Fintype.card (Function.fixedPoints g)) % 2 = 0 := by
      have := hmod
      unfold Nat.ModEq at this
      omega
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Fintype.exists_pair_of_one_lt_card h1
  by_cases hax : a = x₀
  · refine ⟨b, ?_, hb⟩
    intro hbx
    apply hab
    exact Subtype.ext (hax.trans hbx.symm)
  · exact ⟨a, hax, ha⟩

theorem aut_apply_apply_of_mul_self_eq_one {α : MulAut K} (hα : α * α = 1) (x : K) :
    α (α x) = x := by
  have := congrArg (fun a : MulAut K => a x) hα
  simpa using this

section Fixed

variable [Finite K] {n i e : ℕ}

theorem BenderType.exists_sylow_fixed
    (h : BenderType K n i e) (α : MulAut K) (hα : α * α = 1) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map α.toMonoidHom = S := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hodd : Odd (Nat.card (Sylow 2 K)) := by
    rw [Sylow.card_eq_index_normalizer Q]
    change Odd (borel (Q : Subgroup K)).index
    rw [hc.index_eq]
    have hi := h.two_le
    have : Even ((2 ^ n) ^ i) := (Nat.even_pow.mpr ⟨(Nat.even_pow.mpr ⟨even_two, by omega⟩),
      by omega⟩)
    exact this.add_one
  have hsurj : Function.Surjective α.toMonoidHom := α.surjective
  let f : Sylow 2 K → Sylow 2 K := fun S => Sylow.mapSurjective hsurj S
  have hcoe : ∀ S : Sylow 2 K, (f S : Subgroup K) = (S : Subgroup K).map α.toMonoidHom :=
    fun S => Sylow.coe_mapSurjective hsurj S
  have hf : Function.Involutive f := by
    intro S
    apply Sylow.ext
    rw [hcoe, hcoe, Subgroup.map_map]
    have : α.toMonoidHom.comp α.toMonoidHom = MonoidHom.id K :=
      MonoidHom.ext (aut_apply_apply_of_mul_self_eq_one hα)
    rw [this, Subgroup.map_id]
  obtain ⟨S, hS⟩ := exists_fixed_of_odd_card f hf hodd
  refine ⟨S, ?_⟩
  have := congrArg (fun S : Sylow 2 K => (S : Subgroup K)) hS
  simpa only [hcoe] using this

theorem BenderType.exists_fixed_involution_of_sylow
    (h : BenderType K n i e) (α : MulAut K)
    (hα : α * α = 1) (S : Sylow 2 K) (hS : (S : Subgroup K).map α.toMonoidHom = S) :
    ∃ y ∈ rootCenter (S : Subgroup K), y ≠ 1 ∧ α y = y := by
  obtain ⟨t, hc⟩ := h.exists_benderCore S
  have hZ : (rootCenter (S : Subgroup K)).map α.toMonoidHom = rootCenter (S : Subgroup K) := by
    rw [← rootCenter_map, hS]
  have hmem : ∀ z ∈ rootCenter (S : Subgroup K), α z ∈ rootCenter (S : Subgroup K) := by
    intro z hz
    rw [← hZ]
    exact ⟨z, hz, rfl⟩
  let f : rootCenter (S : Subgroup K) → rootCenter (S : Subgroup K) := fun z => ⟨α z, hmem z z.2⟩
  have hf : Function.Involutive f := fun z => Subtype.ext (aut_apply_apply_of_mul_self_eq_one hα z)
  have heven : Even (Nat.card (rootCenter (S : Subgroup K))) := by
    rw [hc.card_center]
    have hi := h.two_le
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  obtain ⟨y, hy1, hy⟩ := exists_second_fixed_of_even_card f hf heven (x₀ := 1)
    (Subtype.ext (map_one α))
  refine ⟨y, y.2, fun h1 => hy1 (Subtype.ext h1), congrArg Subtype.val hy⟩

theorem BenderType.exists_fixed_involution
    (h : BenderType K n i e) (α : MulAut K)
    (hα : α * α = 1) : ∃ y : K, y ≠ 1 ∧ y * y = 1 ∧ α y = y := by
  obtain ⟨S, hS⟩ := h.exists_sylow_fixed α hα
  obtain ⟨y, hy, hy1, hαy⟩ := h.exists_fixed_involution_of_sylow α hα S hS
  obtain ⟨t, hc⟩ := h.exists_benderCore S
  exact ⟨y, hy1, hc.center_sq y hy, hαy⟩

theorem BenderType.exists_fixed_not_mem_normalizer
    (h : BenderType K n i e) (α : MulAut K)
    (hα : α * α = 1) (S S' : Sylow 2 K) (hSS' : S ≠ S')
    (hS : (S : Subgroup K).map α.toMonoidHom = S) (hS' : (S' : Subgroup K).map α.toMonoidHom = S')
    (S'' : Sylow 2 K) : ∃ x : K, α x = x ∧ x ∉ normalizer ((S'' : Subgroup K) : Set K) := by
  obtain ⟨y, hy, hy1, hαy⟩ := h.exists_fixed_involution_of_sylow α hα S hS
  obtain ⟨y', hy', hy1', hαy'⟩ := h.exists_fixed_involution_of_sylow α hα S' hS'
  by_contra hcon
  push Not at hcon
  obtain ⟨t'', hc''⟩ := h.exists_benderCore S''
  obtain ⟨t₁, hc₁⟩ := h.exists_benderCore S
  obtain ⟨t₂, hc₂⟩ := h.exists_benderCore S'
  have hord : ∀ {z : K} {T : Sylow 2 K} {t : K}, BenderCore (2 ^ n) i e (T : Subgroup K) t →
      z ∈ rootCenter (T : Subgroup K) → z ≠ 1 → orderOf z = 2 := by
    intro z T t hc hz hz1
    apply orderOf_eq_prime _ hz1
    rw [sq]
    exact hc.center_sq z hz
  have hyS'' : y ∈ rootCenter (S'' : Subgroup K) :=
    (hc''.involution_iff.mp ⟨hcon y hαy, hord hc₁ hy hy1⟩).1
  have hy'S'' : y' ∈ rootCenter (S'' : Subgroup K) :=
    (hc''.involution_iff.mp ⟨hcon y' hαy', hord hc₂ hy' hy1'⟩).1
  have hzp : ∀ {z : K}, z ≠ 1 → Subgroup.zpowers z ≠ ⊥ := fun hz1 hbot => hz1 (by
    rw [Subgroup.zpowers_eq_bot] at hbot; exact hbot)
  have h1 : S = S'' := hc''.sylow_eq_of_ne_bot (hzp hy1)
    ((Subgroup.zpowers_le.mpr (rootCenter_le _ hyS''))) (Subgroup.zpowers_le.mpr (rootCenter_le _ hy))
  have h2 : S' = S'' := hc''.sylow_eq_of_ne_bot (hzp hy1')
    ((Subgroup.zpowers_le.mpr (rootCenter_le _ hy'S''))) (Subgroup.zpowers_le.mpr (rootCenter_le _ hy'))
  exact hSS' (h1.trans h2.symm)

theorem BenderType.outer_involution_of_fixes_two_sylows
    (h : BenderType K n i e) (α : MulAut K)
    (hα : α * α = 1)
    (hfix : ∃ S S' : Sylow 2 K, S ≠ S' ∧ (S : Subgroup K).map α.toMonoidHom = S ∧
      (S' : Subgroup K).map α.toMonoidHom = S') :
    (∃ y : K, y ≠ 1 ∧ y * y = 1 ∧ α y = y) ∧
      ∀ S : Sylow 2 K, ∃ x : K, α x = x ∧ x ∉ normalizer ((S : Subgroup K) : Set K) := by
  obtain ⟨S, S', hSS', hS, hS'⟩ := hfix
  exact ⟨h.exists_fixed_involution α hα, h.exists_fixed_not_mem_normalizer α hα S S' hSS' hS hS'⟩

end Fixed

theorem BenderType.not_outer_involution_suzuki
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 2 e) (α : MulAut K) (hα : α * α = 1) :
    ∃ g : K, ∀ x : K, α x = g * x * g⁻¹ := by
  obtain ⟨v, -, hv⟩ := h.exists_inner_of_sq_eq_one_suzuki α hα
  exact ⟨v, hv⟩

end CFSG.GH74.Uniqueness.Bender
