module

public import CFSG.GH74.GLS.IVK.Prod32.Out

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Kernel

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}

theorem lift_inner {K T : Subgroup H} (hT : IsPGroup 2 T)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K)
    (hZ : ∀ w ∈ Subgroup.center ↥K, (w : H) * w = 1) {s : H} (hs : s ∈ T)
    (hsN : ∀ y ∈ K, s * y * s⁻¹ ∈ K) (hin : ∃ k ∈ K, ∀ y ∈ K, s * y * s⁻¹ = k * y * k⁻¹) :
    ∃ k₀ ∈ T ⊓ K, s * k₀⁻¹ ∈ centralizer (K : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkx⟩ := hin
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hsNorm : s ∈ normalizer (K : Set H) := mem_normalizer_of_conj_le hsN
  set kb : ↥K := ⟨k, hk⟩ with hkb
  have hnorm : kb ∈ normalizer ((Q : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy : y ∈ (Q : Subgroup ↥K) ↔ (y : H) ∈ T := by
      rw [hQ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
    have hy' : kb * y * kb⁻¹ ∈ (Q : Subgroup ↥K) ↔ k * (y : H) * k⁻¹ ∈ T := by
      rw [hQ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (kb * y * kb⁻¹).2⟩⟩
    rw [hy, hy', ← hkx y y.2]
    constructor
    · intro h
      exact T.mul_mem (T.mul_mem hs h) (T.inv_mem hs)
    · intro h
      have := T.mul_mem (T.mul_mem (T.inv_mem hs) h) hs
      simpa [mul_assoc] using this
  obtain ⟨m, hm⟩ := hT ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hconj : ∀ n : ℕ, ∀ y ∈ K, s ^ n * y * (s ^ n)⁻¹ = k ^ n * y * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y hy; simp
    | succ n ih =>
      intro y hy
      have hs' : ∀ w ∈ K, s ^ n * w * (s ^ n)⁻¹ ∈ K := by
        intro w hw
        have := (Subgroup.mem_normalizer_iff.mp (pow_mem hsNorm n) w).mp hw
        exact this
      have h1 : s ^ (n + 1) * y * (s ^ (n + 1))⁻¹ = s ^ n * (s * y * s⁻¹) * (s ^ n)⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      have h2 : k ^ (n + 1) * y * (k ^ (n + 1))⁻¹ = k ^ n * (k * y * k⁻¹) * (k ^ n)⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [h1, h2, hkx y hy]
      exact ih _ (by
        have := K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)
        exact this)
  have hk2 : k ^ 2 ^ (m + 1) = 1 := by
    have hcen : (kb ^ 2 ^ m) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := hconj (2 ^ m) g g.2
      rw [hsm] at this
      simp only [one_mul, inv_one, mul_one] at this
      have h3 : (g : H) * k ^ 2 ^ m = k ^ 2 ^ m * g := by
        calc (g : H) * k ^ 2 ^ m = (k ^ 2 ^ m * g * (k ^ 2 ^ m)⁻¹) * k ^ 2 ^ m := by rw [← this]
          _ = k ^ 2 ^ m * g := by group
      simpa using h3
    have := hZ _ hcen
    have h4 : (k ^ 2 ^ m) * (k ^ 2 ^ m) = 1 := by simpa using this
    rw [pow_succ, pow_mul, sq]
    exact h4
  have hkbk : kb ^ 2 ^ (m + 1) = 1 := Subtype.ext (by simpa using hk2)
  have hmem : kb ∈ Q := CFSG.Walter.J1.JankoHyp.mem_sylow_of_mem_normalizer Q hnorm hkbk
  have hkT : k ∈ T ⊓ K := by
    have hmem' : kb ∈ (Q : Subgroup ↥K) := hmem
    rw [hQ, Subgroup.mem_subgroupOf] at hmem'
    exact hmem'
  refine ⟨k, hkT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h5 : k⁻¹ * y * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk
  have h6 := hkx _ h5
  have h7 : s * (k⁻¹ * y * k) * s⁻¹ = y := by rw [h6]; group
  calc y * (s * k⁻¹) = (s * (k⁻¹ * y * k) * s⁻¹) * (s * k⁻¹) := by rw [h7]
    _ = s * k⁻¹ * y := by group

theorem Setting.center_sq₁ (hS : Setting H K₁ K₂ z) {w : ↥K₁} (hw : w ∈ Subgroup.center ↥K₁) :
    (w : H) * w = 1 := by
  rcases eq_one_or_eq_of_mem_zpowers hS.z_ord (hS.center_mem₁ hw) with h | h
  · rw [h]; simp
  · rw [h]
    have := hS.z_ord
    have h2 : z ^ 2 = 1 := by rw [← this]; exact pow_orderOf_eq_one z
    simpa [sq] using h2

theorem Hyp.inner_iff_mem_P (h : Hyp H K₁ K₂ z T a)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    {s : H} (hs : s ∈ T1 T K₁) :
    (∃ k ∈ K₁, ∀ y ∈ K₁, s * y * s⁻¹ = k * y * k⁻¹) ↔ s ∈ P T K₁ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.setting
  obtain ⟨hsT, hsN⟩ := hs
  constructor
  · intro hin
    have hsN' : ∀ y ∈ K₁, s * y * s⁻¹ ∈ K₁ := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp hsN y).mp hy
    obtain ⟨k₀, hk₀, hc⟩ := lift_inner h.sylow.isPGroup h.sylow₁ (fun w hw => hS.center_sq₁ hw) hsT hsN' hin
    have hQ : T ⊓ centralizer (K₁ : Set H) = T ⊓ K₂ := by
      refine (hP₂.eq_of_le (P := T ⊓ K₂) (Q := T ⊓ centralizer (K₁ : Set H))
        (K := centralizer (K₁ : Set H)) ?_ inf_le_right ?_)
      · intro y hy
        exact ⟨hy.1, fun u hu => hS.comm u hu y hy.2⟩
      · exact h.sylow.isPGroup.to_inf_left
    have : s * k₀⁻¹ ∈ T ⊓ K₂ := by
      rw [← hQ]
      exact ⟨T.mul_mem hsT (T.inv_mem hk₀.1), hc⟩
    have hs' : s = (s * k₀⁻¹) * k₀ := by group
    rw [hs']
    exact ⟨T.mul_mem (this.1) hk₀.1, by
      have h1 : s * k₀⁻¹ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_right this.2
      have h2 : k₀ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hk₀.2
      exact (K₁ ⊔ K₂).mul_mem h1 h2⟩
  · intro hsP
    obtain ⟨k₁, hk₁, k₂, hk₂, hsk⟩ := (mem_sup_of_comm hS.comm s).mp hsP.2
    refine ⟨k₁, hk₁, fun y hy => ?_⟩
    have := hS.comm y hy k₂ hk₂
    rw [hsk]
    calc k₁ * k₂ * y * (k₁ * k₂)⁻¹ = k₁ * (k₂ * y * k₂⁻¹) * k₁⁻¹ := by group
      _ = k₁ * y * k₁⁻¹ := by
        have h2 : k₂ * y * k₂⁻¹ = y := by rw [← this]; group
        rw [h2]

end Kernel
end CFSG.GH74.GLS.IVK.Prod3
