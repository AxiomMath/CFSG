module

public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Pairing
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Perm

variable {n : ℕ}

theorem support_card_of_involution (hn : n ≤ 11) {σ : Perm (Fin n)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : sign σ = 1) : σ.support.card = 4 ∨ σ.support.card = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hm
  have hsum : σ.support.card = 2 * (m + 1) := by
    rw [← sum_cycleType, hm]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    ring
  have hsign := sign_of_cycleType σ
  rw [hm, hs] at hsign
  have hev : Even (2 * (m + 1) + (m + 1)) := by
    have : ((-1 : ℤˣ)) ^ ((Multiset.replicate (m + 1) 2).sum + (Multiset.replicate (m + 1) 2).card)
        = 1 := hsign.symm
    simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at this
    exact (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).1 (by simpa [mul_comm] using this)
  have hle : σ.support.card ≤ n := by
    simpa using Finset.card_le_univ σ.support
  obtain ⟨k, hk⟩ := hev
  omega

theorem exists_even_conj {σ τ : Perm (Fin n)} (hσ : σ * σ = 1) (hτ : τ * τ = 1) (h1 : σ ≠ 1)
    (h2 : τ ≠ 1) (hc : σ.support.card = τ.support.card) :
    ∃ g : Perm (Fin n), sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ) h1
  have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ) h2
  obtain ⟨a, ha⟩ := cycleType_prime_order (σ := σ) (by rw [hσo]; exact Nat.prime_two)
  obtain ⟨b, hb⟩ := cycleType_prime_order (σ := τ) (by rw [hτo]; exact Nat.prime_two)
  rw [hσo] at ha
  rw [hτo] at hb
  have hab : a = b := by
    have := hc
    rw [← sum_cycleType, ← sum_cycleType, ha, hb] at this
    simp only [Multiset.sum_replicate, smul_eq_mul] at this
    omega
  have hcyc : σ.cycleType = τ.cycleType := by rw [ha, hb, hab]
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 hcyc)
  by_cases hs : sign g = 1
  · exact ⟨g, hs, hg⟩
  · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact h1 (Equiv.ext hcon)
    have hσσ : σ (σ x) = x := by
      have := congrArg (fun p : Perm (Fin n) => p x) hσ
      simpa using this
    have hcomm : swap x (σ x) * σ * (swap x (σ x))⁻¹ = σ := by
      have h0 := swap_apply_apply σ x (σ x)
      rw [hσσ, swap_comm] at h0
      have h' : swap x (σ x) * σ = σ * swap x (σ x) := by
        calc swap x (σ x) * σ = (σ * swap x (σ x) * σ⁻¹) * σ := by rw [← h0]
          _ = σ * swap x (σ x) := by group
      calc swap x (σ x) * σ * (swap x (σ x))⁻¹ = σ * swap x (σ x) * (swap x (σ x))⁻¹ := by
            rw [h']
        _ = σ := by group
    refine ⟨g * swap x (σ x), ?_, ?_⟩
    · rw [Perm.sign_mul, Perm.sign_swap hx.symm]
      rcases Int.units_eq_one_or (sign g) with h | h
      · exact absurd h hs
      · rw [h]; decide
    · calc g * swap x (σ x) * σ * (g * swap x (σ x))⁻¹
          = g * (swap x (σ x) * σ * (swap x (σ x))⁻¹) * g⁻¹ := by group
        _ = τ := by rw [hcomm, hg]

end Perm

section Four

variable {n : ℕ} {a₁ b₁ a₂ b₂ : Fin n}

theorem conj_swap_mul_swap (g : Perm (Fin n)) (a b c d : Fin n) :
    g * (swap a b * swap c d) * g⁻¹ = swap (g a) (g b) * swap (g c) (g d) := by
  rw [swap_apply_apply g a b, swap_apply_apply g c d]
  group

theorem g1_conj (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁) (h1b2 : a₁ ≠ b₂)
    (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) :
    (swap b₁ a₂ * swap a₁ b₁) * (swap a₁ b₁ * swap a₂ b₂) * (swap b₁ a₂ * swap a₁ b₁)⁻¹ =
      swap a₁ a₂ * swap b₁ b₂ := by
  have := h12.symm
  have := h1b1.symm
  have := h1b2.symm
  have := h2b1.symm
  have := h2b2.symm
  have := hbb.symm
  rw [conj_swap_mul_swap]
  have e1 : (swap b₁ a₂ * swap a₁ b₁) a₁ = a₂ := by simp [Perm.mul_apply, *]
  have e2 : (swap b₁ a₂ * swap a₁ b₁) b₁ = a₁ := by simp [Perm.mul_apply, swap_apply_def, *]
  have e3 : (swap b₁ a₂ * swap a₁ b₁) a₂ = b₁ := by simp [Perm.mul_apply, swap_apply_def, *]
  have e4 : (swap b₁ a₂ * swap a₁ b₁) b₂ = b₂ := by simp [Perm.mul_apply, swap_apply_def, *]
  rw [e1, e2, e3, e4, swap_comm a₂ a₁]

theorem swap_mul_eq (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁) (h1b2 : a₁ ≠ b₂)
    (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) :
    (swap a₁ b₁ * swap a₂ b₂) * (swap a₁ a₂ * swap b₁ b₂) = swap a₁ b₂ * swap a₂ b₁ := by
  have := h12.symm
  have := h1b1.symm
  have := h1b2.symm
  have := h2b1.symm
  have := h2b2.symm
  have := hbb.symm
  ext x
  by_cases hx1 : x = a₁
  · subst hx1
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx2 : x = b₁
  · subst hx2
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx3 : x = a₂
  · subst hx3
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx4 : x = b₂
  · subst hx4
    simp [Perm.mul_apply, swap_apply_def, *]
  simp [Perm.mul_apply, swap_apply_def, *]

theorem g2_conj (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁) (h1b2 : a₁ ≠ b₂)
    (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) :
    (swap b₁ b₂ * swap a₁ b₁) * (swap a₁ b₁ * swap a₂ b₂) * (swap b₁ b₂ * swap a₁ b₁)⁻¹ =
      swap a₁ b₂ * swap a₂ b₁ := by
  have := h12.symm
  have := h1b1.symm
  have := h1b2.symm
  have := h2b1.symm
  have := h2b2.symm
  have := hbb.symm
  rw [conj_swap_mul_swap]
  have e1 : (swap b₁ b₂ * swap a₁ b₁) a₁ = b₂ := by simp [Perm.mul_apply, *]
  have e2 : (swap b₁ b₂ * swap a₁ b₁) b₁ = a₁ := by simp [Perm.mul_apply, swap_apply_def, *]
  have e3 : (swap b₁ b₂ * swap a₁ b₁) a₂ = a₂ := by simp [Perm.mul_apply, swap_apply_def, *]
  have e4 : (swap b₁ b₂ * swap a₁ b₁) b₂ = b₁ := by simp [Perm.mul_apply, swap_apply_def, *]
  rw [e1, e2, e3, e4, swap_comm b₂ a₁, swap_comm a₂ b₁]

theorem sign_swap_mul_swap {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

theorem eq_swap_mul_swap {σ : Perm (Fin n)} (h12 : a₁ ≠ a₂) (h1b1 : a₁ ≠ b₁) (h1b2 : a₁ ≠ b₂)
    (h2b1 : a₂ ≠ b₁) (h2b2 : a₂ ≠ b₂) (hbb : b₁ ≠ b₂) (hσ : σ.support.card = 4)
    (e1 : σ a₁ = b₁) (e2 : σ a₂ = b₂) (e3 : σ b₁ = a₁) (e4 : σ b₂ = a₂) :
    σ = swap a₁ b₁ * swap a₂ b₂ := by
  have := h12.symm
  have := h1b1.symm
  have := h1b2.symm
  have := h2b1.symm
  have := h2b2.symm
  have := hbb.symm
  have hsub : ({a₁, b₁, a₂, b₂} : Finset (Fin n)) ⊆ σ.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Perm.mem_support]
    rcases hx with rfl | rfl | rfl | rfl
    · rw [e1]; exact h1b1.symm
    · rw [e3]; exact h1b1
    · rw [e2]; exact h2b2.symm
    · rw [e4]; exact h2b2
  have hcard : ({a₁, b₁, a₂, b₂} : Finset (Fin n)).card = 4 := by
    simp [Finset.card_insert_of_notMem, *]
  have heq : ({a₁, b₁, a₂, b₂} : Finset (Fin n)) = σ.support :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  ext x
  by_cases hx1 : x = a₁
  · subst hx1
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx2 : x = b₁
  · subst hx2
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx3 : x = a₂
  · subst hx3
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx4 : x = b₂
  · subst hx4
    simp [Perm.mul_apply, swap_apply_def, *]
  have hxs : x ∉ σ.support := by
    rw [← heq]
    simp [hx1, hx2, hx3, hx4]
  rw [Perm.notMem_support] at hxs
  simp [Perm.mul_apply, swap_apply_def, *]

end Four

structure CoverSetup (n : ℕ) (K : Type) [Group K] where
  π : K →* alternatingGroup (Fin n)
  surj : Function.Surjective π
  ker : π.ker = center K
  hX : IsDoubleCoverOfAlt K n

noncomputable def CoverSetup.ofCover {n : ℕ} {K : Type} [Group K] (hX : IsDoubleCoverOfAlt K n) :
    CoverSetup n K :=
  let h := CFSG.Sporadic.Recognition.LyonsSims.exists_centralExtension_of_doubleCover hX
  { π := h.choose, surj := h.choose_spec.1, ker := h.choose_spec.2, hX := hX }

namespace CoverSetup

variable {n : ℕ} {K : Type} [Group K]

@[expose] def ρ (C : CoverSetup n K) : K →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp C.π

theorem ρ_apply (C : CoverSetup n K) (x : K) :
    C.ρ x = ((C.π x : alternatingGroup (Fin n)) : Perm (Fin n)) := rfl

theorem ρ_eq_one_iff (C : CoverSetup n K) {x : K} : C.ρ x = 1 ↔ x ∈ center K := by
  rw [← C.ker, MonoidHom.mem_ker, ρ_apply]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem sign_ρ (C : CoverSetup n K) (x : K) : sign (C.ρ x) = 1 :=
  Perm.mem_alternatingGroup.1 (C.π x).2

theorem exists_ρ_eq (C : CoverSetup n K) {σ : Perm (Fin n)} (hσ : sign σ = 1) :
    ∃ x, C.ρ x = σ := by
  obtain ⟨x, hx⟩ := C.surj ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem center_card (C : CoverSetup n K) : Nat.card (center K) = 2 := C.hX.2.1

theorem sq_of_mem_center (C : CoverSetup n K) {z : K} (hz : z ∈ center K) : z * z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : center K) ∣ Nat.card (center K) := orderOf_dvd_natCard _
  rw [C.center_card] at h1
  have h2 : (⟨z, hz⟩ : center K) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
  simpa [pow_two] using congrArg Subtype.val h2

theorem sq_mem_center (C : CoverSetup n K) {x : K} (h : C.ρ x * C.ρ x = 1) :
    x * x ∈ center K := by
  rw [← C.ρ_eq_one_iff, map_mul]
  exact h

theorem sq_conj (C : CoverSetup n K) {u v : K} {g : Perm (Fin n)} (hu : C.ρ u * C.ρ u = 1)
    (hg : sign g = 1) (hv : C.ρ v = g * C.ρ u * g⁻¹) : v * v = u * u := by
  obtain ⟨k, hk⟩ := C.exists_ρ_eq hg
  have hw : C.ρ (k * u * k⁻¹) = C.ρ v := by rw [map_mul, map_mul, map_inv, hk, hv]
  have hc : (k * u * k⁻¹)⁻¹ * v ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hw, inv_mul_cancel]
  obtain ⟨c, hcc, hvc⟩ : ∃ c ∈ center K, v = (k * u * k⁻¹) * c :=
    ⟨(k * u * k⁻¹)⁻¹ * v, hc, by group⟩
  have huu : u * u ∈ center K := C.sq_mem_center hu
  have hcc2 : c * c = 1 := C.sq_of_mem_center hcc
  have hww : (k * u * k⁻¹) * (k * u * k⁻¹) = u * u := by
    calc (k * u * k⁻¹) * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
      _ = u * u := by rw [mem_center_iff.1 huu k]; group
  have hcw : (k * u * k⁻¹) * c = c * (k * u * k⁻¹) := mem_center_iff.1 hcc _
  rw [hvc]
  calc k * u * k⁻¹ * c * (k * u * k⁻¹ * c)
      = (k * u * k⁻¹) * (c * (k * u * k⁻¹)) * c := by group
    _ = (k * u * k⁻¹) * ((k * u * k⁻¹) * c) * c := by rw [← hcw]
    _ = ((k * u * k⁻¹) * (k * u * k⁻¹)) * (c * c) := by group
    _ = u * u := by rw [hww, hcc2, mul_one]

theorem sq_mul_of_comm_central {x y : K} (h : x * y * x⁻¹ * y⁻¹ ∈ center K) :
    (x * y) * (x * y) = (x * y * x⁻¹ * y⁻¹)⁻¹ * ((x * x) * (y * y)) := by
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hyx : y * x = c⁻¹ * (x * y) := by simp [hc]; group
  have hxc : x * c⁻¹ = c⁻¹ * x := mem_center_iff.1 (inv_mem h) x
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (c⁻¹ * (x * y)) * y := by rw [hyx]
    _ = (x * c⁻¹) * (x * y) * y := by group
    _ = (c⁻¹ * x) * (x * y) * y := by rw [hxc]
    _ = c⁻¹ * ((x * x) * (y * y)) := by group

end CoverSetup

section PermFacts

variable {n : ℕ}

theorem IsoI.ne_one {σ : Perm (Fin n)} (h : IsoI σ) : σ ≠ 1 := by
  rintro rfl
  have := h.2
  simp at this

theorem DblI.ne_one {σ : Perm (Fin n)} (h : DblI σ) : σ ≠ 1 := by
  rintro rfl
  have := h.2
  simp at this

theorem IsoI.sign_eq_one {σ : Perm (Fin n)} (h : IsoI σ) : sign σ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.1) h.ne_one
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hm
  have hsum : σ.support.card = 2 * (m + 1) := by
    rw [← sum_cycleType, hm]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    ring
  have hm3 : m = 3 := by have := h.2; omega
  rw [sign_of_cycleType, hm, hm3]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  exact Even.neg_one_pow ⟨6, by norm_num⟩

theorem DblI.sign_eq_one {σ : Perm (Fin n)} (h : DblI σ) : sign σ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.1) h.ne_one
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hm
  have hsum : σ.support.card = 2 * (m + 1) := by
    rw [← sum_cycleType, hm]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    ring
  have hm3 : m = 1 := by have := h.2; omega
  rw [sign_of_cycleType, hm, hm3]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  exact Even.neg_one_pow ⟨3, by norm_num⟩

end PermFacts

namespace CoverSetup

variable {n : ℕ} {K : Type} [Group K]

theorem dblI_sq_ne_one (C : CoverSetup n K) (hn : 8 ≤ n) {x : K} (h : DblI (C.ρ x)) :
    x * x ≠ 1 := by
  obtain ⟨hσ2, hσc⟩ := h
  have hσ1 : C.ρ x ≠ 1 := fun h1 => by rw [h1] at hσc; simp at hσc
  obtain ⟨a₁, b₁, a₂, b₂, h12, h1b1, h1b2, h2b1, h2b2, hbb, e1, e2, e3, e4⟩ :=
    exists_swap_pairs (C.π x).2 hσ2 hσ1
  have hσeq : C.ρ x = swap a₁ b₁ * swap a₂ b₂ :=
    eq_swap_mul_swap h12 h1b1 h1b2 h2b1 h2b2 hbb hσc e1 e2 e3 e4
  obtain ⟨y, hy⟩ := C.exists_ρ_eq (sign_swap_mul_swap h12 hbb)
  have hne : ⁅x, y⁆ ≠ 1 :=
    commutator_ne_one_of_doubleCover hn C.hX C.surj C.ker h12 h1b1 h1b2 h2b1 h2b2 hbb e1 e2 e3 e4 hy
  have hcomm : C.ρ x * C.ρ y = C.ρ y * C.ρ x := by
    rw [hy]
    exact comm_swap_pairs h1b1 h1b2 h2b1 h2b2 (C.ρ x) e1 e2 e3 e4
  have hc : x * y * x⁻¹ * y⁻¹ ∈ center K := by
    rw [← C.ρ_eq_one_iff]
    simp only [map_mul, map_inv]
    calc C.ρ x * C.ρ y * (C.ρ x)⁻¹ * (C.ρ y)⁻¹ = (C.ρ y * C.ρ x) * (C.ρ x)⁻¹ * (C.ρ y)⁻¹ := by
          rw [hcomm]
      _ = 1 := by group
  have hsq := CoverSetup.sq_mul_of_comm_central hc
  have hu : C.ρ x * C.ρ x = 1 := hσ2
  have hyy : y * y = x * x := by
    refine C.sq_conj (g := (swap b₁ a₂ * swap a₁ b₁)) hu
      (sign_swap_mul_swap h2b1.symm h1b1) ?_
    rw [hy, hσeq, g1_conj h12 h1b1 h1b2 h2b1 h2b2 hbb]
  have hxy : (x * y) * (x * y) = x * x := by
    refine C.sq_conj (g := (swap b₁ b₂ * swap a₁ b₁)) hu
      (sign_swap_mul_swap hbb h1b1) ?_
    rw [map_mul, hy, hσeq, swap_mul_eq h12 h1b1 h1b2 h2b1 h2b2 hbb,
      g2_conj h12 h1b1 h1b2 h2b1 h2b2 hbb]
  have hxx : x * x ∈ center K := C.sq_mem_center hu
  have hxx2 : (x * x) * (x * x) = 1 := C.sq_of_mem_center hxx
  rw [hxy, hyy, hxx2, mul_one] at hsq
  intro h1
  rw [h1] at hsq
  have : (x * y * x⁻¹ * y⁻¹)⁻¹ = 1 := hsq.symm
  exact hne (by rw [commutatorElement_def]; exact inv_eq_one.1 this)

theorem isoI_sq_eq_one (C : CoverSetup n K) (hn : 8 ≤ n) (hn' : n ≤ 11)
    (E8 : ∃ a b c : Perm (Fin n), IsoI a ∧ IsoI b ∧ IsoI c ∧ Indep2 a b ∧ Indep3 a b c)
    {x : K} (h : IsoI (C.ρ x)) : x * x = 1 := by
  obtain ⟨a, b, c, ha, hb, hc, ⟨hab, hab'⟩, ⟨hac, hbc, hac', hbc', habc⟩⟩ := E8
  obtain ⟨u, hu2, hunc⟩ :=
    CFSG.Sporadic.Recognition.LyonsSims.exists_noncentral_involution_of_map_gen C.ρ a b c hab hac
      hbc ha.1 hb.1 hc.1 ha.ne_one hb.ne_one hc.ne_one hab'.ne_one hac'.ne_one hbc'.ne_one
      habc.ne_one hab'.1 hac'.1 hbc'.1 habc.1 (C.exists_ρ_eq ha.sign_eq_one)
      (C.exists_ρ_eq hb.sign_eq_one) (C.exists_ρ_eq hc.sign_eq_one)
      (fun x => C.ρ_eq_one_iff) C.center_card
  have hu1 : u * u = 1 := by rw [← pow_two]; exact hu2
  have hσ0 : C.ρ u * C.ρ u = 1 := by rw [← map_mul, hu1, map_one]
  have hσ1 : C.ρ u ≠ 1 := fun h1 => hunc (C.ρ_eq_one_iff.1 h1)
  have hiso : IsoI (C.ρ u) := by
    rcases support_card_of_involution hn' hσ0 hσ1 (C.sign_ρ u) with h4 | h8
    · exact absurd hu1 (C.dblI_sq_ne_one hn ⟨hσ0, h4⟩)
    · exact ⟨hσ0, h8⟩
  obtain ⟨g, hg, hgc⟩ := exists_even_conj hiso.1 h.1 hiso.ne_one h.ne_one (by rw [hiso.2, h.2])
  rw [C.sq_conj hσ0 hg hgc.symm, hu1]

end CoverSetup

end CFSG.OddStandard.Solomon75.AhatData
