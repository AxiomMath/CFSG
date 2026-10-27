module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open Equiv Subgroup

section A4

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

@[expose] noncomputable def permFin4 (hΓ : Fintype.card Γ = 4) : Perm Γ ≃* Perm (Fin 4) :=
  { (Fintype.equivFinOfCardEq hΓ).permCongr with
    map_mul' := (Fintype.equivFinOfCardEq hΓ).permCongr_mul }

theorem sign_permFin4 (hΓ : Fintype.card Γ = 4) (σ : Perm Γ) :
    Perm.sign (permFin4 hΓ σ) = Perm.sign σ :=
  Perm.sign_permCongr _ σ

theorem sq_or_cube_of_alt4 (hΓ : Fintype.card Γ = 4) {σ : Perm Γ} (hσ : Perm.sign σ = 1) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  have key : ∀ x : Perm (Fin 4), Perm.sign x = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1 := by decide
  rcases key (permFin4 hΓ σ) (by rw [sign_permFin4]; exact hσ) with h | h
  · left
    apply (permFin4 hΓ).injective
    rw [map_pow, h, map_one]
  · right
    apply (permFin4 hΓ).injective
    rw [map_pow, h, map_one]

theorem mul_sq_of_alt4 (hΓ : Fintype.card Γ = 4) {σ σ' : Perm Γ} (hσ : Perm.sign σ = 1)
    (hσ' : Perm.sign σ' = 1) (h2 : σ * σ = 1) (h2' : σ' * σ' = 1) :
    σ * σ' * (σ * σ') = 1 := by
  have key : ∀ x y : Perm (Fin 4), Perm.sign x = 1 → Perm.sign y = 1 → x * x = 1 →
      y * y = 1 → x * y * (x * y) = 1 := by decide
  apply (permFin4 hΓ).injective
  rw [map_mul, map_mul, map_one]
  exact key _ _ (by rw [sign_permFin4]; exact hσ) (by rw [sign_permFin4]; exact hσ')
    (by rw [← map_mul, h2, map_one]) (by rw [← map_mul, h2', map_one])

@[expose] def fourGroupOf (hΓ : Fintype.card Γ = 4) : Subgroup (Perm Γ) where
  carrier := {σ | Perm.sign σ = 1 ∧ σ * σ = 1}
  one_mem' := ⟨map_one _, mul_one 1⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, one_mul],
    mul_sq_of_alt4 hΓ ha.1 hb.1 ha.2 hb.2⟩
  inv_mem' := fun {a} ha => by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2
    rw [Set.mem_ofPred_eq, hinv]
    exact ha

theorem card_fourGroupOf (hΓ : Fintype.card Γ = 4) : Nat.card (fourGroupOf hΓ) = 4 := by
  have key : Fintype.card {x : Perm (Fin 4) // Perm.sign x = 1 ∧ x * x = 1} = 4 := by decide
  rw [← key, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ((permFin4 hΓ).toEquiv.subtypeEquiv fun σ => ?_)
  show Perm.sign σ = 1 ∧ σ * σ = 1 ↔ _
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, sign_permFin4, ← map_mul,
    MulEquiv.map_eq_one_iff]

end A4

section Ten

theorem perm_inv_apply_self (f : Perm (Fin 10)) (x : Fin 10) : f⁻¹ (f x) = x :=
  Perm.inv_eq_iff_eq.mpr rfl

theorem perm_apply_inv_self (f : Perm (Fin 10)) (x : Fin 10) : f (f⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

variable {τ : Perm (Fin 10)}

theorem exists_ofSubtype_of_fix_compl (S : Finset (Fin 10)) {σ : Perm (Fin 10)}
    (hσ : ∀ x ∉ S, σ x = x) :
    ∃ σ' : Perm {x // x ∈ S}, Perm.ofSubtype σ' = σ ∧ Perm.sign σ' = Perm.sign σ := by
  have h₁ : ∀ x, σ x ∈ S ↔ x ∈ S := by
    intro x
    by_cases hx : x ∈ S
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      by_contra h
      have h2 : σ x = x := σ.injective (hσ _ h)
      apply h
      rw [h2]
      exact hx
    · rw [hσ x hx]
  have h₂ : ∀ x, σ x ≠ x → x ∈ S := fun x hx => by
    by_contra h
    exact hx (hσ x h)
  exact ⟨σ.subtypePerm h₁, Perm.ofSubtype_subtypePerm h₁ h₂, by
    convert Perm.sign_subtypePerm σ h₁ h₂⟩

@[expose] def fourGroup (h4 : τ.support.card = 4) : Subgroup (Perm (Fin 10)) :=
  (fourGroupOf (Γ := {x // x ∈ τ.support}) (by rw [Fintype.card_coe, h4])).map Perm.ofSubtype

theorem mem_fourGroup (h4 : τ.support.card = 4) (σ : Perm (Fin 10)) :
    σ ∈ fourGroup h4 ↔
      σ ∈ alternatingGroup (Fin 10) ∧ (∀ x ∉ τ.support, σ x = x) ∧ σ * σ = 1 := by
  constructor
  · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    refine ⟨?_, fun x hx => Perm.ofSubtype_apply_of_not_mem a hx, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact ha1
    · rw [← map_mul, ha2, map_one]
  · rintro ⟨hA, hfix, h2⟩
    obtain ⟨σ', hσ', hsign⟩ := exists_ofSubtype_of_fix_compl τ.support hfix
    refine ⟨σ', ⟨?_, ?_⟩, hσ'⟩
    · rw [hsign]
      exact hA
    · apply Perm.ofSubtype_injective
      rw [map_mul, hσ', h2, map_one]

theorem card_fourGroup (h4 : τ.support.card = 4) : Nat.card (fourGroup h4) = 4 := by
  rw [fourGroup, card_map_of_injective Perm.ofSubtype_injective, card_fourGroupOf]

theorem mem_fourGroup_of_two_elt (h4 : τ.support.card = 4) {σ : Perm (Fin 10)}
    (hA : σ ∈ alternatingGroup (Fin 10)) (hfix : ∀ x ∉ τ.support, σ x = x) {e : ℕ}
    (he : σ ^ 2 ^ e = 1) : σ ∈ fourGroup h4 := by
  refine (mem_fourGroup h4 σ).2 ⟨hA, hfix, ?_⟩
  obtain ⟨σ', hσ', hsign⟩ := exists_ofSubtype_of_fix_compl τ.support hfix
  have hΓ : Fintype.card {x // x ∈ τ.support} = 4 := by rw [Fintype.card_coe, h4]
  have hs1 : Perm.sign σ' = 1 := by rw [hsign]; exact hA
  rw [← hσ', ← map_mul]
  rcases sq_or_cube_of_alt4 hΓ hs1 with h2 | h3
  · rw [← sq, h2, map_one]
  · have he' : σ' ^ 2 ^ e = 1 := by
      apply Perm.ofSubtype_injective
      rw [map_pow, hσ', he, map_one]
    have hg := pow_gcd_eq_one.2 ⟨h3, he'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e (by decide : Nat.Coprime 3 2)),
      pow_one] at hg
    rw [hg, mul_one, map_one]

variable {L : Subgroup (Perm (Fin 10))}

theorem swap_mul_swap_mem
    (hL : ∀ l, l ∈ L ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    {x y z : Fin 10} (hxy : x ≠ y) (hyz : y ≠ z) (hx : x ∉ τ.support) (hy : y ∉ τ.support)
    (hz : z ∉ τ.support) : swap x y * swap y z ∈ L := by
  refine (hL _).2 ⟨?_, fun w hw => ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hxy, Perm.sign_swap hyz]
    decide
  · have h1 : w ≠ x := fun h => hx (h ▸ hw)
    have h2 : w ≠ y := fun h => hy (h ▸ hw)
    have h3 : w ≠ z := fun h => hz (h ▸ hw)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h3, swap_apply_of_ne_of_ne h1 h2]

theorem mem_support_of_commute {c σ : Perm (Fin 10)} (h : c * σ = σ * c) {x : Fin 10}
    (hx : x ∈ c.support) : σ x ∈ c.support := by
  rw [Perm.mem_support] at hx ⊢
  intro h1
  apply hx
  apply σ.injective
  rw [← Perm.mul_apply, ← h, Perm.mul_apply, h1]

theorem fix_of_commute_alt (hF : 4 ≤ τ.supportᶜ.card)
    (hL : ∀ l, l ∈ L ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    {σ : Perm (Fin 10)} (hσ : ∀ l ∈ L, l * σ = σ * l) : ∀ x ∉ τ.support, σ x = x := by
  intro x hx
  have hxF : x ∈ τ.supportᶜ := Finset.mem_compl.2 hx
  have hcard : 2 < (τ.supportᶜ.erase x).card := by
    rw [Finset.card_erase_of_mem hxF]
    omega
  obtain ⟨y, z, w, hy, hz, hw, hyz, hyw, hzw⟩ := Finset.two_lt_card_iff.1 hcard
  rw [Finset.mem_erase, Finset.mem_compl] at hy hz hw
  have hxy : x ≠ y := Ne.symm hy.1
  have hxz : x ≠ z := Ne.symm hz.1
  have hxw : x ≠ w := Ne.symm hw.1
  have h1 := mem_support_of_commute (hσ _ (swap_mul_swap_mem hL hxy hyz hx hy.2 hz.2))
    (x := x) (by rw [Perm.support_swap_mul_swap (by simp [hxy, hxz, hyz])]; simp)
  have h2 := mem_support_of_commute (hσ _ (swap_mul_swap_mem hL hxz hzw hx hz.2 hw.2))
    (x := x) (by rw [Perm.support_swap_mul_swap (by simp [hxz, hxw, hzw])]; simp)
  have h3 := mem_support_of_commute (hσ _ (swap_mul_swap_mem hL hxy hyw hx hy.2 hw.2))
    (x := x) (by rw [Perm.support_swap_mul_swap (by simp [hxy, hxw, hyw])]; simp)
  rw [Perm.support_swap_mul_swap (by simp [hxy, hxz, hyz])] at h1
  rw [Perm.support_swap_mul_swap (by simp [hxz, hxw, hzw])] at h2
  rw [Perm.support_swap_mul_swap (by simp [hxy, hxw, hyw])] at h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
  rcases h1 with h1 | h1 | h1
  · exact h1
  · rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
      first | exact h2 | exact h3 | (exfalso; rw [h1] at h2 h3; tauto)
  · rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
      first | exact h2 | exact h3 | (exfalso; rw [h1] at h2 h3; tauto)

theorem apply_not_mem_of_normalizer (hF : 3 ≤ τ.supportᶜ.card)
    (hL : ∀ l, l ∈ L ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    {π : Perm (Fin 10)} (hπ : π ∈ normalizer (L : Set (Perm (Fin 10)))) {x : Fin 10}
    (hx : x ∉ τ.support) : π x ∉ τ.support := by
  intro hπx
  have hxF : x ∈ τ.supportᶜ := Finset.mem_compl.2 hx
  have hcard : 1 < (τ.supportᶜ.erase x).card := by
    rw [Finset.card_erase_of_mem hxF]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase, Finset.mem_compl] at hy hz
  have hc := swap_mul_swap_mem hL (Ne.symm hy.1) hyz hx hy.2 hz.2
  have hc' := ((hL _).1 ((mem_normalizer_iff.1 hπ _).1 hc)).2 (π x) hπx
  simp only [Perm.mul_apply, perm_inv_apply_self] at hc'
  have : swap x y (swap y z x) = y := by
    rw [swap_apply_of_ne_of_ne (Ne.symm hy.1) (Ne.symm hz.1), swap_apply_left]
  rw [this] at hc'
  exact hy.1 (π.injective hc')

theorem conj_mem_fourGroup (h4 : τ.support.card = 4)
    (hL : ∀ l, l ∈ L ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    {π : Perm (Fin 10)} (hπ : π ∈ normalizer (L : Set (Perm (Fin 10)))) {σ : Perm (Fin 10)}
    (hσ : σ ∈ fourGroup h4) : π * σ * π⁻¹ ∈ fourGroup h4 := by
  have hF : τ.supportᶜ.card = 6 := by rw [Finset.card_compl, Fintype.card_fin, h4]
  obtain ⟨hA, hfix, h2⟩ := (mem_fourGroup h4 σ).1 hσ
  refine (mem_fourGroup h4 _).2 ⟨?_, fun x hx => ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_inv,
      Equiv.Perm.mem_alternatingGroup.1 hA, mul_one, mul_inv_cancel]
  ·
    have hinv : π⁻¹ x ∉ τ.support :=
      apply_not_mem_of_normalizer (by omega) hL (inv_mem hπ) hx
    rw [Perm.mul_apply, Perm.mul_apply, hfix _ hinv, perm_apply_inv_self]
  · rw [show π * σ * π⁻¹ * (π * σ * π⁻¹) = π * (σ * σ) * π⁻¹ by group, h2, mul_one,
      mul_inv_cancel]

end Ten

end CFSG.ComponentClassification.CatFactsSmall
