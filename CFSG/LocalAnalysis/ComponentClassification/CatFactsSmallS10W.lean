module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10V

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open Equiv Subgroup

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    {x : G} (h : ∀ g ∈ E, x * g * x⁻¹ ∈ E) : x ∈ normalizer (E : Set G) := by
  have hle : E.map (MulAut.conj x).toMonoidHom ≤ E := by
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  have heq : E.map (MulAut.conj x).toMonoidHom = E :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective])
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hle ⟨y, hy, rfl⟩, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨w, hw, hwy⟩ := hy
  have : w = y := by
    have h2 : x * w * x⁻¹ = x * y * x⁻¹ := hwy
    simpa using h2
  rwa [← this]

section Ten

variable {τ : Perm (Fin 10)}

theorem exists_conj_fourGroup (h4 : τ.support.card = 4) {σ₁ σ₂ : Perm (Fin 10)}
    (h₁ : σ₁ ∈ fourGroup h4) (h₂ : σ₂ ∈ fourGroup h4) (h₁1 : σ₁ ≠ 1) (h₂1 : σ₂ ≠ 1) :
    ∃ π ∈ alternatingGroup (Fin 10), π ∈ normalizer (fourGroup h4 : Set (Perm (Fin 10))) ∧
      π * σ₁ * π⁻¹ = σ₂ := by
  have hΓ : Fintype.card {x // x ∈ τ.support} = 4 := by rw [Fintype.card_coe, h4]
  have key : ∀ x y : Perm (Fin 4), Perm.sign x = 1 → x * x = 1 → x ≠ 1 → Perm.sign y = 1 →
      y * y = 1 → y ≠ 1 → ∃ p : Perm (Fin 4), Perm.sign p = 1 ∧ p * x * p⁻¹ = y := by decide
  obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := h₁
  obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := h₂
  set e := permFin4 hΓ
  have hne : ∀ c : Perm {x // x ∈ τ.support}, Perm.ofSubtype c ≠ 1 → e c ≠ 1 := by
    intro c hc h
    apply hc
    rw [e.map_eq_one_iff.1 h, map_one]
  obtain ⟨p, hp1, hp⟩ := key (e a) (e b) (by rw [sign_permFin4]; exact ha1)
    (by rw [← map_mul, ha2, map_one]) (hne a h₁1) (by rw [sign_permFin4]; exact hb1)
    (by rw [← map_mul, hb2, map_one]) (hne b h₂1)
  set p' := e.symm p with hp'
  have hp'1 : Perm.sign p' = 1 := by
    rw [← sign_permFin4 hΓ, hp', MulEquiv.apply_symm_apply]
    exact hp1
  have hconj : p' * a * p'⁻¹ = b := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, hp', MulEquiv.apply_symm_apply]
    exact hp
  refine ⟨Perm.ofSubtype p', ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
    exact hp'1
  · apply mem_normalizer_of_forall_conj_mem
    rintro _ ⟨c, ⟨hc1, hc2⟩, rfl⟩
    refine ⟨p' * c * p'⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv, hp'1, hc1, inv_one, one_mul, one_mul]
    · rw [show p' * c * p'⁻¹ * (p' * c * p'⁻¹) = p' * (c * c) * p'⁻¹ by group, hc2, mul_one,
        mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, hconj]

theorem exists_two_elt_fourGroup (h4 : τ.support.card = 4) :
    ∃ π ∈ alternatingGroup (Fin 10), π ∈ normalizer (fourGroup h4 : Set (Perm (Fin 10))) ∧
      π * π = 1 ∧ ∃ σ ∈ fourGroup h4, π * σ * π⁻¹ ≠ σ := by
  have hΓ : Fintype.card {x // x ∈ τ.support} = 4 := by rw [Fintype.card_coe, h4]
  have key : ∃ t : Perm (Fin 4), Perm.sign t = -1 ∧ t * t = 1 ∧
      ∃ x : Perm (Fin 4), Perm.sign x = 1 ∧ x * x = 1 ∧ t * x * t⁻¹ ≠ x := by decide
  obtain ⟨t, ht1, ht2, x, hx1, hx2, htx⟩ := key
  set e := permFin4 hΓ
  set t' := e.symm t with ht'
  set x' := e.symm x with hx'
  have ht'1 : Perm.sign t' = -1 := by
    rw [← sign_permFin4 hΓ, ht', MulEquiv.apply_symm_apply]
    exact ht1
  have ht'2 : t' * t' = 1 := by
    apply e.injective
    rw [map_mul, ht', MulEquiv.apply_symm_apply, ht2, map_one]
  have hx'1 : Perm.sign x' = 1 := by
    rw [← sign_permFin4 hΓ, hx', MulEquiv.apply_symm_apply]
    exact hx1
  have hx'2 : x' * x' = 1 := by
    apply e.injective
    rw [map_mul, hx', MulEquiv.apply_symm_apply, hx2, map_one]
  have hF : 1 < τ.supportᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, h4]
    norm_num
  obtain ⟨ω₁, hω₁, ω₂, hω₂, hω⟩ := Finset.one_lt_card.1 hF
  rw [Finset.mem_compl] at hω₁ hω₂
  set s := swap ω₁ ω₂ with hs
  have hscomm : ∀ c : Perm {x // x ∈ τ.support}, Perm.ofSubtype c * s = s * Perm.ofSubtype c := by
    intro c
    have hd : Perm.Disjoint (Perm.ofSubtype c) s := fun y => by
      by_cases hy : y ∈ τ.support
      · have h1 : y ≠ ω₁ := fun h => hω₁ (h ▸ hy)
        have h2 : y ≠ ω₂ := fun h => hω₂ (h ▸ hy)
        exact Or.inr (swap_apply_of_ne_of_ne h1 h2)
      · exact Or.inl (Perm.ofSubtype_apply_of_not_mem c hy)
    exact hd.commute.eq
  refine ⟨Perm.ofSubtype t' * s, ?_, ?_, ?_, Perm.ofSubtype x', ⟨x', ⟨hx'1, hx'2⟩, rfl⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_ofSubtype, ht'1, hs,
      Perm.sign_swap hω]
    decide
  · apply mem_normalizer_of_forall_conj_mem
    rintro _ ⟨c, ⟨hc1, hc2⟩, rfl⟩
    refine ⟨t' * c * t'⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv, hc1, mul_one, mul_inv_cancel]
    · rw [show t' * c * t'⁻¹ * (t' * c * t'⁻¹) = t' * (c * c) * t'⁻¹ by group, hc2, mul_one,
        mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, mul_inv_rev, show Perm.ofSubtype t' * s * Perm.ofSubtype c *
        (s⁻¹ * (Perm.ofSubtype t')⁻¹) = Perm.ofSubtype t' * (s * Perm.ofSubtype c * s⁻¹) *
          (Perm.ofSubtype t')⁻¹ by group, ← hscomm c, mul_inv_cancel_right]
  · rw [show Perm.ofSubtype t' * s * (Perm.ofSubtype t' * s) =
        Perm.ofSubtype t' * (s * Perm.ofSubtype t') * s by group, ← hscomm t',
      show Perm.ofSubtype t' * (Perm.ofSubtype t' * s) * s =
        Perm.ofSubtype (t' * t') * (s * s) by rw [map_mul]; group, ht'2, hs, swap_mul_self,
      map_one, one_mul]
  · intro h
    apply htx
    rw [mul_inv_rev, show Perm.ofSubtype t' * s * Perm.ofSubtype x' *
        (s⁻¹ * (Perm.ofSubtype t')⁻¹) =
        Perm.ofSubtype t' * (s * Perm.ofSubtype x' * s⁻¹) * (Perm.ofSubtype t')⁻¹ by group,
      ← hscomm x', mul_inv_cancel_right, ← map_inv, ← map_mul, ← map_mul] at h
    have h2 := Perm.ofSubtype_injective h
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, map_inv, ht', hx', MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply] at h3

theorem support_card_eq_four {σ : Perm (Fin 10)} (hA : σ ∈ alternatingGroup (Fin 10))
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) {S : Finset (Fin 10)} (hS : ∀ x ∉ S, σ x = x)
    (h7 : S.card ≤ 7) : σ.support.card = 4 := by
  obtain ⟨hc, hpar, hpos⟩ := cycleType_of_involution h2 h1
  have hsub : σ.support ⊆ S := fun x hx => by
    by_contra h
    exact (Perm.mem_support.1 hx) (hS x h)
  have hle := Finset.card_le_card hsub
  have hsign := Perm.sign_of_cycleType σ
  rw [hc, Multiset.sum_replicate, Multiset.card_replicate,
    Equiv.Perm.mem_alternatingGroup.1 hA] at hsign
  set k := σ.support.card / 2 with hk
  have hev : Even k := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have : (-1 : ℤˣ) ^ (k • 2 + k) = -1 := by
      rw [smul_eq_mul, show k * 2 + k = 3 * k by ring]
      exact (Odd.mul (by decide) hodd).neg_one_pow
    rw [this] at hsign
    exact absurd hsign (by decide)
  obtain ⟨j, hj⟩ := hev
  omega

theorem exists_alt_conj_of_support_four {σ₁ σ₂ : Perm (Fin 10)} (h₁2 : σ₁ * σ₁ = 1)
    (h₁1 : σ₁ ≠ 1) (h₂2 : σ₂ * σ₂ = 1) (h₂1 : σ₂ ≠ 1) (hs₁ : σ₁.support.card = 4)
    (hs₂ : σ₂.support.card = 4) :
    ∃ π ∈ alternatingGroup (Fin 10), π * σ₁ * π⁻¹ = σ₂ := by
  have hc₁ := (cycleType_of_involution h₁2 h₁1).1
  have hc₂ := (cycleType_of_involution h₂2 h₂1).1
  rw [hs₁] at hc₁
  rw [hs₂] at hc₂
  obtain ⟨c, hc⟩ := isConj_iff.1 (Perm.isConj_iff_cycleType_eq.2 (hc₁.trans hc₂.symm))
  rcases Int.units_eq_one_or (Perm.sign c) with hs | hs
  · exact ⟨c, hs, hc⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [hs₁]; norm_num : 0 < σ₁.support.card)
  have hxy : x ≠ σ₁ x := fun h => (Perm.mem_support.1 hx) h.symm
  have hσσ : σ₁ (σ₁ x) = x := by rw [← Perm.mul_apply, h₁2, Perm.one_apply]
  have h1 : σ₁ * swap x (σ₁ x) * σ₁⁻¹ = swap x (σ₁ x) := by
    rw [← swap_apply_apply, hσσ, swap_comm]
  have h2 : swap x (σ₁ x) * σ₁ * (swap x (σ₁ x))⁻¹ = σ₁ := by
    have h3 : σ₁ * swap x (σ₁ x) = swap x (σ₁ x) * σ₁ :=
      calc σ₁ * swap x (σ₁ x) = σ₁ * swap x (σ₁ x) * σ₁⁻¹ * σ₁ := by group
        _ = swap x (σ₁ x) * σ₁ := by rw [h1]
    rw [← h3, mul_inv_cancel_right]
  refine ⟨c * swap x (σ₁ x), ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs, Perm.sign_swap hxy]
    decide
  · rw [mul_inv_rev, show c * swap x (σ₁ x) * σ₁ * ((swap x (σ₁ x))⁻¹ * c⁻¹) =
      c * (swap x (σ₁ x) * σ₁ * (swap x (σ₁ x))⁻¹) * c⁻¹ by group, h2, hc]

end Ten

end CFSG.ComponentClassification.CatFactsSmall
