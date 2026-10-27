module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Dih
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

open Equiv

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

local instance decEqM128 : DecidableEq M128 := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2, fun h => ⟨by rw [h], by rw [h]⟩⟩

def q8word : Fin 8 → R0
  | 0 => 1
  | 1 => aR
  | 2 => wR
  | 3 => aR * wR
  | 4 => wR * aR
  | 5 => aR * wR * aR
  | 6 => wR * aR * wR
  | 7 => aR * wR * aR * wR

def q8mk (a b : ZMod 4) (k : Fin 8) : M128 := ⟨Multiplicative.ofAdd (a, b), q8word k⟩

def q8gens : Fin 6 → M128 × M128
  | 0 => (q8mk 0 1 0, q8mk 1 0 7)
  | 1 => (q8mk 0 1 0, q8mk 2 0 6)
  | 2 => (q8mk 0 1 0, q8mk 3 0 7)
  | 3 => (q8mk 0 1 1, q8mk 2 0 1)
  | 4 => (q8mk 1 0 7, q8mk 2 1 0)
  | 5 => (q8mk 1 1 7, q8mk 2 1 0)

def q8list (i : Fin 6) : List M128 :=
  [1, zeta, (q8gens i).1, (q8gens i).1⁻¹, (q8gens i).2, (q8gens i).2⁻¹,
    (q8gens i).1 * (q8gens i).2, ((q8gens i).1 * (q8gens i).2)⁻¹]

theorem q8_cases : ∀ x : M128, x * x = zeta → ∀ y : M128, y * y = zeta → y * x * y⁻¹ = x⁻¹ →
    ∃ i : Fin 6, x ∈ q8list i ∧ y ∈ q8list i := by decide +kernel

theorem q8list_mul : ∀ i : Fin 6, ∀ a ∈ q8list i, ∀ b ∈ q8list i, a * b ∈ q8list i := by decide +kernel

theorem q8list_inv : ∀ i : Fin 6, ∀ a ∈ q8list i, a⁻¹ ∈ q8list i := by decide +kernel

theorem q8list_card : ∀ i : Fin 6, Fintype.card {x : M128 // x ∈ q8list i} = 8 := by decide +kernel

theorem q8_noncomm : ∀ i j : Fin 6, (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨
    ∃ a ∈ q8list i, ∃ b ∈ q8list j, a * b ≠ b * a := by decide +kernel

theorem one_mem_q8list (i : Fin 6) : (1 : M128) ∈ q8list i := by simp [q8list]

def q8sub (i : Fin 6) : Subgroup M128 where
  carrier := {x | x ∈ q8list i}
  mul_mem' {a b} ha hb := q8list_mul i a ha b hb
  one_mem' := one_mem_q8list i
  inv_mem' {a} ha := q8list_inv i a ha

theorem card_q8sub (i : Fin 6) : Nat.card ↥(q8sub i) = 8 := by
  have h1 : Nat.card ↥(q8sub i) = Nat.card {x : M128 // x ∈ q8list i} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  rw [h1, Nat.card_eq_fintype_card]
  exact q8list_card i

theorem card_quaternionGroup_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem q8_inv_eq {Q : Subgroup M128} (e : ↥Q ≃* QuaternionGroup 2) (hζ : zeta ∈ Q) :
    e ⟨zeta, hζ⟩ = QuaternionGroup.a 2 := by
  have h1 : (⟨zeta, hζ⟩ : ↥Q) * ⟨zeta, hζ⟩ = 1 := Subtype.ext zeta_mul_self
  have h2 : (⟨zeta, hζ⟩ : ↥Q) ≠ 1 := fun h => zeta_ne_one (congrArg Subtype.val h)
  have h3 : e ⟨zeta, hζ⟩ * e ⟨zeta, hζ⟩ = 1 := by rw [← map_mul, h1, map_one]
  have h4 : e ⟨zeta, hζ⟩ ≠ 1 := fun h => h2 (e.injective (by rw [h, map_one]))
  generalize e ⟨zeta, hζ⟩ = g at h3 h4
  revert g
  decide

theorem q8_gen_rels {Q : Subgroup M128} (e : ↥Q ≃* QuaternionGroup 2) (hζ : zeta ∈ Q) :
    ((e.symm (QuaternionGroup.a 1) : ↥Q) : M128) * ((e.symm (QuaternionGroup.a 1) : ↥Q) : M128) = zeta ∧
    ((e.symm (QuaternionGroup.xa 0) : ↥Q) : M128) * ((e.symm (QuaternionGroup.xa 0) : ↥Q) : M128) = zeta ∧
    ((e.symm (QuaternionGroup.xa 0) : ↥Q) : M128) * ((e.symm (QuaternionGroup.a 1) : ↥Q) : M128) *
      ((e.symm (QuaternionGroup.xa 0) : ↥Q) : M128)⁻¹ = ((e.symm (QuaternionGroup.a 1) : ↥Q) : M128)⁻¹ := by
  have hz : e.symm (QuaternionGroup.a 2) = ⟨zeta, hζ⟩ := by
    rw [MulEquiv.symm_apply_eq]; exact (q8_inv_eq e hζ).symm
  have r1 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 = QuaternionGroup.a 2 := by decide
  have r2 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 := by decide
  have r3 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
      (QuaternionGroup.a 1)⁻¹ := by decide
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun t : ↥Q => (t : M128)) (show e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.a 1) = ⟨zeta, hζ⟩ by
      rw [← map_mul, r1, hz])
    simpa using this
  · have := congrArg (fun t : ↥Q => (t : M128)) (show e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa 0) = ⟨zeta, hζ⟩ by
      rw [← map_mul, r2, hz])
    simpa using this
  · have := congrArg (fun t : ↥Q => (t : M128)) (show e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) *
        (e.symm (QuaternionGroup.xa 0))⁻¹ = (e.symm (QuaternionGroup.a 1))⁻¹ by
      rw [← map_inv, ← map_mul, ← map_mul, r3, map_inv])
    simpa using this

theorem q8_words : ∀ γ : QuaternionGroup 2, ∃ i : Fin 4, ∃ j : Fin 2,
    γ = QuaternionGroup.a 1 ^ i.val * QuaternionGroup.xa 0 ^ j.val := by decide

theorem q8_le_of_mem {Q H : Subgroup M128} (e : ↥Q ≃* QuaternionGroup 2)
    (hx : ((e.symm (QuaternionGroup.a 1) : ↥Q) : M128) ∈ H)
    (hy : ((e.symm (QuaternionGroup.xa 0) : ↥Q) : M128) ∈ H) : Q ≤ H := by
  intro g hg
  obtain ⟨i, j, hij⟩ := q8_words (e ⟨g, hg⟩)
  have hg' : (⟨g, hg⟩ : ↥Q) = e.symm (QuaternionGroup.a 1) ^ i.val * e.symm (QuaternionGroup.xa 0) ^ j.val := by
    rw [← map_pow, ← map_pow, ← map_mul, ← hij, MulEquiv.symm_apply_apply]
  have := congrArg (fun t : ↥Q => (t : M128)) hg'
  simp only [Subgroup.coe_mul, Subgroup.coe_pow] at this
  rw [this]
  exact H.mul_mem (H.pow_mem hx _) (H.pow_mem hy _)

theorem q8_eq_sub {Q : Subgroup M128} (e : ↥Q ≃* QuaternionGroup 2) (hζ : zeta ∈ Q) :
    ∃ i : Fin 6, Q = q8sub i := by
  obtain ⟨r1, r2, r3⟩ := q8_gen_rels e hζ
  obtain ⟨i, hxi, hyi⟩ := q8_cases _ r1 _ r2 r3
  refine ⟨i, ?_⟩
  have hle : Q ≤ q8sub i := q8_le_of_mem e hxi hyi
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_q8sub, Nat.card_congr e.toEquiv, card_quaternionGroup_two]

theorem q8_pair_unique {Q₁ Q₂ Q₁' Q₂' : Subgroup M128}
    (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    (e₁' : ↥Q₁' ≃* QuaternionGroup 2) (e₂' : ↥Q₂' ≃* QuaternionGroup 2)
    (hζ₁ : zeta ∈ Q₁) (hζ₂ : zeta ∈ Q₂) (hζ₁' : zeta ∈ Q₁') (hζ₂' : zeta ∈ Q₂')
    (hc : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hc' : ∀ a ∈ Q₁', ∀ b ∈ Q₂', a * b = b * a) :
    (Q₁ = Q₁' ∧ Q₂ = Q₂') ∨ (Q₁ = Q₂' ∧ Q₂ = Q₁') := by
  obtain ⟨i₁, rfl⟩ := q8_eq_sub e₁ hζ₁
  obtain ⟨i₂, rfl⟩ := q8_eq_sub e₂ hζ₂
  obtain ⟨j₁, rfl⟩ := q8_eq_sub e₁' hζ₁'
  obtain ⟨j₂, rfl⟩ := q8_eq_sub e₂' hζ₂'
  have key : ∀ i j : Fin 6, (∀ a ∈ q8sub i, ∀ b ∈ q8sub j, a * b = b * a) →
      (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
    intro i j h
    rcases q8_noncomm i j with h1 | h1 | ⟨a, ha, b, hb, hne⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (h a ha b hb) hne
  rcases key i₁ i₂ hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases key j₁ j₂ hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    subst h1 h2 h3 h4
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem q8_pair_transport {S S' : Type*} [Group S] [Group S'] (g : M128 ≃* S) (α : S ≃* S')
    (Q₁ Q₂ : Subgroup S) (Q₁' Q₂' : Subgroup S')
    (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    (e₁' : ↥Q₁' ≃* QuaternionGroup 2) (e₂' : ↥Q₂' ≃* QuaternionGroup 2)
    (hc : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hc' : ∀ a ∈ Q₁', ∀ b ∈ Q₂', a * b = b * a)
    (z : S) (hz1 : z ≠ 1) (hzc : ∀ s, s * z = z * s) (hz₁ : z ∈ Q₁) (hz₂ : z ∈ Q₂)
    (z' : S') (hz1' : z' ≠ 1) (hzc' : ∀ s, s * z' = z' * s) (hz₁' : z' ∈ Q₁') (hz₂' : z' ∈ Q₂') :
    ((∀ x : S, x ∈ Q₁ ↔ α x ∈ Q₁') ∧ (∀ x : S, x ∈ Q₂ ↔ α x ∈ Q₂')) ∨
      ((∀ x : S, x ∈ Q₁ ↔ α x ∈ Q₂') ∧ (∀ x : S, x ∈ Q₂ ↔ α x ∈ Q₁')) := by
  let h : M128 ≃* S' := g.trans α
  have hzeta : g.symm z = zeta := by
    have hc1 : ∀ y : M128, g.symm z * y = y * g.symm z := fun y => by
      have := hzc (g y)
      apply g.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact this.symm
    rcases center_M128 _ hc1 with h1 | h1
    · exact absurd (g.symm.injective (by rw [h1, map_one])) hz1
    · exact h1
  have hzeta' : h.symm z' = zeta := by
    have hc1 : ∀ y : M128, h.symm z' * y = y * h.symm z' := fun y => by
      have := hzc' (h y)
      apply h.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact this.symm
    rcases center_M128 _ hc1 with h1 | h1
    · exact absurd (h.symm.injective (by rw [h1, map_one])) hz1'
    · exact h1
  let R₁ : Subgroup M128 := Q₁.map g.symm.toMonoidHom
  let R₂ : Subgroup M128 := Q₂.map g.symm.toMonoidHom
  let R₁' : Subgroup M128 := Q₁'.map h.symm.toMonoidHom
  let R₂' : Subgroup M128 := Q₂'.map h.symm.toMonoidHom
  have memR : ∀ (K : Subgroup S) (x : M128), x ∈ K.map g.symm.toMonoidHom ↔ g x ∈ K := fun K x => by
    rw [Subgroup.mem_map_equiv]; rfl
  have memR' : ∀ (K : Subgroup S') (x : M128), x ∈ K.map h.symm.toMonoidHom ↔ h x ∈ K := fun K x => by
    rw [Subgroup.mem_map_equiv]; rfl
  have key := q8_pair_unique (Q₁ := R₁) (Q₂ := R₂) (Q₁' := R₁') (Q₂' := R₂')
    ((g.symm.subgroupMap Q₁).symm.trans e₁) ((g.symm.subgroupMap Q₂).symm.trans e₂)
    ((h.symm.subgroupMap Q₁').symm.trans e₁') ((h.symm.subgroupMap Q₂').symm.trans e₂')
    ((memR Q₁ zeta).2 (by rw [← hzeta]; simpa using hz₁))
    ((memR Q₂ zeta).2 (by rw [← hzeta]; simpa using hz₂))
    ((memR' Q₁' zeta).2 (by rw [← hzeta']; simpa using hz₁'))
    ((memR' Q₂' zeta).2 (by rw [← hzeta']; simpa using hz₂'))
    (fun a ha b hb => by
      rw [memR] at ha hb
      apply g.injective
      simp only [map_mul]
      exact hc _ ha _ hb)
    (fun a ha b hb => by
      rw [memR'] at ha hb
      apply h.injective
      simp only [map_mul]
      exact hc' _ ha _ hb)
  have conv : ∀ (K : Subgroup S) (K' : Subgroup S'), K.map g.symm.toMonoidHom = K'.map h.symm.toMonoidHom →
      ∀ x : S, x ∈ K ↔ α x ∈ K' := by
    intro K K' hK x
    have h1 : g.symm x ∈ K.map g.symm.toMonoidHom ↔ g.symm x ∈ K'.map h.symm.toMonoidHom := by rw [hK]
    rw [memR, memR'] at h1
    have e1 : g (g.symm x) = x := MulEquiv.apply_symm_apply g x
    have e2 : h (g.symm x) = α x := by
      show α (g (g.symm x)) = α x
      rw [e1]
    rw [e1, e2] at h1
    exact h1
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact Or.inl ⟨conv _ _ k1, conv _ _ k2⟩
  · exact Or.inr ⟨conv _ _ k1, conv _ _ k2⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
