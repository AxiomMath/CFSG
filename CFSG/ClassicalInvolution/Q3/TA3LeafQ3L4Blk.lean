module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Gen
public import CFSG.LieType.HighestRoot.CentChevalleySLThree

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3L4

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] {P : Type} [Group P]

theorem range_le_closure (hF : Fintype.card F = 3) (β : SL(2, F) × SL(2, F) →* P) :
    β.range ≤ Subgroup.closure {x : P | x ∈ β.range ∧ x ^ 3 = 1} := by
  have hK : Nat.card F = 3 := by rw [Nat.card_eq_fintype_card, hF]
  have key : ∀ φ : SL(2, F) →* P, (∀ c, φ c ∈ β.range) →
      ∀ c, φ c ∈ Subgroup.closure {x : P | x ∈ β.range ∧ x ^ 3 = 1} := by
    intro φ hφ c
    have hc : c ∈ Subgroup.closure {x : SL(2, F) | orderOf x = 3} := by
      rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top hK]
      exact Subgroup.mem_top c
    have hm := Subgroup.mem_map_of_mem φ hc
    rw [MonoidHom.map_closure] at hm
    refine (Subgroup.closure_mono ?_) hm
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hφ y, by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have e : β (a, b) = β (a, 1) * β (1, b) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e]
  exact mul_mem (key (β.comp (MonoidHom.inl _ _)) (fun _ => ⟨_, rfl⟩) a)
    (key (β.comp (MonoidHom.inr _ _)) (fun _ => ⟨_, rfl⟩) b)

variable (hF : Fintype.card F = 3) (β : SL(2, F) × SL(2, F) →* P)
  (hker : ∀ a b, β (a, b) = 1 ↔ (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1)) {u w : P}
  (hβu : β (-1, 1) = u) (hw : ∀ a b, w * β (a, b) * w⁻¹ = β (b, a))

include hF hker hβu in
theorem u_ne_one : u ≠ 1 := by
  rw [← hβu]
  intro h
  rcases (hker _ _).1 h with ⟨h1, -⟩ | ⟨-, h1⟩
  · exact neg_one_ne_one hF h1
  · exact neg_one_ne_one hF h1.symm

omit [Fintype F] in
include hβu in
theorem u_mul_u : u * u = 1 := by
  rw [← hβu, ← map_mul, Prod.mk_mul_mk, neg_mul_neg, one_mul]
  exact map_one β

omit [Fintype F] in
include hβu in
theorem u_comm {x : P} (hx : x ∈ β.range) : x * u = u * x := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  rw [← hβu, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_neg_one, neg_one_mul,
    mul_one, one_mul]

include hF hker hβu hw in
theorem mem_pair_of_mem {R' : Subgroup P} (hRw : ∀ x ∈ R', w * x * w⁻¹ ∈ R')
    (hinv : ∀ x ∈ R', x * x = 1 → x = 1 ∨ x = u)
    (h3 : ∀ x ∈ R', x ∈ β.range → x ^ 3 = 1 → x = 1) :
    ∀ x ∈ R', x ∈ β.range → x = 1 ∨ x = u := by
  have h11 : β (-1, -1) = 1 := (hker _ _).2 (Or.inr ⟨rfl, rfl⟩)
  have key : ∀ a : SL(2, F), a ^ 2 = -1 → β (a, 1) ∉ R' := by
    intro a ha hx
    obtain ⟨ha1, ha2⟩ := ne_one_and_ne_neg_one_of_sq hF ha
    have hy : β (1, a) ∈ R' := by
      rw [← hw]
      exact hRw _ hx
    have hz := mul_mem hx hy
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] at hz
    have hz2 : β (a, a) * β (a, a) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, ← sq, ha, h11]
    rcases hinv _ hz hz2 with h1 | h1
    · rcases (hker a a).1 h1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact ha1 h
      · exact ha2 h
    · have e : β (a, a) * β (-1, 1) = 1 := by rw [h1, ← hβu]; exact u_mul_u β rfl
      rw [← map_mul, Prod.mk_mul_mk, mul_neg_one, mul_one] at e
      rcases (hker _ _).1 e with ⟨-, h⟩ | ⟨-, h⟩
      · exact ha1 h
      · exact ha2 h
  have key' : ∀ a c : SL(2, F), a ^ 2 = -1 → c ^ 2 = 1 → β (a, c) ∉ R' := by
    intro a c ha hc hx
    rcases eq_one_or_neg_one_of_sq hF hc with rfl | rfl
    · exact key a ha hx
    · have e : β (a, -1) = β (-a, 1) := by
        calc β (a, -1) = β (a, -1) * β (-1, -1) := by rw [h11, mul_one]
          _ = β (-a, 1) := by rw [← map_mul, Prod.mk_mul_mk, mul_neg_one, neg_mul_neg, one_mul]
      rw [e] at hx
      exact key (-a) (by rw [neg_sq, ha]) hx
  intro x hx hxH
  obtain ⟨⟨a, b⟩, rfl⟩ := hxH
  have h12 : (β (a, b) ^ 4) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, Prod.pow_mk, Prod.pow_mk, pow_twelve hF a, pow_twelve hF b]
    exact map_one β
  have h4 : β (a, b) ^ 4 = 1 := h3 _ (pow_mem hx 4) ⟨(a, b) ^ 4, map_pow β _ 4⟩ h12
  have hx2 : β (a, b) ^ 2 * β (a, b) ^ 2 = 1 := by
    rw [← pow_add]
    exact h4
  rcases hinv _ (pow_mem hx 2) hx2 with h2 | h2
  · exact hinv _ hx (by rw [← sq]; exact h2)
  · exfalso
    have e : β (a ^ 2, b ^ 2) * β (-1, 1) = 1 := by
      rw [← Prod.pow_mk, map_pow, h2, ← hβu]
      exact u_mul_u β rfl
    rw [← map_mul, Prod.mk_mul_mk, mul_neg_one, mul_one] at e
    rcases (hker _ _).1 e with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact key' a b (neg_eq_iff_eq_neg.mp ha) hb hx
    · have ha' : a ^ 2 = 1 := neg_inj.mp ha
      have hx' := hRw _ hx
      rw [hw] at hx'
      exact key' b a hb ha' hx'

include hF hker hβu hw in
theorem le_pair_of_normal (hwu : w * u = u * w)
    (hnorm : ∀ g : P, g * u = u * g → ∀ x ∈ β.range, g * x * g⁻¹ ∈ β.range)
    (hcent : ∀ g : P, (∀ x ∈ β.range, g * x = x * g) → g = 1 ∨ g = u)
    {R' : Subgroup P} (hRu : ∀ x ∈ R', x * u = u * x)
    (hRn : ∀ g : P, g * u = u * g → ∀ x ∈ R', g * x * g⁻¹ ∈ R')
    (hinv : ∀ x ∈ R', x * x = 1 → x = 1 ∨ x = u)
    (h3 : ∀ x ∈ R', x ∈ β.range → x ^ 3 = 1 → x = 1) :
    ∀ x ∈ R', x = 1 ∨ x = u := by
  have hRH := mem_pair_of_mem hF β hker hβu hw (hRn w hwu) hinv h3
  have hu1 := u_ne_one hF β hker hβu
  have huu := u_mul_u β hβu
  have hZ : ∀ z ∈ Subgroup.zpowers u, z = 1 ∨ z = u := fun z hz =>
    eq_one_or_eq_of_mem_zpowers huu hz
  intro g hg
  apply hcent
  intro x hx
  refine commute_of_commutator_mem (X := {x : P | x ∈ β.range ∧ x ^ 3 = 1})
    (Z := Subgroup.zpowers u) (n := 3) (fun y hy => hy.2) (fun z hz hz3 => ?_)
    (fun z hz y hy => ?_) (fun y hy => ?_) x (range_le_closure hF β hx)
  · rcases hZ z hz with rfl | rfl
    · rfl
    · exfalso
      apply hu1
      rw [pow_succ, sq, huu, one_mul] at hz3
      exact hz3
  · rcases hZ z hz with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (u_comm β hβu hy.1).symm
  · have hyu : y * u = u * y := u_comm β hβu hy.1
    have hcR : g * y * g⁻¹ * y⁻¹ ∈ R' := by
      have h1 := hRn y hyu g⁻¹ (inv_mem hg)
      have h2 := mul_mem hg h1
      rwa [show g * (y * g⁻¹ * y⁻¹) = g * y * g⁻¹ * y⁻¹ by group] at h2
    have hcH : g * y * g⁻¹ * y⁻¹ ∈ β.range :=
      mul_mem (hnorm g (hRu g hg) y hy.1) (inv_mem hy.1)
    rcases hRH _ hcR hcH with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers u

end Q3L4

end CFSG.ClassicalInvolution.Q3.TA3
