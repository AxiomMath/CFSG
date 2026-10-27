module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerAverage

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_mem_ne_ne_of_three_le_card [Finite G] {U : Subgroup G} (hU : 3 ≤ Nat.card U)
    (a b : G) : ∃ x ∈ U, x ≠ a ∧ x ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (U : Set G) ⊆ {a, b} := fun x hx => by
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hcon x hx hxa)
  have h1 : Nat.card (U : Set G) ≤ Nat.card ({a, b} : Set G) := Nat.card_mono (Set.toFinite _) hsub
  have h2 : Nat.card ({a, b} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])
  have h3 : Nat.card (U : Set G) = Nat.card U := rfl
  omega

theorem sup_commutator_complement [Finite G] {Q U A C : Subgroup G} {u : G}
    (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ U)
    (huQ : u ∈ Q) (huU : u ∉ U) (hu : u * u = 1)
    (hθ : ∀ x ∈ Q, involutionDisplacement u x ∈ U)
    (hθsurj : ∀ b ∈ U, ∃ x ∈ Q, involutionDisplacement u x = b)
    (hE : ∀ x ∈ Q, x * u = u * x → x ∈ U ∨ u * x ∈ U)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hAu : A ≤ Subgroup.centralizer ({u} : Set G))
    (hCA : C ≤ A) (hAC : A ≤ Subgroup.normalizer (C : Set G)) (hCodd : Odd (Nat.card C))
    (hCtr : ∀ b ∈ U, b ≠ 1 → ∀ b' ∈ U, b' ≠ 1 → ∃ c ∈ C, c * b * c⁻¹ = b')
    (hU3 : 3 ≤ Nat.card U) :
    U ⊔ ⁅A, Q⁆ ≤ Q ∧ A ≤ Subgroup.normalizer ((U ⊔ ⁅A, Q⁆ : Subgroup G) : Set G) ∧
      Q ≤ Subgroup.normalizer ((U ⊔ ⁅A, Q⁆ : Subgroup G) : Set G) ∧ u ∉ U ⊔ ⁅A, Q⁆ ∧
      (∀ x ∈ U ⊔ ⁅A, Q⁆, x * u = u * x → x ∈ U) ∧
      (∀ b ∈ U, ∃ x ∈ U ⊔ ⁅A, Q⁆, involutionDisplacement u x = b) ∧
      Nat.card (U ⊔ ⁅A, Q⁆ : Subgroup G) = Nat.card U ^ 2 ∧
      (∀ x ∈ U ⊔ ⁅A, Q⁆, x ∉ U → ∀ y ∈ U ⊔ ⁅A, Q⁆, y ∉ U →
        ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U) ∧
      Subgroup.zpowers u ⊔ (U ⊔ ⁅A, Q⁆) = Q := by
  set V := U ⊔ ⁅A, Q⁆ with hV
  have hcommQ : ⁅A, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAQ ha) x).mp hx) (Q.inv_mem hx)
  have hVQ : V ≤ Q := sup_le hUQ hcommQ
  have hUV : U ≤ V := le_sup_left
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_sup U ⁅A, Q⁆
      ⟨hAU ha, le_normalizer_commutator A Q ha⟩
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
      rw [h]
      exact V.mul_mem (hUV (hQcomm x hx v (hVQ hv))) hv
    · intro hw
      have hwQ : x * v * x⁻¹ ∈ Q := hVQ hw
      have h : v = (x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ * (x * v * x⁻¹)⁻¹) * (x * v * x⁻¹) := by group
      rw [h]
      exact V.mul_mem (hUV (hQcomm _ (Q.inv_mem hx) _ hwQ)) hw
  have hCfix : ∀ b ∈ U, (∀ c ∈ C, c * b * c⁻¹ = b) → b = 1 := by
    intro b hb hfix
    by_contra hb1
    obtain ⟨b', hb', hb'1, hb'b⟩ := exists_mem_ne_ne_of_three_le_card hU3 1 b
    obtain ⟨c, hc, hcb⟩ := hCtr b hb hb1 b' hb' hb'1
    exact hb'b (hcb.symm.trans (hfix c hc))
  have huV : u ∉ V := not_mem_sup_commutator_of_odd_normal hUQ hQU hQcomm huQ huU hu hθ hE hAQ
    hAU hAu hCA hAC hCodd hCfix
  have hVE : ∀ x ∈ V, x * u = u * x → x ∈ U := by
    intro x hx hxu
    rcases hE x (hVQ hx) hxu with h | h
    · exact h
    · exfalso
      apply huV
      have h' : u = (u * x) * x⁻¹ := by group
      rw [h']
      exact V.mul_mem (hUV h) (V.inv_mem hx)
  have hθmul : ∀ x ∈ Q, ∀ y ∈ Q, involutionDisplacement u (x * y) =
      involutionDisplacement u x * involutionDisplacement u y := fun x hx y hy =>
    involutionDisplacement_mul hu (hQU hx) (hθ y hy)
  have hθone : involutionDisplacement u 1 = 1 := by
    simp [involutionDisplacement, hu]
  have hθinv : ∀ x ∈ Q, involutionDisplacement u x⁻¹ = (involutionDisplacement u x)⁻¹ := by
    intro x hx
    have h := hθmul x⁻¹ (Q.inv_mem hx) x hx
    rw [inv_mul_cancel, hθone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hθconj : ∀ a ∈ A, ∀ x : G, involutionDisplacement u (a * x * a⁻¹) =
      a * involutionDisplacement u x * a⁻¹ := fun a ha x =>
    involutionDisplacement_conj (Subgroup.mem_centralizer_singleton_iff.mp (hAu ha)) x
  have hconjQ : ∀ a ∈ A, ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAQ ha) x).mp hx
  have hconjV : ∀ a ∈ A, ∀ x ∈ V, a * x * a⁻¹ ∈ V := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAV ha) x).mp hx
  have hθV : ∀ b ∈ U, ∃ x ∈ V, involutionDisplacement u x = b := by
    obtain ⟨b₁, hb₁, hb₁1, -⟩ := exists_mem_ne_ne_of_three_le_card hU3 1 1
    obtain ⟨b₂, hb₂, hb₂1, hb₂b₁⟩ := exists_mem_ne_ne_of_three_le_card hU3 1 b₁
    obtain ⟨c, hc, hcb⟩ := hCtr b₁ hb₁ hb₁1 b₂ hb₂ hb₂1
    obtain ⟨x, hx, hxb⟩ := hθsurj b₁ hb₁
    have hv : ⁅c, x⁆ ∈ V := le_sup_right (a := U) (Subgroup.commutator_mem_commutator (hCA hc) hx)
    have hθv : involutionDisplacement u ⁅c, x⁆ = b₂ * b₁⁻¹ := by
      rw [commutatorElement_def, hθmul _ (hconjQ c (hCA hc) x hx) _ (Q.inv_mem hx),
        hθconj c (hCA hc), hθinv x hx, hxb, hcb]
    have hb0 : b₂ * b₁⁻¹ ≠ 1 := fun h => hb₂b₁ (mul_inv_eq_one.mp h)
    have hb0U : b₂ * b₁⁻¹ ∈ U := U.mul_mem hb₂ (U.inv_mem hb₁)
    intro b hb
    by_cases hb1 : b = 1
    · exact ⟨1, V.one_mem, by rw [hb1, hθone]⟩
    · obtain ⟨c', hc', hc'b⟩ := hCtr _ hb0U hb0 b hb hb1
      exact ⟨c' * ⁅c, x⁆ * c'⁻¹, hconjV c' (hCA hc') _ hv, by
        rw [hθconj c' (hCA hc'), hθv, hc'b]⟩
  let θV : V →* U :=
    { toFun := fun x => ⟨involutionDisplacement u x, hθ x (hVQ x.2)⟩
      map_one' := Subtype.ext hθone
      map_mul' := fun x y => Subtype.ext (hθmul x (hVQ x.2) y (hVQ y.2)) }
  have hθVsurj : Function.Surjective θV := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hx, hxb⟩ := hθV b hb
    exact ⟨⟨x, hx⟩, Subtype.ext hxb⟩
  have hker : θV.ker = U.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (⟨involutionDisplacement u x, _⟩ : U) = 1 ↔ _
    rw [← Subtype.coe_inj, OneMemClass.coe_one, involutionDisplacement_eq_one_iff hu]
    refine ⟨hVE x x.2, fun hx => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp (hQU huQ) x hx
  have hVcard : Nat.card V = Nat.card U ^ 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θV.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θV hθVsurj).toEquiv, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv, pow_two]
  have htrans : ∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U := by
    intro x hx hxU y hy hyU
    have hθx : involutionDisplacement u x ≠ 1 := fun h =>
      hxU (hVE x hx ((involutionDisplacement_eq_one_iff hu x).mp h))
    have hθy : involutionDisplacement u y ≠ 1 := fun h =>
      hyU (hVE y hy ((involutionDisplacement_eq_one_iff hu y).mp h))
    obtain ⟨c, hc, hcb⟩ := hCtr _ (hθ x (hVQ hx)) hθx _ (hθ y (hVQ hy)) hθy
    refine ⟨c, hCA hc, hVE _ (V.mul_mem (V.inv_mem hy) (hconjV c (hCA hc) x hx)) ?_⟩
    rw [← involutionDisplacement_eq_one_iff hu,
      hθmul _ (Q.inv_mem (hVQ hy)) _ (hconjQ c (hCA hc) x (hVQ hx)), hθinv y (hVQ hy),
      hθconj c (hCA hc), hcb, inv_mul_cancel]
  have hQeq : Subgroup.zpowers u ⊔ V = Q := by
    apply le_antisymm (sup_le (Subgroup.zpowers_le.mpr huQ) hVQ)
    intro x hx
    obtain ⟨v, hv, hvx⟩ := hθV _ (hθ x hx)
    have hw : v⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hVQ hv)) hx
    have hθw : involutionDisplacement u (v⁻¹ * x) = 1 := by
      rw [hθmul _ (Q.inv_mem (hVQ hv)) _ hx, hθinv v (hVQ hv), hvx, inv_mul_cancel]
    have hwu := (involutionDisplacement_eq_one_iff hu _).mp hθw
    have hxe : x = v * (v⁻¹ * x) := by group
    rw [hxe]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hv) ?_
    rcases hE _ hw hwu with h | h
    · exact Subgroup.mem_sup_right (hUV h)
    · have h' : v⁻¹ * x = u⁻¹ * (u * (v⁻¹ * x)) := by group
      rw [h']
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)))
        (Subgroup.mem_sup_right (hUV h))
  exact ⟨hVQ, hAV, hQV, huV, hVE, hθV, hVcard, htrans, hQeq⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
