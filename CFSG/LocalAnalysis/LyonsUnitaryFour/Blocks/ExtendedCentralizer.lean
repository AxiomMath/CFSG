module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.PrimaryParts
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula

public section

namespace CFSG.LyonsUnitaryFour

open scoped Classical

theorem conj_eq_self_iff_mul_comm {G : Type*} [Group G] (x g : G) :
    g⁻¹ * x * g = x ↔ g * x = x * g := by
  constructor
  · intro h
    calc g * x = g * (g⁻¹ * x * g) := by rw [h]
      _ = x * g := by group
  · intro h
    rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_inv_of_conj_eq_inv {G : Type*} [Group G] {x g : G} (h : g⁻¹ * x * g = x⁻¹) :
    g * x * g⁻¹ = x⁻¹ := by
  have h' : g⁻¹ * x⁻¹ * g = x := by
    rw [show g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ by group, h, inv_inv]
  calc g * x * g⁻¹ = g * (g⁻¹ * x⁻¹ * g) * g⁻¹ := by rw [h']
    _ = x⁻¹ := by group

@[expose] def extendedCentralizer {G : Type*} [Group G] (x : G) : Subgroup G where
  carrier := {g | g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x⁻¹}
  one_mem' := Or.inl (by group)
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    have hconj : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
    have hinvconj : h⁻¹ * x⁻¹ * h = (h⁻¹ * x * h)⁻¹ := by group
    rcases hg with hg | hg
    · rw [hconj, hg]
      exact hh
    · rw [hconj, hg, hinvconj]
      rcases hh with hh | hh
      · right
        rw [hh]
      · left
        rw [hh, inv_inv]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [inv_inv]
    rcases hg with hg | hg
    · left
      calc g * x * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hg]
        _ = x := by group
    · right
      exact conj_inv_of_conj_eq_inv hg

theorem mem_extendedCentralizer {G : Type*} [Group G] (x g : G) :
    g ∈ extendedCentralizer x ↔ g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x⁻¹ := Iff.rfl

theorem centralizer_le_extendedCentralizer {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer {x} ≤ extendedCentralizer x := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  exact Or.inl ((conj_eq_self_iff_mul_comm x g).mpr hg)

theorem extendedCentralizer_inv_mul_mem {G : Type*} [Group G] (x g g' : G)
    (hg : g⁻¹ * x * g = x⁻¹) (hg' : g'⁻¹ * x * g' = x⁻¹) :
    g⁻¹ * g' ∈ Subgroup.centralizer {x} := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← conj_eq_self_iff_mul_comm]
  have h1 : g * x⁻¹ * g⁻¹ = x := by
    have := conj_inv_of_conj_eq_inv hg
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = x := by rw [this, inv_inv]
  calc (g⁻¹ * g')⁻¹ * x * (g⁻¹ * g') = g'⁻¹ * (g * x⁻¹ * g⁻¹)⁻¹ * g' := by group
    _ = g'⁻¹ * x⁻¹ * g' := by rw [h1]
    _ = (g'⁻¹ * x * g')⁻¹ := by group
    _ = x := by rw [hg', inv_inv]

theorem conj_eq_of_inv_mul_mem_centralizer {G : Type*} [Group G] (x g g' : G)
    (hg : g ∈ extendedCentralizer x) (hc : g⁻¹ * g' ∈ Subgroup.centralizer {x}) :
    g'⁻¹ * x * g' = g⁻¹ * x * g := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← conj_eq_self_iff_mul_comm] at hc
  have hcinv : (g⁻¹ * g')⁻¹ * x⁻¹ * (g⁻¹ * g') = x⁻¹ := by
    rw [show (g⁻¹ * g')⁻¹ * x⁻¹ * (g⁻¹ * g') = ((g⁻¹ * g')⁻¹ * x * (g⁻¹ * g'))⁻¹ by group, hc]
  have hsplit : g'⁻¹ * x * g' = (g⁻¹ * g')⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * g') := by group
  rcases hg with hg | hg
  · rw [hsplit, hg, hc]
  · rw [hsplit, hg, hcinv]

theorem relIndex_centralizer_extendedCentralizer_le_two {G : Type*} [Group G] (x : G) :
    (Subgroup.centralizer {x}).relIndex (extendedCentralizer x) ≤ 2 := by
  classical
  set E := extendedCentralizer x
  set C' := (Subgroup.centralizer {x}).subgroupOf E
  let f : E ⧸ C' → Bool := Quotient.lift (fun g : E => decide ((g : G)⁻¹ * x * g = x)) (by
    intro g g' hgg'
    have hc : (g⁻¹ * g' : E) ∈ C' := QuotientGroup.leftRel_apply.mp hgg'
    have hc' : (g : G)⁻¹ * g' ∈ Subgroup.centralizer {x} := hc
    have heq := conj_eq_of_inv_mul_mem_centralizer x g g' g.property hc'
    simp only [heq])
  have hinj : Function.Injective f := by
    intro q q' hqq'
    induction q using QuotientGroup.induction_on with
    | H g =>
    induction q' using QuotientGroup.induction_on with
    | H g' =>
    apply QuotientGroup.eq.mpr
    change (g : G)⁻¹ * (g' : G) ∈ Subgroup.centralizer {x}
    have hval : decide ((g : G)⁻¹ * x * g = x) = decide ((g' : G)⁻¹ * x * g' = x) := hqq'
    obtain ⟨a, ha⟩ := g
    obtain ⟨a', ha'⟩ := g'
    dsimp only at hval ⊢
    rw [mem_extendedCentralizer] at ha ha'
    by_cases hax : a⁻¹ * x * a = x
    · have ha'x : a'⁻¹ * x * a' = x := by
        have : decide (a'⁻¹ * x * a' = x) = true := by rw [← hval]; exact decide_eq_true hax
        exact of_decide_eq_true this
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : a * x = x * a := (conj_eq_self_iff_mul_comm x a).mp hax
      have h2 : a' * x = x * a' := (conj_eq_self_iff_mul_comm x a').mp ha'x
      calc a⁻¹ * a' * x = a⁻¹ * (x * a') := by rw [mul_assoc, h2]
        _ = a⁻¹ * (x * a) * (a⁻¹ * a') := by group
        _ = a⁻¹ * (a * x) * (a⁻¹ * a') := by rw [h1]
        _ = x * (a⁻¹ * a') := by group
    · have ha'x : ¬ a'⁻¹ * x * a' = x := by
        intro h
        have : decide (a⁻¹ * x * a = x) = true := by rw [hval]; exact decide_eq_true h
        exact hax (of_decide_eq_true this)
      exact extendedCentralizer_inv_mul_mem x a a' (ha.resolve_left hax) (ha'.resolve_left ha'x)
  calc (Subgroup.centralizer {x}).relIndex E = Nat.card (E ⧸ C') := by
        rw [Subgroup.relIndex, Subgroup.index]
    _ ≤ Nat.card Bool := Nat.card_le_card_of_injective f hinj
    _ = 2 := by simp

theorem involution_product_inverted {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) :
    a⁻¹ * (a * b) * a = (a * b)⁻¹ ∧ b⁻¹ * (a * b) * b = (a * b)⁻¹ := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  constructor
  · rw [hainv, mul_inv_rev, hainv, hbinv, ← mul_assoc, ha, one_mul]
  · rw [hbinv, mul_inv_rev, hainv, hbinv, mul_assoc, mul_assoc, hb, mul_one]

theorem involution_product_extended_centralizer_localization {G : Type*} [Group G]
    [DecidableEq G] (x : G) (A B : Finset G) (hAinv : ∀ a ∈ A, a * a = 1)
    (hBinv : ∀ b ∈ B, b * b = 1) :
    Subgroup.centralizer {x} ≤ extendedCentralizer x ∧
    (Subgroup.centralizer {x}).relIndex (extendedCentralizer x) ≤ 2 ∧
    (∀ a ∈ A, ∀ b ∈ B, a * b = x →
      a⁻¹ * x * a = x⁻¹ ∧ b⁻¹ * x * b = x⁻¹ ∧ a ∈ extendedCentralizer x ∧
        b ∈ extendedCentralizer x) ∧
    ((∀ a ∈ A, a⁻¹ * x * a ≠ x⁻¹) → productCount A B x = 0) ∧
    (∀ H : Subgroup G, extendedCentralizer x ≤ H →
      productCount A B x = productCount (A.filter (· ∈ H)) (B.filter (· ∈ H)) x) ∧
    (∀ (p : ℕ) (u r : G) (e : ℕ), orderOf u ∣ p ^ e → Commute u r →
      Nat.Coprime p (orderOf r) → extendedCentralizer (u * r) ≤ extendedCentralizer u) := by
  have hpairs : ∀ a ∈ A, ∀ b ∈ B, a * b = x →
      a⁻¹ * x * a = x⁻¹ ∧ b⁻¹ * x * b = x⁻¹ ∧ a ∈ extendedCentralizer x ∧
        b ∈ extendedCentralizer x := by
    rintro a ha b hb rfl
    obtain ⟨h1, h2⟩ := involution_product_inverted (hAinv a ha) (hBinv b hb)
    exact ⟨h1, h2, Or.inr h1, Or.inr h2⟩
  refine ⟨centralizer_le_extendedCentralizer x, relIndex_centralizer_extendedCentralizer_le_two x,
    hpairs, ?_, ?_, ?_⟩
  · intro hnot
    unfold productCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨a, b⟩ hab hprod
    rw [Finset.mem_product] at hab
    exact hnot a hab.1 (hpairs a hab.1 b hab.2 hprod).1
  · intro H hH
    unfold productCount
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨ha, hb⟩, hprod⟩
      obtain ⟨-, -, haE, hbE⟩ := hpairs a ha b hb hprod
      exact ⟨⟨⟨ha, hH haE⟩, ⟨hb, hH hbE⟩⟩, hprod⟩
    · rintro ⟨⟨⟨ha, -⟩, ⟨hb, -⟩⟩, hprod⟩
      exact ⟨⟨ha, hb⟩, hprod⟩
  · intro p u r e hu hur hr g hg
    have hcop : Nat.Coprime (orderOf u) (orderOf r) := (hr.pow_left e).of_dvd_left hu
    obtain ⟨k, hk⟩ := CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors
      (rfl : u * r = u * r) hur hcop
    rw [mem_extendedCentralizer] at hg ⊢
    have hpow : ∀ y : G, g⁻¹ * y ^ k * g = (g⁻¹ * y * g) ^ k := by
      intro y
      have h := conj_pow (a := g⁻¹) (b := y) (i := k)
      rw [inv_inv] at h
      exact h.symm
    rcases hg with hg | hg
    · left
      rw [← hk, hpow, hg]
    · right
      rw [← hk, hpow, hg, inv_pow]

end CFSG.LyonsUnitaryFour
