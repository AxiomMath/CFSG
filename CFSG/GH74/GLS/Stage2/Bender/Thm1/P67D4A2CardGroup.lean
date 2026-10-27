module

public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.GH74.BNPair.Cells
public import CFSG.GH74.BNPair.WeylIso

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

section Generic

variable {X : Type*} [Group X]

theorem cardG_ncard_mul {S T : Set X}
    (h : Set.InjOn (fun p : X × X => p.1 * p.2) (S ×ˢ T)) :
    (S * T).ncard = S.ncard * T.ncard := by
  rw [← Set.image_mul_prod, h.ncard_image, Set.ncard_prod]

theorem cardG_ncard_mul_of_left {S T : Set X}
    (h : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, ∀ b' ∈ T, a * b = a' * b' → a = a') :
    (S * T).ncard = S.ncard * T.ncard := by
  refine cardG_ncard_mul ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨a', b'⟩ ⟨ha', hb'⟩ hab
  have hab' : a * b = a' * b' := hab
  have := h a ha a' ha' b hb b' hb' hab'
  subst this
  simp only [Prod.mk.injEq, true_and]
  exact mul_left_cancel hab'

end Generic

section Cells

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem cardG_card_cell (w : D.Weyl) :
    Nat.card (dc D.B D.N w) = Nat.card D.B * Nat.card (D.UwMinus (D.lift w)) := by
  let f : D.B × D.UwMinusSub (D.lift w) → dc D.B D.N w := fun p =>
    ⟨(p.1 : X) * (D.lift w : X) * (p.2 : X),
      (D.mem_dc_iff_coord (D.lift w) (D.lift_mk w)).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b, u⟩ ⟨b', u'⟩ h
      have h1 : (b : X) * (D.lift w : X) * (u : X) = (b' : X) * (D.lift w : X) * (u' : X) :=
        congrArg Subtype.val h
      have hu : (u : X) = u' := D.coord_unique (D.lift w) b.2 b'.2 u.2 u'.2 h1
      have hu' : u = u' := Subtype.ext hu
      subst hu'
      have hb : (b : X) = b' := mul_right_cancel (mul_right_cancel h1)
      have hb' : b = b' := Subtype.ext hb
      subst hb'
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb, u, hu, rfl⟩ := (D.mem_dc_iff_coord (D.lift w) (D.lift_mk w)).1 hx
      exact ⟨(⟨b, hb⟩, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  rfl

theorem cardG_UwMinus_A {i : ℕ} (hi : i ≤ n) :
    D.UwMinus (D.lift (altWord D.w₁ D.w₂ i)) = chainProd D.root (intList 1 i) :=
  (D.eq30_5_A hi _ (D.lift_mk _)).1

theorem cardG_UwMinus_B {i : ℕ} (hi : i ≤ n) :
    D.UwMinus (D.lift (altWord D.w₂ D.w₁ i)) =
      chainProd D.root (intList ((n : ℤ) - i + 1) n).reverse :=
  (D.eq30_5_B hi _ (D.lift_mk _)).1

theorem cardG_sum_weyl [Fintype D.Weyl] (f : D.Weyl → ℕ) :
    ∑ w : D.Weyl, f w = ∑ i : Fin (n + 1), f (altWord D.w₁ D.w₂ i) +
      ∑ j : Fin (n - 1), f (altWord D.w₂ D.w₁ ((j : ℕ) + 1)) := by
  have hb := D.rank2.dih.altParam'_bijective
  rw [← hb.sum_comp f, Fintype.sum_sum_type]
  simp only [altParam']

variable [Finite X]

theorem cardG_card_eq_sum [Fintype D.Weyl] :
    Nat.card X = ∑ w : D.Weyl, Nat.card (dc D.B D.N w) := by
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv D.bw).symm, Nat.card_sigma]
  refine Finset.sum_congr rfl fun w _ => ?_
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  exact ⟨fun h => h ▸ D.mem_dc_bw x, fun h => D.bw_eq h⟩

theorem cardG_card_eq_mul_sum [Fintype D.Weyl] :
    Nat.card X = Nat.card D.B * ∑ w : D.Weyl, Nat.card (D.UwMinus (D.lift w)) := by
  rw [cardG_card_eq_sum D, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => cardG_card_cell D w

theorem cardG_card_eq_general :
    Nat.card X = Nat.card D.B * (∑ i : Fin (n + 1), Nat.card (chainProd D.root (intList 1 i)) +
      ∑ j : Fin (n - 1), Nat.card
        (chainProd D.root (intList ((n : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ) + 1) n).reverse)) := by
  have : Fintype D.Weyl := Fintype.ofFinite _
  rw [cardG_card_eq_mul_sum D, cardG_sum_weyl D (fun w => Nat.card (D.UwMinus (D.lift w)))]
  congr 2
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [cardG_UwMinus_A D (Nat.lt_succ_iff.1 i.2)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [cardG_UwMinus_B D (i := (j : ℕ) + 1) (by have := j.2; omega)]

end Cells

namespace RGD2

section Local

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem cardG_card_B {n : ℕ} (R : RGD2 n H r₁ r₂ U root) :
    Nat.card (H ⊔ U : Subgroup X) = Nat.card H * Nat.card U := by
  have h1 : Nat.card (H ⊔ U : Subgroup X) = ((H ⊔ U : Subgroup X) : Set X).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, R.coe_sup_HU, cardG_ncard_mul_of_left]
  · rfl
  · intro a ha a' ha' b hb b' hb' hab
    have h2 : a'⁻¹ * a = b' * b⁻¹ :=
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ U ⊓ H :=
      ⟨h2 ▸ U.mul_mem hb' (U.inv_mem hb), H.mul_mem (H.inv_mem ha') ha⟩
    rw [R.U_inf_H, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm

theorem cardG_unique3 (R : RGD2 3 H r₁ r₂ U root) {a a' b b' c c' : X}
    (ha : a ∈ root 1) (ha' : a' ∈ root 1) (hb : b ∈ root 2) (hb' : b' ∈ root 2)
    (hc : c ∈ root 3) (hc' : c' ∈ root 3) (h : a * (b * c) = a' * (b' * c')) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hl : intList 1 ((3 : ℕ) : ℤ) = [1, 2, 3] := by decide
  have key := R.unique (fun k => if k = 1 then a else if k = 2 then b else c)
    (fun k => if k = 1 then a' else if k = 2 then b' else c') ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · simpa using key 1 (by rw [hl]; simp)
    · simpa using key 2 (by rw [hl]; simp)
    · simpa using key 3 (by rw [hl]; simp)
  · intro k hk
    rw [hl] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simpa
  · intro k hk
    rw [hl] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simpa
  · rw [hl]
    simpa using h

theorem cardG_card_chain_nil : Nat.card (chainProd root ([] : List ℤ)) = 1 := by
  have : chainProd root ([] : List ℤ) = {1} := by
    simp [chainProd, Set.singleton_one]
  rw [this]
  simp

theorem cardG_card_chain_one {q : ℕ} (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card (root k) = q)
    {k : ℤ} (hk : IsRoot 3 k) : Nat.card (chainProd root [k]) = q := by
  rw [chainProd_singleton]
  exact hroot k hk

theorem cardG_card_chain_12 (R : RGD2 3 H r₁ r₂ U root) {q : ℕ}
    (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card (root k) = q) :
    Nat.card (chainProd root [1, 2]) = q ^ 2 := by
  have h1 : IsRoot 3 1 := ⟨by decide, by decide⟩
  have h2 : IsRoot 3 2 := ⟨by decide, by decide⟩
  rw [Nat.card_coe_set_eq, chainProd_cons, chainProd_singleton,
    cardG_ncard_mul_of_left, pow_two]
  · exact congrArg₂ (· * ·) (hroot 1 h1) (hroot 2 h2)
  · intro a ha a' ha' b hb b' hb' hab
    have := R.cardG_unique3 (c := 1) (c' := 1) ha ha' hb hb' (root 3).one_mem (root 3).one_mem
      (by simpa using hab)
    exact this.1

theorem cardG_card_chain_U (R : RGD2 3 H r₁ r₂ U root) {q : ℕ} (hU : Nat.card U = q ^ 3) :
    Nat.card (chainProd root (intList 1 ((3 : ℕ) : ℤ))) = q ^ 3 := by
  rw [← R.carrier_eq]
  exact hU

theorem cardG_card_chain_32 (R : RGD2 3 H r₁ r₂ U root) {q : ℕ}
    (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card (root k) = q) :
    Nat.card (chainProd root [3, 2]) = q ^ 2 := by
  have h2 : IsRoot 3 2 := ⟨by decide, by decide⟩
  have h3 : IsRoot 3 3 := ⟨by decide, by decide⟩
  rw [Nat.card_coe_set_eq, chainProd_cons, chainProd_singleton,
    cardG_ncard_mul_of_left, pow_two]
  · exact congrArg₂ (· * ·) (hroot 3 h3) (hroot 2 h2)
  · intro c hc c' hc' b hb b' hb' hcb
    have h := congrArg (fun z => z⁻¹) hcb
    simp only [mul_inv_rev] at h
    have := R.cardG_unique3 (a := 1) (a' := 1) (root 1).one_mem (root 1).one_mem
      ((root 2).inv_mem hb) ((root 2).inv_mem hb') ((root 3).inv_mem hc) ((root 3).inv_mem hc')
      (by simpa using h)
    exact inv_injective this.2.2

theorem cardG_card_pref (R : RGD2 3 H r₁ r₂ U root) {q : ℕ}
    (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card (root k) = q) (hU : Nat.card U = q ^ 3)
    {i : ℕ} (hi : i ≤ 3) : Nat.card (chainProd root (intList 1 (i : ℤ))) = q ^ i := by
  interval_cases i
  · rw [show intList 1 ((0 : ℕ) : ℤ) = [] by decide, cardG_card_chain_nil, pow_zero]
  · rw [show intList 1 ((1 : ℕ) : ℤ) = [1] by decide,
      cardG_card_chain_one hroot (k := 1) ⟨by decide, by decide⟩, pow_one]
  · rw [show intList 1 ((2 : ℕ) : ℤ) = [1, 2] by decide, R.cardG_card_chain_12 hroot]
  · exact R.cardG_card_chain_U hU

theorem cardG_card_suf (R : RGD2 3 H r₁ r₂ U root) {q : ℕ}
    (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card (root k) = q) {j : ℕ} (hj : j < 2) :
    Nat.card (chainProd root
      (intList (((3 : ℕ) : ℤ) - (((j + 1 : ℕ)) : ℤ) + 1) ((3 : ℕ) : ℤ)).reverse) = q ^ (j + 1) := by
  interval_cases j
  · rw [show intList (((3 : ℕ) : ℤ) - (((0 + 1 : ℕ)) : ℤ) + 1) ((3 : ℕ) : ℤ) = [3] by decide,
      List.reverse_singleton, zero_add, pow_one]
    exact cardG_card_chain_one hroot (k := 3) ⟨by decide, by decide⟩
  · rw [show intList (((3 : ℕ) : ℤ) - (((1 + 1 : ℕ)) : ℤ) + 1) ((3 : ℕ) : ℤ) = [2, 3] by decide,
      show ([2, 3] : List ℤ).reverse = [3, 2] from rfl]
    exact R.cardG_card_chain_32 hroot

end Local

end RGD2

section Final

variable {X : Type*} [Group X] [Finite X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

namespace RGD2

theorem card_eq (R : RGD2 3 H r₁ r₂ U root) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 3 i → ∀ x ∈ root i, g * x = x * g) → g = 1) {q : ℕ}
    (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card (root k) = q) (hU : Nat.card U = q ^ 3) :
    Nat.card X = Nat.card H * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
  have hN := R.cartan_normal
  obtain ⟨D, hDB, hDroot⟩ : ∃ D : RankTwoSystem X 3, D.B = H ⊔ U ∧ D.root = root :=
    ⟨(R.toPre hgen).toSystem (R.faithful hgen hZ), rfl, rfl⟩
  have h := cardG_card_eq_general D
  rw [hDB, R.cardG_card_B, hU, hDroot] at h
  have e1 : ∑ i : Fin (3 + 1), Nat.card (chainProd root (intList 1 ((i : ℕ) : ℤ))) =
      ∑ i : Fin (3 + 1), q ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i _ => R.cardG_card_pref hroot hU (by have := i.2; omega)
  have e2 : ∑ j : Fin (3 - 1), Nat.card (chainProd root
      (intList (((3 : ℕ) : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ) + 1) ((3 : ℕ) : ℤ)).reverse) =
      ∑ j : Fin (3 - 1), q ^ ((j : ℕ) + 1) :=
    Finset.sum_congr rfl fun j _ => R.cardG_card_suf hroot (by have := j.2; omega)
  have hs : ∑ i : Fin (3 + 1), q ^ (i : ℕ) + ∑ j : Fin (3 - 1), q ^ ((j : ℕ) + 1) =
      (q + 1) * (q ^ 2 + q + 1) := by
    simp [Fin.sum_univ_succ]
    ring
  rw [e1, e2, hs] at h
  exact h

end RGD2

end Final

end CFSG.GH74.GLS.SP
