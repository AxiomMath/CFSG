module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open Matrix

variable {F : Type*} [Field F]

@[expose] def SemInv (σ : F ≃+* F) (b : (Fin 2 → F) → (Fin 2 → F)) : Prop :=
  (∀ w w', b (w + w') = b w + b w') ∧ (∀ (c : F) w, b (c • w) = σ c • b w) ∧ ∀ w, b (b w) = w

@[expose] def fixSet (b : (Fin 2 → F) → (Fin 2 → F)) : Set (Fin 2 → F) := {w | b w = w}

@[expose] def centSL (b : (Fin 2 → F) → (Fin 2 → F)) : Set (SpecialLinearGroup (Fin 2) F) :=
  {g | ∀ w, b (g.1.mulVec w) = g.1.mulVec (b w)}

@[expose] def fixSL (σ : F ≃+* F) : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  MonoidHom.eqLocus (SpecialLinearGroup.map (σ : F →+* F)) (MonoidHom.id _)

variable {σ : F ≃+* F} {b : (Fin 2 → F) → (Fin 2 → F)}

omit [Field F] in
theorem mem_fixSet {w : Fin 2 → F} : w ∈ fixSet b ↔ b w = w := Iff.rfl

theorem mem_fixSL {M : SpecialLinearGroup (Fin 2) F} :
    M ∈ fixSL σ ↔ ∀ i j, σ (M.1 i j) = M.1 i j := by
  show SpecialLinearGroup.map (σ : F →+* F) M = M ↔ _
  constructor
  · intro h i j
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) i j) h
    simpa using this
  · intro h
    refine SpecialLinearGroup.ext _ _ fun i j => ?_
    simpa using h i j

namespace SemInv

theorem add (hb : SemInv σ b) (w w' : Fin 2 → F) : b (w + w') = b w + b w' := hb.1 w w'

theorem smul (hb : SemInv σ b) (c : F) (w : Fin 2 → F) : b (c • w) = σ c • b w := hb.2.1 c w

theorem invol (hb : SemInv σ b) (w : Fin 2 → F) : b (b w) = w := hb.2.2 w

theorem sigma_sigma (hb : SemInv σ b) (x : F) : σ (σ x) = x := by
  have h1 := hb.invol (x • (![1, 0] : Fin 2 → F))
  rw [hb.smul, hb.smul, hb.invol] at h1
  simpa using congrFun h1 0

theorem exists_fixed_pair (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) :
    ∃ v₁ v₂ : Fin 2 → F, b v₁ = v₁ ∧ b v₂ = v₂ ∧ v₁ 0 * v₂ 1 - v₂ 0 * v₁ 1 ≠ 0 := by
  obtain ⟨c, hc⟩ := hσ
  by_contra H
  push Not at H
  have hp : ∀ w : Fin 2 → F, b (w + b w) = w + b w := fun w => by
    rw [hb.add, hb.invol, add_comm]
  have key : ∀ w : Fin 2 → F,
      (σ c - c) • w = σ c • (w + b w) - (c • w + b (c • w)) := by
    intro w
    rw [hb.smul]
    module
  have hzero : ∀ v₀ : Fin 2 → F, b v₀ = v₀ → v₀ = 0 := by
    intro v₀ hv₀
    have hα : ∀ w : Fin 2 → F, v₀ 0 * w 1 - w 0 * v₀ 1 = 0 := by
      intro w
      have h1 := H v₀ _ hv₀ (hp w)
      have h2 := H v₀ _ hv₀ (hp (c • w))
      have e0 := congrFun (key w) 0
      have e1 := congrFun (key w) 1
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at e0 e1 h1 h2
      have h3 : (σ c - c) * (v₀ 0 * w 1 - w 0 * v₀ 1) = 0 := by
        linear_combination (v₀ 0) * e1 - (v₀ 1) * e0 + σ c * h1 - h2
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)
    have a1 := hα ![1, 0]
    have a2 := hα ![0, 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_mul,
      one_mul, sub_zero, zero_sub, neg_eq_zero] at a1 a2
    ext i
    fin_cases i
    · exact a2
    · exact a1
  have hp1 := hzero _ (hp ![1, 0])
  have hq1 := hzero _ (hp (c • ![1, 0]))
  have h4 := key ![1, 0]
  rw [hp1, hq1] at h4
  have h5 := congrFun h4 0
  simp at h5
  exact hc (sub_eq_zero.1 h5)

end SemInv

theorem exists_normal_form (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) :
    ∃ h : GL (Fin 2) F, ∀ w, b w = h.1.mulVec (fun i => σ ((h⁻¹).1.mulVec w i)) := by
  obtain ⟨v₁, v₂, h1, h2, hdet⟩ := hb.exists_fixed_pair hσ
  let A : Matrix (Fin 2) (Fin 2) F := !![v₁ 0, v₂ 0; v₁ 1, v₂ 1]
  have hA : A.det ≠ 0 := by
    rw [det_fin_two]
    simpa [A] using hdet
  have hAx : ∀ y : Fin 2 → F, A.mulVec y = y 0 • v₁ + y 1 • v₂ := by
    intro y
    ext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  obtain ⟨h, hh⟩ : ∃ h : GL (Fin 2) F, h.1 = A := ⟨GeneralLinearGroup.mkOfDetNeZero A hA, rfl⟩
  refine ⟨h, fun w => ?_⟩
  have hw : w = h.1.mulVec ((h⁻¹).1.mulVec w) := by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  generalize (h⁻¹).1.mulVec w = x at hw ⊢
  rw [hw, hh, hAx x, hb.add, hb.smul, hb.smul, h1, h2, hAx]

theorem inv_mulVec_mulVec (h : GL (Fin 2) F) (x : Fin 2 → F) :
    (h⁻¹).1.mulVec (h.1.mulVec x) = x := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec]

theorem mulVec_inv_mulVec (h : GL (Fin 2) F) (x : Fin 2 → F) :
    h.1.mulVec ((h⁻¹).1.mulVec x) = x := by
  rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

theorem fixed_coord {h : GL (Fin 2) F}
    (hh : ∀ w, b w = h.1.mulVec (fun i => σ ((h⁻¹).1.mulVec w i))) {w : Fin 2 → F}
    (hw : w ∈ fixSet b) (i : Fin 2) :
    σ ((h⁻¹).1.mulVec w i) = (h⁻¹).1.mulVec w i := by
  have h1 : h.1.mulVec (fun i => σ ((h⁻¹).1.mulVec w i)) = w := (hh w).symm.trans hw
  have h2 := congrArg (fun z => (h⁻¹).1.mulVec z) h1
  simp only [inv_mulVec_mulVec] at h2
  exact congrFun h2 i

theorem sigma_mulVec {M : Matrix (Fin 2) (Fin 2) F} (hM : ∀ i j, σ (M i j) = M i j)
    (y : Fin 2 → F) (i : Fin 2) :
    σ (M.mulVec y i) = M.mulVec (fun j => σ (y j)) i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul, hM]

theorem exists_fixSL_mulVec_e₁ {x : Fin 2 → F} (hx : x ≠ 0) (hfix : ∀ i, σ (x i) = x i) :
    ∃ S ∈ fixSL σ, S.1.mulVec ![1, 0] = x := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      ext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨!![0, -(x 1)⁻¹; x 1, 0], ?_⟩, ?_, ?_⟩
    · rw [det_fin_two_of]
      field_simp
      ring
    · refine mem_fixSL.2 fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [map_neg, map_inv₀, hfix]
    · ext i
      fin_cases i <;> simp [mulVec, dotProduct, h0]
  · refine ⟨⟨!![x 0, 0; x 1, (x 0)⁻¹], ?_⟩, ?_, ?_⟩
    · rw [det_fin_two_of]
      field_simp
      ring
    · refine mem_fixSL.2 fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [map_inv₀, hfix]
    · ext i
      fin_cases i <;> simp [mulVec, dotProduct]

theorem exists_fixSL_mulVec_eq {x x' : Fin 2 → F} (hx : x ≠ 0) (hx' : x' ≠ 0)
    (hfix : ∀ i, σ (x i) = x i) (hfix' : ∀ i, σ (x' i) = x' i) :
    ∃ M ∈ fixSL σ, M.1.mulVec x = x' := by
  obtain ⟨S, hS, hSx⟩ := exists_fixSL_mulVec_e₁ hx hfix
  obtain ⟨S', hS', hSx'⟩ := exists_fixSL_mulVec_e₁ hx' hfix'
  refine ⟨S' * S⁻¹, mul_mem hS' (inv_mem hS), ?_⟩
  have h1 : (S⁻¹ * S).1 = 1 := by rw [inv_mul_cancel]; rfl
  have h2 : ∀ y : Fin 2 → F, (S⁻¹).1.mulVec (S.1.mulVec y) = y := fun y => by
    rw [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, h1, one_mulVec]
  rw [← hSx', ← hSx, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, h2]

theorem exists_sl_conj (h : GL (Fin 2) F) (M : SpecialLinearGroup (Fin 2) F) :
    ∃ g : SpecialLinearGroup (Fin 2) F, g.1 = h.1 * M.1 * (h⁻¹).1 := by
  refine ⟨⟨h.1 * M.1 * (h⁻¹).1, ?_⟩, rfl⟩
  have h1 : h.1.det * (h⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, M.2]
  linear_combination h1

theorem exists_centSL_smul (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) {w w' : Fin 2 → F}
    (hw : w ∈ fixSet b) (hw' : w' ∈ fixSet b) (h0 : w ≠ 0) (h0' : w' ≠ 0) :
    ∃ g ∈ centSL b, g.1.mulVec w = w' := by
  obtain ⟨h, hh⟩ := exists_normal_form hσ hb
  have hx : (h⁻¹).1.mulVec w ≠ 0 := fun hx =>
    h0 (by rw [← mulVec_inv_mulVec h w, hx, mulVec_zero])
  have hx' : (h⁻¹).1.mulVec w' ≠ 0 :=
    fun hx => h0' (by rw [← mulVec_inv_mulVec h w', hx, mulVec_zero])
  obtain ⟨M, hM, hMx⟩ := exists_fixSL_mulVec_eq hx hx' (fixed_coord hh hw) (fixed_coord hh hw')
  obtain ⟨g, hg⟩ := exists_sl_conj h M
  have hgv : ∀ v, g.1.mulVec v = h.1.mulVec (M.1.mulVec ((h⁻¹).1.mulVec v)) := fun v => by
    rw [hg, ← mulVec_mulVec, ← mulVec_mulVec]
  refine ⟨g, fun v => ?_, ?_⟩
  · have e1 : (h⁻¹).1.mulVec (g.1.mulVec v) = M.1.mulVec ((h⁻¹).1.mulVec v) := by
      rw [hgv, inv_mulVec_mulVec]
    rw [hh (g.1.mulVec v), e1, hgv (b v), hh v, inv_mulVec_mulVec]
    congr 2
    funext i
    exact sigma_mulVec (mem_fixSL.1 hM) _ i
  · rw [hgv, hMx, mulVec_inv_mulVec]

theorem card_fixSet [Finite F] (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) :
    Nat.card ↥(fixSet b) = Nat.card F := by
  obtain ⟨c, hc⟩ := id hσ
  have hss := hb.sigma_sigma
  have hd : c - σ c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  have hσd : σ (c - σ c) = -(c - σ c) := by rw [map_sub, hss]; ring
  obtain ⟨e, he⟩ : ∃ e : F, e + σ e ≠ 0 := by
    by_cases h : c + σ c = 0
    · refine ⟨1, ?_⟩
      rw [map_one]
      intro h2
      exact hc (by linear_combination h - c * h2)
    · exact ⟨c, h⟩
  let T : (Fin 2 → F) →+ (Fin 2 → F) :=
    AddMonoidHom.mk' (fun w => w + b w) fun w w' => by rw [hb.add]; abel
  have hT : ∀ w, T w = w + b w := fun w => rfl
  have hrange : ∀ u, u ∈ T.range ↔ u ∈ fixSet b := by
    intro u
    rw [AddMonoidHom.mem_range, mem_fixSet]
    constructor
    · rintro ⟨y, rfl⟩
      rw [hT, hb.add, hb.invol, add_comm]
    · intro hu
      have hσt : σ (e + σ e) = e + σ e := by rw [map_add, hss, add_comm]
      refine ⟨((e + σ e)⁻¹ * e) • u, ?_⟩
      rw [hT, hb.smul, hu, ← add_smul, map_mul, map_inv₀, hσt, ← mul_add,
        inv_mul_cancel₀ he, one_smul]
  have hk1 : ∀ w, w ∈ T.ker → (c - σ c)⁻¹ • w ∈ fixSet b := by
    intro w hw
    rw [AddMonoidHom.mem_ker, hT] at hw
    have hbw : b w = -w := eq_neg_of_add_eq_zero_right hw
    simp only [mem_fixSet, hb.smul, hbw, map_inv₀, hσd, inv_neg, neg_smul, smul_neg, neg_neg]
  have hk2 : ∀ u, u ∈ fixSet b → (c - σ c) • u ∈ T.ker := by
    intro u hu
    rw [mem_fixSet] at hu
    rw [AddMonoidHom.mem_ker, hT, hb.smul, hu, hσd, neg_smul, add_neg_cancel]
  have hker : Nat.card T.ker = Nat.card (fixSet b) :=
    Nat.card_congr
      { toFun := fun w => ⟨(c - σ c)⁻¹ • (w : Fin 2 → F), hk1 w w.2⟩
        invFun := fun u => ⟨(c - σ c) • (u : Fin 2 → F), hk2 u u.2⟩
        left_inv := fun w => Subtype.ext (smul_inv_smul₀ hd _)
        right_inv := fun u => Subtype.ext (inv_smul_smul₀ hd _) }
  have hmul := AddSubgroup.card_ker_mul_card_range T
  have hrange' : Nat.card T.range = Nat.card (fixSet b) :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange)
  have hF : Nat.card (Fin 2 → F) = Nat.card F * Nat.card F := by
    rw [Nat.card_fun]
    simp [sq]
  rw [hker, hrange', hF] at hmul
  exact Nat.mul_self_inj.1 hmul

theorem exists_centSL_ne [Finite F] (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) {w : Fin 2 → F}
    (hw : w ∈ fixSet b) (h0 : w ≠ 0) : ∃ g ∈ centSL b, g.1.mulVec w ≠ w := by
  obtain ⟨c, hc⟩ := id hσ
  have h3 : 2 < (fixSet b).ncard := by
    rw [← Nat.card_coe_set_eq, card_fixSet hσ hb, ← Set.ncard_univ,
      Set.two_lt_ncard_iff (Set.toFinite _)]
    refine ⟨0, 1, c, Set.mem_univ _, Set.mem_univ _, Set.mem_univ _, zero_ne_one, ?_, ?_⟩
    · rintro rfl
      exact hc (map_zero σ)
    · rintro rfl
      exact hc (map_one σ)
  obtain ⟨a, a', a'', ha, ha', ha'', h1, h2, h3'⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).1 h3
  obtain ⟨y, hy, hy0, hyw⟩ : ∃ y ∈ fixSet b, y ≠ 0 ∧ y ≠ w := by
    by_contra hcon
    push Not at hcon
    have f : ∀ y ∈ fixSet b, y = 0 ∨ y = w := fun y hy => by
      by_cases hy0 : y = 0
      · exact Or.inl hy0
      · exact Or.inr (hcon y hy hy0)
    rcases f a ha with rfl | rfl <;> rcases f a' ha' with rfl | rfl <;>
      rcases f a'' ha'' with rfl | rfl <;> simp_all
  obtain ⟨g, hg, hgw⟩ := exists_centSL_smul hσ hb hw hy h0 hy0
  exact ⟨g, hg, by rw [hgw]; exact hyw⟩

theorem irred_fixSet (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) (X : AddSubgroup (Fin 2 → F))
    (hX : ∀ w ∈ X, w ∈ fixSet b)
    (hinv : ∀ g ∈ centSL b, ∀ w ∈ X, g.1.mulVec w ∈ X) :
    X = ⊥ ∨ ∀ w ∈ fixSet b, w ∈ X := by
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwX, hw0⟩ : ∃ w ∈ X, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.2 fun x hx => by simpa using hcon x hx)
  intro w' hw'
  by_cases h0 : w' = 0
  · rw [h0]
    exact X.zero_mem
  obtain ⟨g, hg, hgw⟩ := exists_centSL_smul hσ hb (hX w hwX) hw' hw0 h0
  rw [← hgw]
  exact hinv g hg w hwX

theorem exists_kappa_of_invariant {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup A] (β : F →+ F →+ A)
    (h : ∀ (l : Fˣ) (r s : F), β ((l⁻¹ : Fˣ) * r) ((l : F) ^ 2 * s) = β r s) :
    ∃ κ : F →+ A, ∀ r s, β r s = κ (r ^ 2 * s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (frobenius F 2) := frobenius_inj F 2
  have hsurj : Function.Surjective (frobenius F 2) := Finite.surjective_of_injective hinj
  let e : F ≃+* F := RingEquiv.ofBijective (frobenius F 2) ⟨hinj, hsurj⟩
  have he : ∀ x, e x = x ^ 2 := fun x => by
    rw [show e x = frobenius F 2 x from rfl, frobenius_def]
  have key : ∀ r s : F, β r s = β (e.symm s * r) 1 := by
    intro r s
    by_cases hs : s = 0
    · subst hs
      simp
    · have hl : e.symm s ≠ 0 := fun h0 => hs (by simpa using congrArg e h0)
      have hl2 : e.symm s ^ 2 = s := by rw [← he, RingEquiv.apply_symm_apply]
      have h1 := h (Units.mk0 (e.symm s) hl)⁻¹ r s
      simp only [inv_inv, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hl2] at h1
      rw [inv_mul_cancel₀ hs] at h1
      exact h1.symm
  let κ : F →+ A := AddMonoidHom.mk' (fun x => β (e.symm x) 1) fun x y => by
    rw [map_add, map_add, AddMonoidHom.add_apply]
  refine ⟨κ, fun r s => ?_⟩
  have hκ : κ (r ^ 2 * s) = β (e.symm (r ^ 2 * s)) 1 := rfl
  rw [key r s, hκ, map_mul e.symm (r ^ 2) s,
    show e.symm (r ^ 2) = r by rw [← he, RingEquiv.symm_apply_apply], mul_comm]

end CFSG.CGT.PushingUpLit.A78Sp4
