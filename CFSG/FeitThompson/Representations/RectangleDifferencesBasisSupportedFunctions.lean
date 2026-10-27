module

public import CFSG.FeitThompson.Representations.ProductCharactersFullBasis
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

open scoped Classical in
theorem natCard_ne_eq {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  have := Fintype.ofFinite α
  simp [Nat.card_eq_fintype_card, ← Set.card_ne_eq a]

theorem classFun_eq_top (X : Type*) [Group X] [IsMulCommutative X] : classFun X = ⊤ := by
  refine eq_top_iff.2 fun f _ => mem_classFun.2 fun x y hxy => ?_
  let _ : CommGroup X := IsMulCommutative.instCommGroup
  rw [isConj_iff_eq.1 hxy]

theorem dadeDomain_eq_spanSubset (L : Subgroup G) [IsMulCommutative ↥L] [Finite ↥L] (A : Set G) :
    dadeDomain L A = Pi.spanSubset ℂ {x : ↥L | (x : G) ∈ A} := by
  ext f
  rw [mem_dadeDomain, Pi.mem_spanSubset_iff, classFun_eq_top]
  simp

theorem finrank_dadeDomain (L : Subgroup G) [IsMulCommutative ↥L] [Finite ↥L] (A : Set G) :
    Module.finrank ℂ (dadeDomain L A) = Nat.card {x : ↥L // (x : G) ∈ A} := by
  rw [dadeDomain_eq_spanSubset, Pi.dim_spanSubset]
  exact (Nat.card_coe_set_eq _).symm

abbrev NonprincipalIrrPair (W1 W2 : Subgroup G) : Type _ :=
  {i : Irr ↥W1 // i ≠ principalIrr ↥W1} × {j : Irr ↥W2 // j ≠ principalIrr ↥W2}

namespace IsCyclicTIPair

theorem prodCharAlpha_apply_mul (h : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ)
    {x y : G} (hx : x ∈ W1) (hy : y ∈ W2) :
    h.prodCharAlpha lam mu ⟨x * y, mul_mem (h.left_le hx) (h.right_le hy)⟩ =
      (1 - lam ⟨x, hx⟩) * (1 - mu ⟨y, hy⟩) := by
  rw [h.prodCharAlpha_eq_mul, Pi.mul_apply, Pi.sub_apply, Pi.sub_apply, Pi.one_apply,
    h.prodChar_apply_mul lam 1 hx hy, h.prodChar_apply_mul 1 mu hx hy]
  simp

theorem prodCharAlpha_apply_eq_zero_of_mem_left (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ}
    {mu : ↥W2 → ℂ} (hmu : mu ∈ Irr ↥W2) {z : ↥W} (hz : (z : G) ∈ W1) :
    h.prodCharAlpha lam mu z = 0 := by
  have := h.isMulCommutative_right
  have hmu1 : mu ⟨(1 : G), one_mem W2⟩ = 1 := apply_one_eq_one_of_mem_Irr hmu
  have hz' : z = ⟨(z : G) * (1 : G), mul_mem (h.left_le hz) (h.right_le (one_mem W2))⟩ :=
    Subtype.ext (by simp)
  rw [hz', h.prodCharAlpha_apply_mul lam mu hz (one_mem W2), hmu1, sub_self, mul_zero]

theorem prodCharAlpha_apply_eq_zero_of_mem_right (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ}
    {mu : ↥W2 → ℂ} (hlam : lam ∈ Irr ↥W1) {z : ↥W} (hz : (z : G) ∈ W2) :
    h.prodCharAlpha lam mu z = 0 := by
  have := h.isMulCommutative_left
  have hlam1 : lam ⟨(1 : G), one_mem W1⟩ = 1 := apply_one_eq_one_of_mem_Irr hlam
  have hz' : z = ⟨(1 : G) * (z : G), mul_mem (h.left_le (one_mem W1)) (h.right_le hz)⟩ :=
    Subtype.ext (by simp)
  rw [hz', h.prodCharAlpha_apply_mul lam mu (one_mem W1) hz, hlam1, sub_self, zero_mul]

theorem prodCharAlpha_mem_dadeDomain (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ} {mu : ↥W2 → ℂ}
    (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) :
    h.prodCharAlpha lam mu ∈ dadeDomain W (cyclicTIDiff W W1 W2) := by
  have := h.isMulCommutative_coe
  refine mem_dadeDomain.2 ⟨by rw [classFun_eq_top]; trivial, fun z hz => ?_⟩
  rw [mem_cyclicTIDiff, not_and_or, not_and_or] at hz
  rcases hz with hz | hz | hz
  · exact absurd z.2 hz
  · exact prodCharAlpha_apply_eq_zero_of_mem_left h hmu (not_not.1 hz)
  · exact prodCharAlpha_apply_eq_zero_of_mem_right h hlam (not_not.1 hz)

open scoped Classical in
theorem cfInner_prodCharAlpha_prodChar (h : IsCyclicTIPair W W1 W2) [Fintype ↥W]
    (i k : Irr ↥W1) (j l : Irr ↥W2) (hk : k ≠ principalIrr ↥W1) (hl : l ≠ principalIrr ↥W2) :
    cfInner (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodChar (k : ↥W1 → ℂ) (l : ↥W2 → ℂ)) = if i = k ∧ j = l then 1 else 0 := by
  have hone : (1 : ↥W → ℂ) = h.prodChar ((principalIrr ↥W1 : Irr ↥W1) : ↥W1 → ℂ)
      ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) := by
    rw [coe_principalIrr, coe_principalIrr, h.prodChar_one_one]
  have h1 : h.prodChar (i : ↥W1 → ℂ) (1 : ↥W2 → ℂ) =
      h.prodChar (i : ↥W1 → ℂ) ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) := by
    rw [coe_principalIrr]
  have h2 : h.prodChar (1 : ↥W1 → ℂ) (j : ↥W2 → ℂ) =
      h.prodChar ((principalIrr ↥W1 : Irr ↥W1) : ↥W1 → ℂ) (j : ↥W2 → ℂ) := by
    rw [coe_principalIrr]
  rw [prodCharAlpha_eq, hone, h1, h2, cfInner_add_left, cfInner_sub_left, cfInner_sub_left,
    h.cfInner_prodChar_eq_ite_and, h.cfInner_prodChar_eq_ite_and,
    h.cfInner_prodChar_eq_ite_and, h.cfInner_prodChar_eq_ite_and,
    if_neg (fun hc => hk hc.1.symm), if_neg (fun hc => hl hc.2.symm),
    if_neg (fun hc => hk hc.1.symm)]
  ring

theorem linearIndependent_prodCharAlpha (h : IsCyclicTIPair W W1 W2) :
    LinearIndependent ℂ (fun p : NonprincipalIrrPair W1 W2 =>
      h.prodCharAlpha ((p.1.1 : Irr ↥W1) : ↥W1 → ℂ) ((p.2.1 : Irr ↥W2) : ↥W2 → ℂ)) := by
  classical
  have := h.finite_coe
  have : Fintype ↥W := Fintype.ofFinite ↥W
  rw [linearIndependent_iff']
  intro s g hsum p hp
  set w := h.prodChar ((p.1.1 : Irr ↥W1) : ↥W1 → ℂ) ((p.2.1 : Irr ↥W2) : ↥W2 → ℂ) with hw
  have h0 : cfInner (∑ i ∈ s, g i • h.prodCharAlpha ((i.1.1 : Irr ↥W1) : ↥W1 → ℂ)
      ((i.2.1 : Irr ↥W2) : ↥W2 → ℂ)) w = 0 := by
    rw [hsum, cfInner_zero_left]
  rw [cfInner_sum_left] at h0
  have hterm : ∀ q ∈ s, cfInner (g q • h.prodCharAlpha ((q.1.1 : Irr ↥W1) : ↥W1 → ℂ)
      ((q.2.1 : Irr ↥W2) : ↥W2 → ℂ)) w = if q = p then g q else 0 := by
    intro q _
    rw [cfInner_smul_left, hw, h.cfInner_prodCharAlpha_prodChar _ _ _ _ p.1.2 p.2.2]
    by_cases hqp : q = p
    · subst hqp; simp
    · rw [if_neg, mul_zero, if_neg hqp]
      intro hc
      exact hqp (Prod.ext (Subtype.ext hc.1) (Subtype.ext hc.2))
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s p g] at h0
  simpa [hp] using h0

theorem mul_mem_cyclicTIDiff_iff (h : IsCyclicTIPair W W1 W2) {x y : G} (hx : x ∈ W1)
    (hy : y ∈ W2) : x * y ∈ cyclicTIDiff W W1 W2 ↔ x ≠ 1 ∧ y ≠ 1 := by
  have hmem : x * y ∈ W := mul_mem (h.left_le hx) (h.right_le hy)
  rw [mem_cyclicTIDiff]
  refine ⟨fun ⟨_, h1, h2⟩ => ⟨?_, ?_⟩, fun ⟨hx1, hy1⟩ => ⟨hmem, ?_, ?_⟩⟩
  · rintro rfl; exact h2 (by simpa using hy)
  · rintro rfl; exact h1 (by simpa using hx)
  · intro hc
    have : y ∈ W1 ⊓ W2 := ⟨by simpa using mul_mem (W1.inv_mem hx) hc, hy⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at this
    exact hy1 this
  · intro hc
    have : x ∈ W1 ⊓ W2 := ⟨hx, by simpa using mul_mem hc (W2.inv_mem hy)⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at this
    exact hx1 this

theorem mem_cyclicTIDiff_iff (h : IsCyclicTIPair W W1 W2) (z : ↥W) :
    (z : G) ∈ cyclicTIDiff W W1 W2 ↔
      (h.mulEquivProd.symm z).1 ≠ 1 ∧ (h.mulEquivProd.symm z).2 ≠ 1 := by
  set p := h.mulEquivProd.symm z with hp
  have hz : (z : G) = (p.1 : G) * (p.2 : G) := by
    have := h.coe_mulEquivProd_apply p
    rwa [hp, MulEquiv.apply_symm_apply] at this
  rw [hz, h.mul_mem_cyclicTIDiff_iff p.1.2 p.2.2]
  simp only [ne_eq, OneMemClass.coe_eq_one]

noncomputable def cyclicTIDiffEquiv (h : IsCyclicTIPair W W1 W2) :
    {z : ↥W // (z : G) ∈ cyclicTIDiff W W1 W2} ≃ {x : ↥W1 // x ≠ 1} × {y : ↥W2 // y ≠ 1} where
  toFun z := (⟨(h.mulEquivProd.symm z.1).1, ((h.mem_cyclicTIDiff_iff z.1).1 z.2).1⟩,
    ⟨(h.mulEquivProd.symm z.1).2, ((h.mem_cyclicTIDiff_iff z.1).1 z.2).2⟩)
  invFun p := ⟨h.mulEquivProd (p.1.1, p.2.1), by
    rw [h.mem_cyclicTIDiff_iff, MulEquiv.symm_apply_apply]
    exact ⟨p.1.2, p.2.2⟩⟩
  left_inv z := by simp
  right_inv p := by simp

theorem natCard_cyclicTIDiff (h : IsCyclicTIPair W W1 W2) :
    Nat.card {z : ↥W // (z : G) ∈ cyclicTIDiff W W1 W2} =
      (Nat.card ↥W1 - 1) * (Nat.card ↥W2 - 1) := by
  have := h.finite_left
  have := h.finite_right
  rw [Nat.card_congr h.cyclicTIDiffEquiv, Nat.card_prod, natCard_ne_eq, natCard_ne_eq]

theorem nontrivial_Irr_left (h : IsCyclicTIPair W W1 W2) : Nontrivial (Irr ↥W1) := by
  have := h.finite_left
  have : Finite (Irr ↥W1) := finite_coe_Irr
  rw [← Finite.one_lt_card_iff_nontrivial, h.card_Irr_left]
  exact lt_of_lt_of_le (by norm_num) h.three_le_natCard_left

theorem nontrivial_Irr_right (h : IsCyclicTIPair W W1 W2) : Nontrivial (Irr ↥W2) := by
  have := h.finite_right
  have : Finite (Irr ↥W2) := finite_coe_Irr
  rw [← Finite.one_lt_card_iff_nontrivial, h.card_Irr_right]
  exact lt_of_lt_of_le (by norm_num) h.three_le_natCard_right

theorem nonempty_nonprincipalIrrPair (h : IsCyclicTIPair W W1 W2) :
    Nonempty (NonprincipalIrrPair W1 W2) := by
  have := h.nontrivial_Irr_left
  have := h.nontrivial_Irr_right
  obtain ⟨i, hi⟩ := exists_ne (principalIrr ↥W1)
  obtain ⟨j, hj⟩ := exists_ne (principalIrr ↥W2)
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

theorem finite_nonprincipalIrrPair (h : IsCyclicTIPair W W1 W2) :
    Finite (NonprincipalIrrPair W1 W2) := by
  have := h.finite_left
  have := h.finite_right
  have : Finite (Irr ↥W1) := finite_coe_Irr
  have : Finite (Irr ↥W2) := finite_coe_Irr
  infer_instance

theorem natCard_nonprincipalIrrPair (h : IsCyclicTIPair W W1 W2) :
    Nat.card (NonprincipalIrrPair W1 W2) =
      Nat.card {z : ↥W // (z : G) ∈ cyclicTIDiff W W1 W2} := by
  have := h.finite_left
  have := h.finite_right
  have : Finite (Irr ↥W1) := finite_coe_Irr
  have : Finite (Irr ↥W2) := finite_coe_Irr
  rw [Nat.card_prod, natCard_ne_eq, natCard_ne_eq, h.natCard_cyclicTIDiff, h.card_Irr_left,
    h.card_Irr_right]

noncomputable def prodCharAlphaDade (h : IsCyclicTIPair W W1 W2) (p : NonprincipalIrrPair W1 W2) :
    dadeDomain W (cyclicTIDiff W W1 W2) :=
  ⟨h.prodCharAlpha ((p.1.1 : Irr ↥W1) : ↥W1 → ℂ) ((p.2.1 : Irr ↥W2) : ↥W2 → ℂ),
    h.prodCharAlpha_mem_dadeDomain p.1.1.2 p.2.1.2⟩

@[simp]
theorem coe_prodCharAlphaDade (h : IsCyclicTIPair W W1 W2) (p : NonprincipalIrrPair W1 W2) :
    (h.prodCharAlphaDade p : ↥W → ℂ) =
      h.prodCharAlpha ((p.1.1 : Irr ↥W1) : ↥W1 → ℂ) ((p.2.1 : Irr ↥W2) : ↥W2 → ℂ) := (rfl)

theorem linearIndependent_prodCharAlphaDade (h : IsCyclicTIPair W W1 W2) :
    LinearIndependent ℂ h.prodCharAlphaDade :=
  LinearIndependent.of_comp (dadeDomain W (cyclicTIDiff W W1 W2)).subtype
    h.linearIndependent_prodCharAlpha

theorem span_prodCharAlphaDade (h : IsCyclicTIPair W W1 W2) :
    Submodule.span ℂ (Set.range h.prodCharAlphaDade) = ⊤ := by
  have := h.finite_coe
  have := h.isMulCommutative_coe
  have := h.finite_nonprincipalIrrPair
  have : Fintype (NonprincipalIrrPair W1 W2) := Fintype.ofFinite _
  have := h.nonempty_nonprincipalIrrPair
  exact h.linearIndependent_prodCharAlphaDade.span_eq_top_of_card_eq_finrank
    (by rw [finrank_dadeDomain, ← Nat.card_eq_fintype_card, h.natCard_nonprincipalIrrPair])

noncomputable def basisProdCharAlpha (h : IsCyclicTIPair W W1 W2) :
    Module.Basis (NonprincipalIrrPair W1 W2) ℂ (dadeDomain W (cyclicTIDiff W W1 W2)) :=
  Module.Basis.mk h.linearIndependent_prodCharAlphaDade (le_of_eq h.span_prodCharAlphaDade.symm)

@[simp]
theorem coe_basisProdCharAlpha (h : IsCyclicTIPair W W1 W2) :
    (h.basisProdCharAlpha : NonprincipalIrrPair W1 W2 → dadeDomain W (cyclicTIDiff W W1 W2)) =
      h.prodCharAlphaDade :=
  Module.Basis.coe_mk _ _

@[simp]
theorem coe_basisProdCharAlpha_apply (h : IsCyclicTIPair W W1 W2)
    (p : NonprincipalIrrPair W1 W2) :
    ((h.basisProdCharAlpha p : dadeDomain W (cyclicTIDiff W W1 W2)) : ↥W → ℂ) =
      h.prodCharAlpha ((p.1.1 : Irr ↥W1) : ↥W1 → ℂ) ((p.2.1 : Irr ↥W2) : ↥W2 → ℂ) := by
  rw [coe_basisProdCharAlpha, coe_prodCharAlphaDade]

end IsCyclicTIPair

end CFSG.FeitThompson
