module

public import CFSG.Adapters.TauCetiExceptional.BigCellG2
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
open Polynomial

section Frobenius

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem coe_finiteFrobeniusAut_pow_G2
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 3) (k : ℕ)
    (g : adjointGroup ReeTag.G2.tag K) :
    ((ReeTag.G2.finiteFrobeniusAut K ^ k) g : ModGL ReeTag.G2.tag K) =
      Units.map (entrywiseHom (σ ^ k).toRingHom) (g : ModGL ReeTag.G2.tag K) := by
  induction k with
  | zero =>
    refine Units.ext ?_
    simp only [pow_zero, MulAut.one_apply, Units.coe_map]
    exact (entrywise_id _).symm
  | succ k ih =>
    refine Units.ext ?_
    rw [pow_succ', MulAut.mul_apply, ReeTag.coe_finiteFrobeniusAut, entrywiseGL, Units.coe_map,
      ih, Units.coe_map, Units.coe_map]
    change entrywise (frobenius K ReeTag.G2.prime) (entrywise (σ ^ k).toRingHom _) =
      entrywise (σ ^ (k + 1)).toRingHom _
    rw [entrywise_entrywise]
    congr 1
    refine RingHom.ext fun c => ?_
    rw [pow_succ', RingHom.comp_apply]
    change (frobenius K ReeTag.G2.prime) ((σ ^ k) c) = σ ((σ ^ k) c)
    rw [hσ, frobenius_def]
    rfl

omit [Finite K] [CharP K ReeTag.G2.prime] in
theorem ringEquiv_pow_apply_of_cube {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 3) (k : ℕ) (c : K) :
    (σ ^ k) c = c ^ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change σ ((σ ^ k) c) = _
    rw [ih, hσ, ← pow_mul, pow_succ]

theorem conj_eq_of_even
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 3) (g : adjointGroup ReeTag.G2.tag K)
    (j : ℕ) (x : adjointGroup ReeTag.G2.tag K) :
    ((MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ (2 * j)) x : ModGL ReeTag.G2.tag K) =
      (g : ModGL ReeTag.G2.tag K) * Units.map (entrywiseHom (σ ^ j).toRingHom)
        (x : ModGL ReeTag.G2.tag K) * (g : ModGL ReeTag.G2.tag K)⁻¹ := by
  rw [MulAut.mul_apply, finiteExceptionalAut_pow_two_mul, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_finiteFrobeniusAut_pow_G2 hσ]

theorem finiteFrobeniusAut_pow_xElement
    (j : ℕ) (i : Fin ReeTag.G2.tag.rank) (c : K) :
    (ReeTag.G2.finiteFrobeniusAut K ^ j) (xElement i c) = xElement i (c ^ 3 ^ j) := by
  have hσ : ∀ c : K, frobeniusEquiv K ReeTag.G2.prime c = c ^ 3 := fun c =>
    frobeniusEquiv_def K ReeTag.G2.prime c
  refine Subtype.ext ?_
  rw [coe_finiteFrobeniusAut_pow_G2 hσ]
  refine Units.ext ?_
  change entrywise ((frobeniusEquiv K ReeTag.G2.prime) ^ j).toRingHom (xOp _ K i c) =
    xOp _ K i (c ^ 3 ^ j)
  rw [CFSG.LieType.Chevalley.entrywise_xOp]
  congr 1
  exact ringEquiv_pow_apply_of_cube hσ j c

theorem finiteExceptionalAut_odd_xElement_zero
    (j : ℕ) (c : K) :
    (ReeTag.G2.finiteExceptionalAut K ^ (2 * j + 1)) (xElement ⟨0, by decide⟩ c) =
      xElement ⟨1, by decide⟩ (c ^ 3 ^ j) := by
  rw [pow_succ', MulAut.mul_apply, finiteExceptionalAut_pow_two_mul,
    finiteFrobeniusAut_pow_xElement, ReeTag.finiteExceptionalAut_xElement]
  have hperm : ReeTag.G2.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have hexp : ReeTag.G2.exponent ⟨0, by decide⟩ = 1 := by decide
  rw [hperm, hexp, pow_one]

theorem finiteExceptionalAut_odd_xElement_one
    (j : ℕ) (c : K) :
    (ReeTag.G2.finiteExceptionalAut K ^ (2 * j + 1)) (xElement ⟨1, by decide⟩ c) =
      xElement ⟨0, by decide⟩ (c ^ 3 ^ (j + 1)) := by
  rw [pow_succ, MulAut.mul_apply, ReeTag.finiteExceptionalAut_xElement]
  have hperm : ReeTag.G2.perm ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
  have hexp : ReeTag.G2.exponent ⟨1, by decide⟩ = 3 := by decide
  rw [hperm, hexp, finiteExceptionalAut_pow_two_mul, finiteFrobeniusAut_pow_xElement, ← pow_mul,
    pow_succ']

end Frobenius

section Entries

variable {τ : Tag} {L : Type} [Field L]

theorem xOp_entry_inl
    (i : Fin τ.rank) (c : L) :
    xOp τ L i c (Finsupp.single (Sum.inl i) 1) (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩) =
      2 * c := by
  simp only [xOp_single_inl, τ.cartan_self, rootVec_eq_single (isRoot_single τ i),
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hVec]
  rw [Finsupp.single_eq_of_ne (by simp), zero_add]
  norm_num

theorem xOp_entry_neg
    (i : Fin τ.rank) (c : L) :
    xOp τ L i c (Finsupp.single (Sum.inr ⟨-Pi.single i 1, isRoot_neg_single τ i⟩) 1)
      (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩) = c ^ 2 := by
  rw [← rootVec_eq_single (isRoot_neg_single τ i), xOp_rootVec_neg_single',
    rootVec_eq_single (isRoot_neg_single τ i), rootVec_eq_single (isRoot_single τ i), hVec]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  rw [Finsupp.single_eq_of_ne, Finsupp.single_eq_of_ne (by simp), mul_zero, zero_add, zero_add]
  intro e
  have := congrArg (fun v : Fin τ.rank → ℤ => v i) (congrArg Subtype.val (Sum.inr_injective e))
  simp at this

end Entries

abbrev g2Long : Fin ReeTag.G2.tag.rank := ⟨0, by decide⟩

abbrev g2Short : Fin ReeTag.G2.tag.rank := ⟨1, by decide⟩

theorem false_of_conj_odd
    {L : Type} [Field L] (h2 : (2 : L) ≠ 0) (E : Subfield L) [Finite E]
    [CharP E ReeTag.G2.prime] {f : ℕ} (hE : Nat.card E = 3 ^ f) (hf : 2 ≤ f)
    (h' : ModGL ReeTag.G2.tag L) {j : ℕ} (hj : 2 * j + 1 < 2 * f)
    (hconj : ∀ x : adjointGroup ReeTag.G2.tag E,
      h' * baseChangeGL E.subtype (x : ModGL ReeTag.G2.tag E) * h'⁻¹ = baseChangeGL E.subtype
        ((ReeTag.G2.finiteExceptionalAut E ^ (2 * j + 1)) x : ModGL ReeTag.G2.tag E)) :
    False := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 3 ^ f := by rw [← Nat.card_eq_fintype_card, hE]
  set T : Module.End L (RootModule ReeTag.G2.tag L) → Module.End L (RootModule ReeTag.G2.tag L) :=
    fun A => (h' : Module.End L (RootModule ReeTag.G2.tag L)) * A *
      ((h'⁻¹ : ModGL ReeTag.G2.tag L) : Module.End L (RootModule ReeTag.G2.tag L)) with hT
  have hT1 : T 1 = 1 := by simp only [hT, mul_one, Units.mul_inv]
  have hTadd : ∀ A B, T (A + B) = T A + T B := fun A B => by
    simp only [hT, mul_add, add_mul]
  have hTsmul : ∀ (e : L) A, T (e • A) = e • T A := fun e A => by
    simp only [hT, mul_smul_comm, smul_mul_assoc]
  have hx : ∀ (i i' : Fin ReeTag.G2.tag.rank) (c : E) (d : E),
      (ReeTag.G2.finiteExceptionalAut E ^ (2 * j + 1)) (xElement i c) = xElement i' d →
        T (xOp ReeTag.G2.tag L i (c : L)) = xOp ReeTag.G2.tag L i' (d : L) := by
    intro i i' c d hcd
    have e := congrArg Units.val (hconj (xElement i c))
    rw [hcd] at e
    simpa only [hT, xElement, baseChangeGL_xUnit, Units.val_mul, coe_xUnit,
      Subfield.coe_subtype] using e
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  ·
    set ε : ℕ → L := fun k => T (xCoeff ReeTag.G2.tag L g2Short k)
      (Finsupp.single (Sum.inr ⟨-Pi.single g2Long 1, isRoot_neg_single _ g2Long⟩) 1)
      (Sum.inr ⟨Pi.single g2Long 1, isRoot_single _ g2Long⟩) with hε
    have hid : ∀ c : E, (c : L) ^ 6 = ∑ k ∈ Finset.range 4, ε k * (c : L) ^ k := by
      intro c
      have e := hx g2Short g2Long c (c ^ 3 ^ (0 + 1))
        (finiteExceptionalAut_odd_xElement_one 0 c)
      rw [xOp_eq_sum_xCoeff] at e
      have e' := congrArg (fun A : Module.End L (RootModule ReeTag.G2.tag L) =>
        A (Finsupp.single (Sum.inr ⟨-Pi.single g2Long 1, isRoot_neg_single _ g2Long⟩) 1)
          (Sum.inr ⟨Pi.single g2Long 1, isRoot_single _ g2Long⟩)) e
      simp only [hT, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
        LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul, xOp_entry_neg] at e'
      rw [hε]
      simp only
      rw [show (c : L) ^ 6 = ((((c ^ 3 ^ (0 + 1) : E)) : L)) ^ 2 by push_cast; ring, ← e']
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have heval : ∀ c : E, (X ^ 6 - ∑ k ∈ Finset.range 4, C (ε k) * X ^ k : L[X]).eval
        (E.subtype c) = 0 := by
      intro c
      simp only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C,
        Subfield.coe_subtype]
      rw [hid c, sub_self]
    have hP := eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ E.subtype_injective heval (by
      rw [hcardE]
      calc natDegree (X ^ 6 - ∑ k ∈ Finset.range 4, C (ε k) * X ^ k : L[X]) ≤ 6 := by
            refine (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le 6) ?_)
            refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
            exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hk; omega)
        _ < 3 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf))
    have h6 := congrArg (fun P : L[X] => P.coeff 6) hP
    simp [Finset.sum_range_succ, coeff_X_pow, coeff_C_mul] at h6
  ·
    have hA3 : xCoeff ReeTag.G2.tag L g2Long 3 = 0 := xCoeff_three_eq_zero_of stringsLeTwoAt_G2_zero
    set δ : ℕ → L := fun k => T (xCoeff ReeTag.G2.tag L g2Long k)
      (Finsupp.single (Sum.inl g2Short) 1) (Sum.inr ⟨Pi.single g2Short 1, isRoot_single _ g2Short⟩)
      with hδ
    have hone : (1 : Module.End L (RootModule ReeTag.G2.tag L)) (Finsupp.single (Sum.inl g2Short) 1)
        (Sum.inr ⟨Pi.single g2Short 1, isRoot_single _ g2Short⟩) = 0 := by
      rw [Module.End.one_apply, Finsupp.single_eq_of_ne (by simp)]
    have heval : ∀ c : E, (C 2 * X ^ 3 ^ j - C (δ 1) * X - C (δ 2) * X ^ 2 : L[X]).eval
        (E.subtype c) = 0 := by
      intro c
      have e := hx g2Long g2Short c (c ^ 3 ^ j) (finiteExceptionalAut_odd_xElement_zero j c)
      rw [xOp_eq_quadratic_of hA3, hTadd, hTadd, hTsmul, hTsmul, hT1] at e
      have e' := congrArg (fun A : Module.End L (RootModule ReeTag.G2.tag L) =>
        A (Finsupp.single (Sum.inl g2Short) 1)
          (Sum.inr ⟨Pi.single g2Short 1, isRoot_single _ g2Short⟩)) e
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul, hone, zero_add, xOp_entry_inl] at e'
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, Subfield.coe_subtype, hδ]
      push_cast at e'
      linear_combination -e'
    have hlt : 3 ^ j < 3 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hjpos
    have hP := eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ E.subtype_injective heval (by
      rw [hcardE]
      refine lt_of_le_of_lt ?_ hlt
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
      · exact natDegree_C_mul_X_pow_le _ _
      · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by omega))
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega))
    have hc := congrArg (fun P : L[X] => P.coeff (3 ^ j)) hP
    have hn1 : 3 ^ j ≠ 1 := by omega
    have hn2 : 3 ^ j ≠ 2 := by omega
    simp [coeff_X_pow, coeff_C_mul, coeff_X, hn1.symm, hn2] at hc
    exact h2 hc

theorem two_le_pairBound_G2 : 2 ≤ pairBound .G2 := by
  have h := natAbs_le_pairBound (τ := .G2)
    (Sum.inr ⟨Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1, isRoot_single _ _⟩)
    (Sum.inl (⟨0, by decide⟩ : Fin Tag.G2.rank)) ⟨0, by decide⟩
  have e : (∑ k, Tag.G2.cartan ⟨0, by decide⟩ k *
      (Label.latticeWeight (Sum.inr ⟨Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1,
        isRoot_single _ _⟩ : Label .G2) k -
        Label.latticeWeight (Sum.inl (⟨0, by decide⟩ : Fin Tag.G2.rank) : Label .G2) k)) = 2 := by
    simp only [Label.latticeWeight, Pi.zero_apply, sub_zero]
    rw [Finset.sum_eq_single (⟨0, by decide⟩ : Fin Tag.G2.rank)
      (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_one]
    exact Tag.G2.cartan_self _
  rw [e] at h
  exact h

theorem false_of_conj_inner_odd
    {L : Type} [Field L] (h2 : (2 : L) ≠ 0) (E : Subfield L)
    [Finite E] [CharP E ReeTag.G2.prime] {f : ℕ} (hE : Nat.card E = 3 ^ f) (hf : 2 ≤ f)
    (h : ModGL ReeTag.G2.tag L) (g : adjointGroup ReeTag.G2.tag E) {j : ℕ}
    (hj : 2 * j + 1 < 2 * f) (α : MulAut (adjointGroup ReeTag.G2.tag E))
    (hα : ∀ x : adjointGroup ReeTag.G2.tag E, baseChangeGL E.subtype (α x : ModGL _ E) =
      h * baseChangeGL E.subtype (x : ModGL ReeTag.G2.tag E) * h⁻¹)
    (hgk : α = MulAut.conj g * ReeTag.G2.finiteExceptionalAut E ^ (2 * j + 1)) : False := by
  set g' : ModGL ReeTag.G2.tag L := baseChangeGL E.subtype (g : ModGL ReeTag.G2.tag E) with hg'
  refine false_of_conj_odd h2 E hE hf (g'⁻¹ * h) hj fun x => ?_
  have e : g'⁻¹ * h * baseChangeGL E.subtype (x : ModGL ReeTag.G2.tag E) * (g'⁻¹ * h)⁻¹ =
      g'⁻¹ * (h * baseChangeGL E.subtype (x : ModGL ReeTag.G2.tag E) * h⁻¹) * g' := by group
  rw [e, ← hα x, hgk, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, map_mul, map_mul, map_inv, hg']
  group

section Three

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 3] [Algebra (ZMod 3) L]
  [Algebra.IsAlgebraic (ZMod 3) L]

theorem le_adjointGroup_G2_three'
    (H : Subgroup (ModGL ReeTag.G2.tag L))
    (hCH : adjointGroup ReeTag.G2.tag L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat ReeTag.G2.tag P →
      evalMat (natMat ReeTag.G2.tag L (h : Module.End L (RootModule ReeTag.G2.tag L))) P = 0) :
    H ≤ adjointGroup ReeTag.G2.tag L := by
  intro h hh
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut (p := 3) (by decide) H hCH hH hh
  have : Finite (frobeniusFixedSubfield L 3 k) := finite_frobeniusFixedSubfield L 3 k hk
  have hcard : Nat.card (frobeniusFixedSubfield L 3 k) = 3 ^ k :=
    card_frobeniusFixedSubfield L 3 k hk
  have : CharP (frobeniusFixedSubfield L 3 k) ReeTag.G2.prime :=
    Subfield.charP (frobeniusFixedSubfield L 3 k) 3
  obtain ⟨⟨g, k'⟩, hgk, -⟩ := (G2_three_exact_automorphism_normal_form
    (Nat.one_le_iff_ne_zero.2 hk) (frobeniusFixedSubfield L 3 k) hcard).2.1 α
  have h2 : (2 : L) ≠ 0 := two_ne_zero_of_charP (p := 3) (by decide)
  rcases Nat.even_or_odd (k' : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  · refine mem_adjointGroup_of_inner_entrywise
      (hasQuadraticNode_G2 : HasQuadraticNode ReeTag.G2.tag) h2 _
      (frobeniusEquiv (frobeniusFixedSubfield L 3 k) ReeTag.G2.prime ^ j) t ht hCH hH hh g α hα
      fun x => ?_
    rw [hgk, hj, ← two_mul]
    exact conj_eq_of_even (fun c => frobeniusEquiv_def _ _ c) g j x
  · exfalso
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hU : Nat.card (frobeniusFixedSubfield L 3 k)ˣ = 2 := by
        rw [Nat.card_units, hcard, show k = 1 by omega]
        norm_num
      have h1 : t ^ (2 : ℤ) = 1 := by
        rw [zpow_ofNat, ← hU]
        exact pow_card_eq_one'
      exact ht 2 (by norm_num) (two_le_pairBound_G2 : 2 ≤ pairBound ReeTag.G2.tag) h1
    exact false_of_conj_inner_odd h2 _ hcard hk2 h g (j := j) (by have := k'.isLt; omega) α hα
      (by rw [hgk, hj])

theorem le_adjointGroup_G2_three
    (H : Subgroup (ModGL .G2 L)) (hCH : adjointGroup .G2 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .G2 P →
      evalMat (natMat .G2 L (h : Module.End L (RootModule .G2 L))) P = 0) :
    H ≤ adjointGroup .G2 L :=
  le_adjointGroup_G2_three' H hCH hH

end Three

section Odd

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_G2
    (hp2 : p ≠ 2) (H : Subgroup (ModGL .G2 L))
    (hCH : adjointGroup .G2 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .G2 P →
      evalMat (natMat .G2 L (h : Module.End L (RootModule .G2 L))) P = 0) :
    H ≤ adjointGroup .G2 L := by
  by_cases hp3 : p = 3
  · subst hp3
    exact le_adjointGroup_G2_three H hCH hH
  · exact le_adjointGroup_G2_of_ne_three hp2 hp3 H hCH hH

end Odd

end CFSG.TauCetiBridge.BigCell
