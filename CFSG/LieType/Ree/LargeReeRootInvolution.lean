module

public import CFSG.LieType.Ree.G2PrimeFieldWords
public import CFSG.LieType.Ree.LargeReeB2

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section CharTwo

variable {τ : Tag} {K : Type} [Field K]

theorem weylElt_conj_pinnedX_of_two_eq_zero
    (h2 : (2 : K) = 0) (i : Fin τ.rank)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : K) :
    weylElt τ K i 1 * pinnedX τ K β c * (weylElt τ K i 1)⁻¹ = pinnedX τ K (reflect τ i β) c := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hβ
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 hsq)
  rw [h, hε1, one_mul]

theorem prod_weylElt_conj_pinnedX_of_two_eq_zero
    (h2 : (2 : K) = 0) :
    ∀ (w : List ℕ) {β : Fin τ.rank → ℤ}, IsRoot τ β → ∀ c : K,
      ((w.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod * pinnedX τ K β c *
          (((w.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod)⁻¹ =
        pinnedX τ K (w.foldl (fun v i => reflect τ (τ.idx i) v) β) c
  | [], _, _, c => by simp
  | i :: w, β, hβ, c => by
    have ih := prod_weylElt_conj_pinnedX_of_two_eq_zero h2 w (IsRoot.reflect (τ.idx i) hβ) c
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, mul_inv_rev,
      List.foldl_cons, ← ih, ← weylElt_conj_pinnedX_of_two_eq_zero h2 (τ.idx i) hβ c]
    group

theorem pinnedX_eq_of_two_eq_zero
    (h2 : (2 : K) = 0) (α : Fin τ.rank → ℤ) (c : K) :
    pinnedX τ K α c = pinnedWeyl τ K α * xUnit τ K (pinnedData τ α).1 c * (pinnedWeyl τ K α)⁻¹ := by
  have hneg : (-1 : K) = 1 := by linear_combination -h2
  rw [pinnedX]
  rcases pinnedSign_eq τ α with h | h <;> rw [h]
  · rw [one_smul]
  · rw [neg_smul, one_smul, show -c = c by linear_combination -c * h2]

end CharTwo

namespace ReeTag

theorem quadForm_eq_iform (t : ReeTag) (v : Fin t.tag.rank → ℤ) :
    t.quadForm v = Steinberg.Adjoint.iform v v := by
  simp only [quadForm, Steinberg.Adjoint.iform, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc]

theorem quadForm_reflect
    (t : ReeTag) (i : Fin t.tag.rank) (v : Fin t.tag.rank → ℤ) :
    t.quadForm (reflect t.tag i v) = t.quadForm v := by
  rw [quadForm_eq_iform, quadForm_eq_iform, Steinberg.Adjoint.iform_reflect]

theorem quadForm_foldl_reflect
    (t : ReeTag) :
    ∀ (w : List ℕ) (v : Fin t.tag.rank → ℤ),
      t.quadForm (w.foldl (fun v i => reflect t.tag (t.tag.idx i) v) v) = t.quadForm v
  | [], _ => rfl
  | i :: w, v => by rw [List.foldl_cons, quadForm_foldl_reflect t w, quadForm_reflect]

theorem dualRoot_foldl_reflect
    (t : ReeTag) :
    ∀ (w : List ℕ) {β : Fin t.tag.rank → ℤ}, IsRoot t.tag β →
      (w.map fun i => ((t.perm (t.tag.idx i) : Fin t.tag.rank) : ℕ)).foldl
          (fun v i => reflect t.tag (t.tag.idx i) v) (t.dualRoot β) =
        t.dualRoot (w.foldl (fun v i => reflect t.tag (t.tag.idx i) v) β)
  | [], _, _ => rfl
  | i :: w, β, hβ => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, idx_perm, ← dualRoot_reflect hβ,
      dualRoot_foldl_reflect t w (IsRoot.reflect _ hβ)]

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] in
theorem F4_two_eq_zero : (2 : K) = 0 := by
  have h := CharP.cast_eq_zero K F4.prime
  exact_mod_cast h

theorem finiteReeAut_pinnedX_F4
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : K) :
    F4.finiteReeAut K a ⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
      ⟨pinnedX F4.tag K (F4.dualRoot α) (c ^ F4.relationExponent a (pinnedData F4.tag α).1),
        pinnedX_mem_adjointGroup _ _⟩ := by
  have h2 := F4_two_eq_zero (K := K)
  set j := (pinnedData F4.tag α).1
  set w := (pinnedData F4.tag α).2.1
  have hdec : (⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag K) =
      wordWeylElement w * xElement j c * (wordWeylElement w)⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordWeylElement]
    rw [pinnedX_eq_of_two_eq_zero h2]
    rfl
  rw [hdec, map_mul, map_mul, map_inv, finiteReeAut_wordWeylElement, finiteReeAut_xElement]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordWeylElement]
  rw [show (xElement (F4.perm j) (c ^ F4.relationExponent a j) : ModGL F4.tag K) =
      pinnedX F4.tag K (Pi.single (F4.perm j) 1) (c ^ F4.relationExponent a j) from
        (pinnedX_single F4.tag K _ _).symm,
    prod_weylElt_conj_pinnedX_of_two_eq_zero h2 _ (isRoot_single _ _), ← dualRoot_single,
    dualRoot_foldl_reflect F4 w (isRoot_single _ _), foldl_reflect_pinnedData hα]

theorem quadForm_pinnedData
    {t : ReeTag} {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    t.quadForm α = t.quadForm (Pi.single (pinnedData t.tag α).1 1) := by
  conv_lhs => rw [← foldl_reflect_pinnedData hα]
  exact quadForm_foldl_reflect t _ _

theorem F4_quadForm_single : ∀ j : Fin F4.tag.rank,
    F4.quadForm (Pi.single j 1) = if j ∈ F4.longSet then 4 else 2 := by
  decide

theorem relationExponent_pinnedData_F4
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) :
    (α ∈ F4.longRoots → F4.relationExponent a (pinnedData F4.tag α).1 = 2 ^ a) ∧
      (α ∈ F4.shortRoots → F4.relationExponent a (pinnedData F4.tag α).1 = 2 * 2 ^ a) := by
  have hq := quadForm_pinnedData hα
  rw [F4_quadForm_single] at hq
  refine ⟨fun hl => ?_, fun hs => ?_⟩
  · have h4 : F4.quadForm α = 4 := (lengthParam_eq_prime_iff (t := F4)).1 hl.2
    rw [relationExponent, ite_eq_left ?_]
    · rfl
    · by_contra h
      rw [ite_eq_right h] at hq
      omega
  · have h2 : F4.quadForm α = 2 := (lengthParam_eq_one_iff (t := F4)).1 hs.2
    rw [relationExponent, ite_eq_right ?_, pow_succ, mul_comm]
    · rfl
    · intro h
      rw [ite_eq_left h] at hq
      omega

end Aut

theorem large_Ree_field_powers (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ ρ σ : K ≃+* K, (∀ c, ρ c = c ^ 2 ^ a) ∧ (∀ c, σ c = c ^ (2 * 2 ^ a)) ∧
      ρ.trans σ = RingEquiv.refl K ∧ σ.trans ρ = RingEquiv.refl K ∧ (∀ c, σ (σ c) = c ^ 2) ∧
      (1 ≤ a → (σ : RingAut K) ^ 4 ≠ 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have hpowq : ∀ x : K, x ^ 2 ^ (2 * a + 1) = x := fun x => by
    rw [← hcard, FiniteField.pow_card]
  set ρ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 a)
    (iterateFrobenius K 2 a).injective.bijective_of_finite with hρ
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 (a + 1))
    (iterateFrobenius K 2 (a + 1)).injective.bijective_of_finite with hσ
  have hρx : ∀ x, ρ x = x ^ 2 ^ a := fun x => iterateFrobenius_def (p := 2) a x
  have hσx : ∀ x, σ x = x ^ (2 * 2 ^ a) := fun x => by
    rw [← pow_succ']
    exact iterateFrobenius_def (p := 2) (a + 1) x
  have hexp : 2 ^ a * (2 * 2 ^ a) = 2 ^ (2 * a + 1) := by ring
  refine ⟨ρ, σ, hρx, hσx, ?_, ?_, fun x => ?_, fun ha hσ4 => ?_⟩
  · refine RingEquiv.ext fun x => ?_
    rw [RingEquiv.trans_apply, hσx, hρx, ← pow_mul, hexp, hpowq, RingEquiv.refl_apply]
  · refine RingEquiv.ext fun x => ?_
    rw [RingEquiv.trans_apply, hρx, hσx, ← pow_mul, mul_comm, hexp, hpowq,
      RingEquiv.refl_apply]
  · rw [hσx, hσx, ← pow_mul, show 2 * 2 ^ a * (2 * 2 ^ a) = 2 ^ (2 * a + 1) * 2 by ring,
      pow_mul, hpowq]
  ·
    have hσσ : ∀ x : K, σ (σ x) = x ^ 2 := fun x => by
      rw [hσx, hσx, ← pow_mul, show 2 * 2 ^ a * (2 * 2 ^ a) = 2 ^ (2 * a + 1) * 2 by ring,
        pow_mul, hpowq]
    have h4 : ∀ x : K, x ^ 4 = x := fun x => by
      have h := congrArg (fun e : RingAut K => e x) hσ4
      simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] at h
      rw [hσσ, hσσ, ← pow_mul] at h
      exact h
    have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.X ^ 4 - Polynomial.X : Polynomial K) (f := id) Function.injective_id
      (fun x => by simp [h4])
      (by
        rw [FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num : 1 < 4), hcard]
        calc 4 < 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num : 1 < 4)
    rw [hP, Polynomial.natDegree_zero] at hdeg
    omega

@[expose] def largeReeRootF (i : Fin 4) : Fin F4.tag.rank → ℤ :=
  largeReeRoot i

theorem largeReeRoot_duality :
    F4.dualRoot (largeReeRootF 0) = largeReeRootF 1 ∧
      F4.dualRoot (largeReeRootF 1) = largeReeRootF 0 ∧
      F4.dualRoot (largeReeRootF 2) = largeReeRootF 3 ∧
      F4.dualRoot (largeReeRootF 3) = largeReeRootF 2 ∧
      F4.quadForm (largeReeRootF 0) = 2 ∧ F4.quadForm (largeReeRootF 1) = 4 ∧
      F4.quadForm (largeReeRootF 2) = 2 ∧ F4.quadForm (largeReeRootF 3) = 4 := by
  decide

theorem large_Ree_root_parameter_involution
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ ρ σ : K ≃+* K, (∀ c, ρ c = c ^ 2 ^ a) ∧ (∀ c, σ c = c ^ (2 * 2 ^ a)) ∧
      ρ.trans σ = RingEquiv.refl K ∧ σ.trans ρ = RingEquiv.refl K ∧ (∀ c, σ (σ c) = c ^ 2) ∧
      (∀ α ∈ F4.longRoots, ∀ c : K,
        F4.finiteReeAut K a ⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
          ⟨pinnedX F4.tag K (F4.dualRoot α) (ρ c), pinnedX_mem_adjointGroup _ _⟩) ∧
      (∀ α ∈ F4.shortRoots, ∀ c : K,
        F4.finiteReeAut K a ⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
          ⟨pinnedX F4.tag K (F4.dualRoot α) (σ c), pinnedX_mem_adjointGroup _ _⟩) ∧
      (∀ c : K,
        F4.finiteReeAut K a ⟨largeReeX K 0 c, pinnedX_mem_adjointGroup _ c⟩ =
          ⟨largeReeX K 1 (σ c), pinnedX_mem_adjointGroup _ _⟩ ∧
        F4.finiteReeAut K a ⟨largeReeX K 1 c, pinnedX_mem_adjointGroup _ c⟩ =
          ⟨largeReeX K 0 (ρ c), pinnedX_mem_adjointGroup _ _⟩ ∧
        F4.finiteReeAut K a ⟨largeReeX K 2 c, pinnedX_mem_adjointGroup _ c⟩ =
          ⟨largeReeX K 3 (σ c), pinnedX_mem_adjointGroup _ _⟩ ∧
        F4.finiteReeAut K a ⟨largeReeX K 3 c, pinnedX_mem_adjointGroup _ c⟩ =
          ⟨largeReeX K 2 (ρ c), pinnedX_mem_adjointGroup _ _⟩) ∧
      (1 ≤ a → (σ : RingAut K) ^ 4 ≠ 1) := by
  obtain ⟨ρ, σ, hρ, hσ, h1, h2, h3, h4⟩ := large_Ree_field_powers a K hK
  have hlong : ∀ α ∈ F4.longRoots, ∀ c : K,
      F4.finiteReeAut K a ⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
        ⟨pinnedX F4.tag K (F4.dualRoot α) (ρ c), pinnedX_mem_adjointGroup _ _⟩ := by
    intro α hα c
    rw [finiteReeAut_pinnedX_F4 hα.1, (relationExponent_pinnedData_F4 hα.1).1 hα, hρ]
  have hshort : ∀ α ∈ F4.shortRoots, ∀ c : K,
      F4.finiteReeAut K a ⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
        ⟨pinnedX F4.tag K (F4.dualRoot α) (σ c), pinnedX_mem_adjointGroup _ _⟩ := by
    intro α hα c
    rw [finiteReeAut_pinnedX_F4 hα.1, (relationExponent_pinnedData_F4 hα.1).2 hα, hσ]
  obtain ⟨d0, d1, d2, d3, q0, q1, q2, q3⟩ := largeReeRoot_duality
  have hr : ∀ i : Fin 4, IsRoot F4.tag (largeReeRootF i) := fun i => (largeReeRoot_pos i).1
  have hl : ∀ i : Fin 4, F4.quadForm (largeReeRootF i) = 4 → largeReeRootF i ∈ F4.longRoots :=
    fun i h => ⟨hr i, (lengthParam_eq_prime_iff (t := F4)).2 h⟩
  have hs : ∀ i : Fin 4, F4.quadForm (largeReeRootF i) = 2 → largeReeRootF i ∈ F4.shortRoots :=
    fun i h => ⟨hr i, (lengthParam_eq_one_iff (t := F4)).2 h⟩
  refine ⟨ρ, σ, hρ, hσ, h1, h2, h3, hlong, hshort, fun c => ⟨?_, ?_, ?_, ?_⟩, h4⟩
  · have h := hshort _ (hs 0 q0) c
    rw [d0] at h
    exact h
  · have h := hlong _ (hl 1 q1) c
    rw [d1] at h
    exact h
  · have h := hshort _ (hs 2 q2) c
    rw [d2] at h
    exact h
  · have h := hlong _ (hl 3 q3) c
    rw [d3] at h
    exact h

end ReeTag

end CFSG.LieType.Ree
