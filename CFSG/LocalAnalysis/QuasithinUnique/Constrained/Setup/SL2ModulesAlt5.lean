module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

section Weights

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def weight (x : Ω → ZMod 2) : ℕ := (Finset.univ.filter fun ω => x ω ≠ 0).card

omit [DecidableEq Ω] in
theorem sum_eq_weight (x : Ω → ZMod 2) : ∑ ω, x ω = (weight x : ZMod 2) := by
  have h1 : ∀ ω, x ω = if x ω ≠ 0 then (1 : ZMod 2) else 0 := fun ω => by
    rcases zmod2_cases (x ω) with h | h <;> simp [h]
  conv_lhs => rw [Finset.sum_congr rfl (fun ω _ => h1 ω)]
  rw [Finset.sum_boole]
  rfl

omit [DecidableEq Ω] in
theorem mem_evenWeight_iff (x : Ω → ZMod 2) : x ∈ evenWeight Ω ↔ Even (weight x) := by
  show ∑ ω, x ω = 0 ↔ _
  rw [sum_eq_weight]
  exact ZMod.natCast_eq_zero_iff_even

omit [DecidableEq Ω] in
theorem weight_permAct (σ : Equiv.Perm Ω) (x : Ω → ZMod 2) : weight (permAct σ x) = weight x := by
  unfold weight
  refine Finset.card_bij (fun ω _ => σ.symm ω) ?_ ?_ ?_
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩
  · intro a _ b _ h
    exact σ.symm.injective h
  · intro ω hω
    refine ⟨σ ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    show x (σ.symm (σ ω)) ≠ 0
    rw [Equiv.symm_apply_apply]
    exact (Finset.mem_filter.mp hω).2

omit [DecidableEq Ω] in
theorem weight_zero_iff {x : Ω → ZMod 2} : weight x = 0 ↔ x = 0 := by
  unfold weight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext ω
    by_contra hω
    exact h (Finset.mem_univ ω) hω
  · intro h ω _
    simp [h]

theorem weight_delta_add_delta {a b : Ω} (hab : a ≠ b) : weight (delta a + delta b) = 2 := by
  unfold weight
  have : (Finset.univ.filter fun ω => (delta a + delta b) ω ≠ 0) = {a, b} := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      by_contra hne
      push Not at hne
      apply h
      simp [delta, hne.1, hne.2]
    · rintro (rfl | rfl)
      · simp [delta, hab]
      · simp [delta, Ne.symm hab]
  rw [this, Finset.card_pair hab]

theorem eq_delta_add_delta_of_weight_two {x : Ω → ZMod 2} (hx : weight x = 2) :
    ∃ a b, a ≠ b ∧ x = delta a + delta b := by
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hx
  refine ⟨a, b, hab, ?_⟩
  funext ω
  have hL : x ω ≠ 0 ↔ ω = a ∨ ω = b := by
    have := congrArg (fun S : Finset Ω => ω ∈ S) hS
    simpa using this
  by_cases hωa : ω = a
  · have h1 : x ω = 1 := by
      rcases zmod2_cases (x ω) with h0 | h0
      · exact absurd h0 ((hL.mpr (Or.inl hωa)))
      · exact h0
    subst hωa
    simp [delta, hab, h1]
  by_cases hωb : ω = b
  · have h1 : x ω = 1 := by
      rcases zmod2_cases (x ω) with h0 | h0
      · exact absurd h0 ((hL.mpr (Or.inr hωb)))
      · exact h0
    subst hωb
    simp [delta, hωa, h1]
  · have h0 : x ω = 0 := by
      by_contra hne
      rcases hL.mp hne with h | h
      · exact hωa h
      · exact hωb h
    simp [delta, hωa, hωb, h0]

theorem weight_one_add_delta (h5 : Fintype.card Ω = 5) (a : Ω) :
    weight ((fun _ : Ω => (1 : ZMod 2)) + delta a) = 4 := by
  unfold weight
  have : (Finset.univ.filter fun ω => ((fun _ : Ω => (1 : ZMod 2)) + delta a) ω ≠ 0) =
      Finset.univ.erase a := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    by_cases ha : ω = a
    · subst ha
      simp [delta]
      decide
    · simp [delta, ha]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h5]

theorem eq_one_add_delta_of_weight_four (h5 : Fintype.card Ω = 5) {x : Ω → ZMod 2}
    (hx : weight x = 4) : ∃ a, x = (fun _ : Ω => (1 : ZMod 2)) + delta a := by
  have hz : (Finset.univ.filter fun ω => x ω = 0).card = 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω))
      (fun ω => x ω ≠ 0)
    simp only [not_not] at h1
    rw [Finset.card_univ, h5] at h1
    have : (Finset.univ.filter fun ω => x ω ≠ 0).card = 4 := hx
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hz
  refine ⟨a, ?_⟩
  funext ω
  have hL : x ω = 0 ↔ ω = a := by
    have := congrArg (fun S : Finset Ω => ω ∈ S) ha
    simpa using this
  by_cases hωa : ω = a
  · have h0 := hL.mpr hωa
    subst hωa
    simp [delta, h0]
    decide
  · have h1 : x ω = 1 := by
      rcases zmod2_cases (x ω) with h | h
      · exact absurd (hL.mp h) hωa
      · exact h
    simp [delta, hωa, h1]

theorem alt_two_transitive (h5 : Fintype.card Ω = 5) {a b c d : Ω} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ ∈ alternatingGroup Ω, σ a = c ∧ σ b = d := by
  have h5' : Nat.card Ω = 5 := by rw [Nat.card_eq_fintype_card, h5]
  have h3 : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω (Nat.card Ω - 2) :=
    alternatingGroup.isMultiplyPretransitive Ω
  rw [h5'] at h3
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 3) (by norm_num)
      (by rw [h5']; norm_num)
  obtain ⟨g, hg1, hg2⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab hcd
  exact ⟨g.1, g.2, hg1, hg2⟩

theorem alt_transitive (h5 : Fintype.card Ω = 5) (a c : Ω) :
    ∃ σ ∈ alternatingGroup Ω, σ a = c := by
  have hΩ2 : ∀ a : Ω, ∃ b : Ω, b ≠ a := fun a => by
    by_contra hcon
    push Not at hcon
    have : Fintype.card Ω ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun x y => by rw [hcon x, hcon y])
    omega
  obtain ⟨b, hb⟩ := hΩ2 a
  obtain ⟨d, hd⟩ := hΩ2 c
  obtain ⟨σ, hσ, h1, -⟩ := alt_two_transitive h5 hb.symm hd.symm
  exact ⟨σ, hσ, h1⟩

omit [DecidableEq Ω] in
theorem weight_cases (h5 : Fintype.card Ω = 5) {x : Ω → ZMod 2} (hx : x ∈ evenWeight Ω) :
    weight x = 0 ∨ weight x = 2 ∨ weight x = 4 := by
  obtain ⟨m, hm⟩ := (mem_evenWeight_iff x).mp hx
  have : weight x ≤ 5 := h5 ▸ Finset.card_le_univ _
  omega

theorem exists_alt_of_weight_eq (h5 : Fintype.card Ω = 5) {x y : Ω → ZMod 2}
    (hx : x ∈ evenWeight Ω) (hw : weight x = weight y) :
    ∃ σ ∈ alternatingGroup Ω, permAct σ x = y := by
  rcases weight_cases h5 hx with h0 | h2 | h4
  · refine ⟨1, one_mem _, ?_⟩
    have hy0 : weight y = 0 := hw.symm.trans h0
    rw [weight_zero_iff.mp h0, weight_zero_iff.mp hy0]
    rfl
  · obtain ⟨a, b, hab, rfl⟩ := eq_delta_add_delta_of_weight_two h2
    obtain ⟨c, d, hcd, rfl⟩ := eq_delta_add_delta_of_weight_two (hw ▸ h2)
    obtain ⟨σ, hσ, h1, h2'⟩ := alt_two_transitive h5 hab hcd
    exact ⟨σ, hσ, by rw [permAct_add, permAct_delta, permAct_delta, h1, h2']⟩
  · obtain ⟨a, rfl⟩ := eq_one_add_delta_of_weight_four h5 h4
    obtain ⟨c, rfl⟩ := eq_one_add_delta_of_weight_four h5 (hw ▸ h4)
    obtain ⟨σ, hσ, h1⟩ := alt_transitive h5 a c
    exact ⟨σ, hσ, by rw [permAct_add, permAct_one, permAct_delta, h1]⟩

end Weights

section Counting

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem weight_comp_equiv {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (e : Ω ≃ Ω')
    (x : Ω' → ZMod 2) : weight (fun ω => x (e ω)) = weight x := by
  unfold weight
  exact Finset.card_bij (fun ω _ => e ω) (fun ω hω => by simpa using hω)
    (fun a _ b _ h => e.injective h)
    (fun ω' hω' => ⟨e.symm ω', by simpa using hω', by simp⟩)

theorem natCard_weight_class (h5 : Fintype.card Ω = 5) (k : ℕ) :
    Nat.card {x : Ω → ZMod 2 // weight x = k} = Nat.card {x : Fin 5 → ZMod 2 // weight x = k} := by
  let e : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq h5
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl (ZMod 2))) fun x => ?_)
  show weight x = k ↔ weight (fun i => x (e.symm i)) = k
  rw [weight_comp_equiv e.symm x]

theorem natCard_weight_zero (h5 : Fintype.card Ω = 5) :
    Nat.card {x : Ω → ZMod 2 // weight x = 0} = 1 := by
  rw [natCard_weight_class h5, Nat.card_eq_fintype_card]
  decide

theorem natCard_weight_two (h5 : Fintype.card Ω = 5) :
    Nat.card {x : Ω → ZMod 2 // weight x = 2} = 10 := by
  rw [natCard_weight_class h5, Nat.card_eq_fintype_card]
  decide

theorem natCard_weight_four (h5 : Fintype.card Ω = 5) :
    Nat.card {x : Ω → ZMod 2 // weight x = 4} = 5 := by
  rw [natCard_weight_class h5, Nat.card_eq_fintype_card]
  decide

end Counting

section Normalizer

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem unit_inv_val_apply {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (u : (Module.End R M)ˣ) (x : M) : (u⁻¹).val (u.val x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

@[expose] def permU (σ : Equiv.Perm Ω) : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ where
  val := (permLin σ).restrict (fun _ hx => permAct_mem_evenWeight σ hx)
  inv := (permLin σ⁻¹).restrict (fun _ hx => permAct_mem_evenWeight σ⁻¹ hx)
  val_inv := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show permAct σ (permAct σ⁻¹ (x : Ω → ZMod 2)) = x
    rw [← permAct_mul, mul_inv_cancel]
    rfl
  inv_val := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show permAct σ⁻¹ (permAct σ (x : Ω → ZMod 2)) = x
    rw [← permAct_mul, inv_mul_cancel]
    rfl

omit [DecidableEq Ω] in
theorem permU_apply (σ : Equiv.Perm Ω) (x : ↥(evenWeight Ω)) :
    (((permU σ).val x : ↥(evenWeight Ω)) : Ω → ZMod 2) = permAct σ (x : Ω → ZMod 2) := rfl

omit [DecidableEq Ω] in
theorem permU_mul (σ τ : Equiv.Perm Ω) : permU (σ * τ) = permU σ * permU τ := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show permAct (σ * τ) (x : Ω → ZMod 2) = permAct σ (permAct τ (x : Ω → ZMod 2))
  exact permAct_mul σ τ _

theorem vvec_mem (h5 : Fintype.card Ω = 5) (ω : Ω) :
    (fun _ : Ω => (1 : ZMod 2)) + delta ω ∈ evenWeight Ω := by
  rw [mem_evenWeight_iff, weight_one_add_delta h5]
  decide

@[expose] def vvec (h5 : Fintype.card Ω = 5) (ω : Ω) : ↥(evenWeight Ω) :=
  ⟨(fun _ : Ω => (1 : ZMod 2)) + delta ω, vvec_mem h5 ω⟩

theorem permU_vvec (h5 : Fintype.card Ω = 5) (σ : Equiv.Perm Ω) (ω : Ω) :
    (permU σ).val (vvec h5 ω) = vvec h5 (σ ω) := by
  apply Subtype.ext
  show permAct σ ((fun _ : Ω => (1 : ZMod 2)) + delta ω) = _
  rw [permAct_add, permAct_one, permAct_delta]
  rfl

theorem permU_injective (h5 : Fintype.card Ω = 5) :
    Function.Injective (permU : Equiv.Perm Ω → (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ) := by
  intro σ τ h
  ext ω
  have h1 := congrArg (fun u : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ =>
    ((u.val (vvec h5 ω) : ↥(evenWeight Ω)) : Ω → ZMod 2)) h
  simp only [permU_vvec] at h1
  have h2 := congrFun h1 (σ ω)
  by_contra hne
  have hne' : σ ω ≠ τ ω := hne
  simp [vvec, delta, hne'] at h2

omit [DecidableEq Ω] in
theorem natCard_cls (_h5 : Fintype.card Ω = 5) (k : ℕ) (hk : Even k) :
    Nat.card {z : ↥(evenWeight Ω) // weight (z : Ω → ZMod 2) = k} =
      Nat.card {x : Ω → ZMod 2 // weight x = k} := by
  refine Nat.card_congr
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun x => ⟨⟨x.1, (mem_evenWeight_iff _).mpr (by rw [x.2]; exact hk)⟩, x.2⟩
      left_inv := fun z => rfl
      right_inv := fun x => rfl }

theorem normalizer_conj_surj (h5 : Fintype.card Ω = 5)
    (h : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ)
    (hN : ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω, h * permU σ * h⁻¹ = permU σ') :
    ∀ σ ∈ alternatingGroup Ω, ∃ σ'' ∈ alternatingGroup Ω, h⁻¹ * permU σ * h = permU σ'' := by
  classical
  choose! c hcA hc using hN
  let c' : ↥(alternatingGroup Ω) → ↥(alternatingGroup Ω) := fun σ => ⟨c σ.1, hcA σ.1 σ.2⟩
  have hinj : Function.Injective c' := by
    intro σ τ hστ
    have h1 : c σ.1 = c τ.1 := congrArg Subtype.val hστ
    have h2 : h * permU σ.1 * h⁻¹ = h * permU τ.1 * h⁻¹ := by
      rw [hc σ.1 σ.2, hc τ.1 τ.2, h1]
    have h3 : permU σ.1 = permU τ.1 := by
      have := mul_right_cancel h2
      exact mul_left_cancel this
    exact Subtype.ext (permU_injective h5 h3)
  have hsurj : Function.Surjective c' := Finite.injective_iff_surjective.mp hinj
  intro σ hσ
  obtain ⟨τ, hτ⟩ := hsurj ⟨σ, hσ⟩
  refine ⟨τ.1, τ.2, ?_⟩
  have h4 : c τ.1 = σ := congrArg Subtype.val hτ
  have h5' : h * permU τ.1 * h⁻¹ = permU σ := by rw [hc τ.1 τ.2, h4]
  calc h⁻¹ * permU σ * h = h⁻¹ * (h * permU τ.1 * h⁻¹) * h := by rw [h5']
    _ = permU τ.1 := by group

theorem weight_constant_on_class (h5 : Fintype.card Ω = 5)
    (u : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ)
    (hu : ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω, u * permU σ * u⁻¹ = permU σ')
    (y z : ↥(evenWeight Ω)) (hyz : weight (y : Ω → ZMod 2) = weight (z : Ω → ZMod 2)) :
    weight ((u.val y : ↥(evenWeight Ω)) : Ω → ZMod 2) =
      weight ((u.val z : ↥(evenWeight Ω)) : Ω → ZMod 2) := by
  obtain ⟨σ, hσ, hσz⟩ := exists_alt_of_weight_eq h5 y.2 hyz
  obtain ⟨σ', hσ', hσ'⟩ := hu σ hσ
  have hz : z = (permU σ).val y := Subtype.ext hσz.symm
  have h1 : u.val z = (permU σ').val (u.val y) := by
    rw [hz, ← hσ']
    show u.val ((permU σ).val y) = (u * permU σ * u⁻¹).val (u.val y)
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (u⁻¹).val u.val, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply]
  rw [h1, permU_apply, weight_permAct]

theorem normalizer_weight_two (h5 : Fintype.card Ω = 5)
    (u : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ)
    (hu : ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω, u * permU σ * u⁻¹ = permU σ')
    (x : ↥(evenWeight Ω)) (hx : weight (x : Ω → ZMod 2) = 2) :
    weight ((u.val x : ↥(evenWeight Ω)) : Ω → ZMod 2) = 2 := by
  have hux := (u.val x).2
  rcases weight_cases h5 hux with h0 | h2 | h4
  · exfalso
    have : u.val x = 0 := Subtype.ext (weight_zero_iff.mp h0)
    have hx0 : x = 0 := by
      have := congrArg (u⁻¹).val this
      simpa [← Module.End.mul_apply, ← Units.val_mul] using this
    rw [hx0] at hx
    simp [weight] at hx
  · exact h2
  · exfalso
    have hinj : Function.Injective (fun z : {z : ↥(evenWeight Ω) // weight (z : Ω → ZMod 2) = 2} =>
        (⟨u.val z.1, by rw [weight_constant_on_class h5 u hu z.1 x (z.2.trans hx.symm), h4]⟩ :
          {z : ↥(evenWeight Ω) // weight (z : Ω → ZMod 2) = 4})) := by
      intro a b hab
      apply Subtype.ext
      have h1 : u.val a.1 = u.val b.1 := congrArg (fun p : {z : ↥(evenWeight Ω) //
        weight (z : Ω → ZMod 2) = 4} => (p.1 : ↥(evenWeight Ω))) hab
      have h' : (u⁻¹).val (u.val a.1) = (u⁻¹).val (u.val b.1) := by rw [h1]
      rwa [unit_inv_val_apply, unit_inv_val_apply] at h'
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [natCard_cls h5 2 (by decide), natCard_cls h5 4 (by decide), natCard_weight_two h5,
      natCard_weight_four h5] at hle
    omega

theorem normalizer_weight (h5 : Fintype.card Ω = 5)
    (h : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ)
    (hN : ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω, h * permU σ * h⁻¹ = permU σ')
    (x : ↥(evenWeight Ω)) :
    weight ((h.val x : ↥(evenWeight Ω)) : Ω → ZMod 2) = weight (x : Ω → ZMod 2) := by
  have hN' := normalizer_conj_surj h5 h hN
  have hN'' : ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω,
      h⁻¹ * permU σ * (h⁻¹)⁻¹ = permU σ' := by
    intro σ hσ
    obtain ⟨σ'', h1, h2⟩ := hN' σ hσ
    exact ⟨σ'', h1, by simpa using h2⟩
  have hinv : ∀ y : ↥(evenWeight Ω), (h⁻¹).val (h.val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  rcases weight_cases h5 x.2 with h0 | h2 | h4
  · have hx0 : x = 0 := Subtype.ext (weight_zero_iff.mp h0)
    rw [hx0, map_zero]
  · rw [h2]
    exact normalizer_weight_two h5 h hN x h2
  · rw [h4]
    rcases weight_cases h5 (h.val x).2 with h0' | h2' | h4'
    · exfalso
      have hz : h.val x = 0 := Subtype.ext (weight_zero_iff.mp h0')
      have : x = 0 := by rw [← hinv x, hz, map_zero]
      rw [this] at h4
      simp [weight] at h4
    · exfalso
      have := normalizer_weight_two h5 h⁻¹ hN'' (h.val x) h2'
      rw [hinv x, h4] at this
      omega
    · exact h4'

theorem alternating_five_deleted_normalizer_orbits (h5 : Fintype.card Ω = 5)
    (H : Subgroup (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ)
    (hSH : ∀ σ ∈ alternatingGroup Ω, permU σ ∈ H)
    (hHN : ∀ h ∈ H, ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω,
      h * permU σ * h⁻¹ = permU σ') :
    (∀ x y : ↥(evenWeight Ω), (∃ h ∈ H, h.val x = y) ↔
        weight (y : Ω → ZMod 2) = weight (x : Ω → ZMod 2)) ∧
      Nat.card {x : Ω → ZMod 2 // weight x = 0} = 1 ∧
      Nat.card {x : Ω → ZMod 2 // weight x = 2} = 10 ∧
      Nat.card {x : Ω → ZMod 2 // weight x = 4} = 5 ∧
      ∀ x : ↥(evenWeight Ω), ¬ (4 ∣ Nat.card {y : ↥(evenWeight Ω) // ∃ h ∈ H, h.val x = y}) := by
  have horb : ∀ x y : ↥(evenWeight Ω), (∃ h ∈ H, h.val x = y) ↔
      weight (y : Ω → ZMod 2) = weight (x : Ω → ZMod 2) := by
    intro x y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact normalizer_weight h5 h (hHN h hh) x
    · intro hxy
      obtain ⟨σ, hσ, hσx⟩ := exists_alt_of_weight_eq h5 x.2 hxy.symm
      exact ⟨permU σ, hSH σ hσ, Subtype.ext hσx⟩
  refine ⟨horb, natCard_weight_zero h5, natCard_weight_two h5, natCard_weight_four h5, ?_⟩
  intro x hdiv
  have hcard : Nat.card {y : ↥(evenWeight Ω) // ∃ h ∈ H, h.val x = y} =
      Nat.card {y : ↥(evenWeight Ω) // weight (y : Ω → ZMod 2) = weight (x : Ω → ZMod 2)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => horb x y)
  rw [hcard] at hdiv
  rcases weight_cases h5 x.2 with h0 | h2 | h4
  · rw [h0, natCard_cls h5 0 (by decide), natCard_weight_zero h5] at hdiv
    omega
  · rw [h2, natCard_cls h5 2 (by decide), natCard_weight_two h5] at hdiv
    omega
  · rw [h4, natCard_cls h5 4 (by decide), natCard_weight_four h5] at hdiv
    omega

theorem vvec_injective (h5 : Fintype.card Ω = 5) : Function.Injective (vvec h5) := by
  intro a b hab
  have h1 := congrFun (congrArg Subtype.val hab) a
  by_contra hne
  simp [vvec, delta, hne] at h1

theorem span_vvec (h5 : Fintype.card Ω = 5) :
    Submodule.span (ZMod 2) (Set.range (vvec h5)) = ⊤ := by
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨o⟩ := this
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ L ∈ Finset.univ.erase o, (x : Ω → ZMod 2) L • (vvec h5 L + vvec h5 o) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, Submodule.coe_add]
    conv_lhs => rw [eq_sum_pairs o x.2]
    refine Finset.sum_congr rfl fun L _ => ?_
    congr 1
    funext ω
    simp only [vvec, Pi.add_apply, delta]
    symm
    linear_combination zmod2_two
  rw [hx]
  exact Submodule.sum_mem _ fun L _ => Submodule.smul_mem _ _
    (Submodule.add_mem _ (Submodule.subset_span ⟨L, rfl⟩) (Submodule.subset_span ⟨o, rfl⟩))

theorem deleted_five_normalizer (h5 : Fintype.card Ω = 5)
    (h : (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ)
    (hN : ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω, h * permU σ * h⁻¹ = permU σ') :
    ∃! τ : Equiv.Perm Ω, h = permU τ := by
  have hv : ∀ ω, ∃ ω', h.val (vvec h5 ω) = vvec h5 ω' := by
    intro ω
    have hw : weight ((h.val (vvec h5 ω) : ↥(evenWeight Ω)) : Ω → ZMod 2) = 4 := by
      rw [normalizer_weight h5 h hN]
      exact weight_one_add_delta h5 ω
    obtain ⟨a, ha⟩ := eq_one_add_delta_of_weight_four h5 hw
    exact ⟨a, Subtype.ext ha⟩
  choose τ hτ using hv
  have hτinj : Function.Injective τ := by
    intro a b hab
    have h1 : h.val (vvec h5 a) = h.val (vvec h5 b) := by rw [hτ, hτ, hab]
    have h2 : vvec h5 a = vvec h5 b := by
      have := congrArg (h⁻¹).val h1
      simpa [← Module.End.mul_apply, ← Units.val_mul] using this
    exact vvec_injective h5 h2
  let τe : Equiv.Perm Ω := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  have hh : h = permU τe := by
    apply Units.ext
    apply LinearMap.ext_on (span_vvec h5)
    rintro _ ⟨ω, rfl⟩
    rw [hτ, permU_vvec]
    rfl
  exact ⟨τe, hh, fun τ' hτ' => permU_injective h5 (hτ'.symm.trans hh)⟩

end Normalizer

end CFSG.QuasithinUnique.Setup.SL2Modules