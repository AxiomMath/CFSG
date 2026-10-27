module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSignedPerm
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public noncomputable section

namespace CFSG.ComponentClassification.PresentationLocal

open Equiv SemidirectProduct

variable {n : ℕ}

theorem add_self_vec (v : Fin n → ZMod 2) : v + v = 0 :=
  funext fun j => CharTwo.add_self_eq_zero (v j)

theorem eq_sum_smul_basisVec_add {w : Fin n → ZMod 2} (hw : w ∈ evenSubspace n) (r : Fin n) :
    w = ∑ k, w k • (basisVec r + basisVec k) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, basisVec, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [mem_evenSubspace.1 hw, zero_mul, zero_add]
  simp [Pi.single_apply]

theorem span_basisVec_add (r : Fin n) :
    Submodule.span (ZMod 2) (Set.range fun k => basisVec r + basisVec k) = evenSubspace n := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_
  · rintro _ ⟨k, rfl⟩
    exact basisVec_add_basisVec_mem r k
  · rw [eq_sum_smul_basisVec_add hw r]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem add_permVec_swap {v : Fin n → ZMod 2} {i j : Fin n} (h : v i ≠ v j) :
    v + permVec (swap i j) v = basisVec i + basisVec j := by
  have hij : i ≠ j := fun hij => h (congrArg v hij)
  have hsum : v i + v j = 1 := by
    have key : ∀ a b : ZMod 2, a ≠ b → a + b = 1 := by decide
    exact key _ _ h
  funext k
  simp only [Pi.add_apply, permVec_apply, swap_inv, basisVec, Pi.single_apply]
  by_cases hki : k = i
  · subst hki
    simp [swap_apply_left, hij, hsum]
  by_cases hkj : k = j
  · subst hkj
    simp [swap_apply_right, hki, add_comm (v k), hsum]
  rw [swap_apply_of_ne_of_ne hki hkj, ite_eq_right hki, ite_eq_right hkj, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem exists_perm_apply_eq_apply_eq {i j r t : Fin n} (hij : i ≠ j) (hrt : r ≠ t) :
    ∃ σ : Perm (Fin n), σ i = r ∧ σ j = t := by
  have hne : r ≠ swap i r j := by
    intro h
    have h' := swap_apply_eq_iff.1 h.symm
    rw [swap_apply_right] at h'
    exact hij h'.symm
  refine ⟨swap (swap i r j) t * swap i r, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hne hrt]
  · rw [Perm.mul_apply, swap_apply_left]

theorem eq_evenSubspace_of_basisVec_add_mem {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hU : U ≤ evenSubspace n) (hinv : ∀ (σ : Perm (Fin n)) (v : Fin n → ZMod 2), v ∈ U →
      permVec σ v ∈ U) {i j : Fin n} (hij : i ≠ j) (hmem : basisVec i + basisVec j ∈ U) :
    U = evenSubspace n := by
  refine le_antisymm hU ?_
  rw [← span_basisVec_add i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  by_cases hk : k = i
  · show basisVec i + basisVec k ∈ U
    rw [hk, add_self_vec]
    exact U.zero_mem
  · obtain ⟨σ, hσi, hσj⟩ := exists_perm_apply_eq_apply_eq hij (Ne.symm hk)
    have := hinv σ _ hmem
    rwa [permVec_add, permVec_basisVec, permVec_basisVec, hσi, hσj] at this

theorem evenSubspace_eq_bot_or_eq (hodd : Odd n) {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hU : U ≤ evenSubspace n) (hinv : ∀ (σ : Perm (Fin n)) (v : Fin n → ZMod 2), v ∈ U →
      permVec σ v ∈ U) :
    U = ⊥ ∨ U = evenSubspace n := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  right
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hex : ∃ i j, v i ≠ v j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hv0 (funext h')
    have hvi : v i = 1 := by
      have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact key _ hi
    have hsum := mem_evenSubspace.1 (hU hvU)
    simp only [← hcon i, hvi, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hsum
    rw [ZMod.natCast_eq_one_iff_odd.2 hodd] at hsum
    exact one_ne_zero hsum
  obtain ⟨i, j, hij⟩ := hex
  have hmem : basisVec i + basisVec j ∈ U := by
    rw [← add_permVec_swap hij]
    exact U.add_mem hvU (hinv _ _ hvU)
  exact eq_evenSubspace_of_basisVec_add_mem hU hinv (fun h => hij (congrArg v h)) hmem

theorem card_evenSubspace (hn : 1 ≤ n) : Nat.card (evenSubspace n) = 2 ^ (n - 1) := by
  let f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i, LinearMap.proj i
  have hf : ∀ v, f v = ∑ i, v i := fun v => by simp [f]
  have hker : LinearMap.ker f = evenSubspace n := by
    ext v
    rw [LinearMap.mem_ker, hf, mem_evenSubspace]
  have hsurj : Function.Surjective f := fun c => ⟨Pi.single ⟨0, hn⟩ c, by rw [hf]; simp⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hker,
    Module.finrank_fin_fun] at hrank
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  omega

theorem mul_comm_of_mem_signSubgroup {a b : W n} (ha : a ∈ signSubgroup n)
    (hb : b ∈ signSubgroup n) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem mul_self_of_mem_signSubgroup {a : W n} (ha : a ∈ signSubgroup n) : a * a = 1 := by
  refine ext_vec ?_ ?_
  · obtain ⟨x, rfl⟩ := ha
    rw [vec_mul, right_inl, permVec_one, add_self_vec, vec_one]
  · obtain ⟨x, rfl⟩ := ha
    simp

theorem isElementaryAbelian_signSubgroup : CFSG.IsElementaryAbelian 2 (signSubgroup n) := by
  have : IsMulCommutative (signSubgroup n) :=
    ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_signSubgroup a.2 b.2)⟩⟩
  exact ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]
    exact mul_self_of_mem_signSubgroup x.2)⟩

theorem card_signSubgroup (hn : 1 ≤ n) : Nat.card (signSubgroup n) = 2 ^ (n - 1) := by
  rw [signSubgroup,
    ← Nat.card_congr (MonoidHom.ofInjective (inl_injective (φ := permAut n))).toEquiv,
    ← card_evenSubspace hn]
  exact Nat.card_congr Multiplicative.toAdd

theorem inl_mul_inr_mul_inv_mul_inv (v : Multiplicative (evenSubspace n)) (σ : Perm (Fin n)) :
    (inl v : W n) * inr σ * (inl v)⁻¹ * (inr σ)⁻¹ =
      mk (vec (inl v : W n) + permVec σ (vec (inl v : W n)))
        (Submodule.add_mem _ (vec_mem _) (permVec_mem σ (vec_mem _))) 1 := by
  refine ext_vec ?_ ?_
  · simp only [vec_mul, vec_inv, right_mul, right_inv', right_inl, right_inr, vec_inr,
      permVec_zero, permVec_one, inv_one, one_mul, add_zero, vec_mk]
  · simp

theorem inl_basisVec_add_mem_commutator (hn : 3 ≤ n) (j k : Fin n) :
    (inl (Multiplicative.ofAdd ⟨basisVec j + basisVec k, basisVec_add_basisVec_mem j k⟩) :
      W n) ∈ commutator (W n) := by
  obtain ⟨i, hij, hik⟩ : ∃ i : Fin n, i ≠ j ∧ i ≠ k := by
    by_cases h0 : (j : ℕ) ≠ 0 ∧ (k : ℕ) ≠ 0
    · exact ⟨⟨0, by omega⟩, fun h => h0.1 (by rw [← h]), fun h => h0.2 (by rw [← h])⟩
    by_cases h1 : (j : ℕ) ≠ 1 ∧ (k : ℕ) ≠ 1
    · exact ⟨⟨1, by omega⟩, fun h => h1.1 (by rw [← h]), fun h => h1.2 (by rw [← h])⟩
    refine ⟨⟨2, by omega⟩, fun h => ?_, fun h => ?_⟩
    · have : (j : ℕ) = 2 := by rw [← h]
      omega
    · have : (k : ℕ) = 2 := by rw [← h]
      omega
  have hcomm := Subgroup.commutator_mem_commutator (Subgroup.mem_top
    (inl (Multiplicative.ofAdd ⟨basisVec i + basisVec j, basisVec_add_basisVec_mem i j⟩) :
      W n)) (Subgroup.mem_top (inr (swap j k) : W n))
  rw [commutatorElement_def, inl_mul_inr_mul_inv_mul_inv, ← commutator_def] at hcomm
  convert hcomm using 1
  refine ext_vec ?_ rfl
  simp only [vec_inl, vec_mk, permVec_add, permVec_basisVec, swap_apply_of_ne_of_ne hij hik,
    swap_apply_left]
  rw [add_add_add_comm, add_self_vec, zero_add]

theorem signSubgroup_le_commutator (hn : 3 ≤ n) : signSubgroup n ≤ commutator (W n) := by
  rintro _ ⟨x, rfl⟩
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have key : ∀ v : Fin n → ZMod 2, v ∈ Submodule.span (ZMod 2)
      (Set.range fun k => basisVec (⟨0, by omega⟩ : Fin n) + basisVec k) →
      ∀ hv : v ∈ evenSubspace n, (inl (Multiplicative.ofAdd ⟨v, hv⟩) : W n) ∈ commutator (W n) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro _
      exact inl_basisVec_add_mem_commutator hn _ _
    | zero =>
      intro _
      exact Subgroup.one_mem _
    | add y z hy hz ihy ihz =>
      intro _
      rw [span_basisVec_add] at hy hz
      have := Subgroup.mul_mem _ (ihy hy) (ihz hz)
      rwa [← map_mul] at this
    | smul c y hy ih =>
      intro hcy
      rw [span_basisVec_add] at hy
      rcases h01 c with rfl | rfl
      · have : (⟨(0 : ZMod 2) • y, hcy⟩ : evenSubspace n) = 0 := Subtype.ext (zero_smul _ _)
        rw [this]
        exact Subgroup.one_mem _
      · have : (⟨(1 : ZMod 2) • y, hcy⟩ : evenSubspace n) = ⟨y, hy⟩ := Subtype.ext (one_smul _ _)
        rw [this]
        exact ih hy
  exact key _ (by rw [span_basisVec_add]; exact (Multiplicative.toAdd x).2)
    (Multiplicative.toAdd x).2

theorem odd_even_weight_permutation_module_irreducible (hn : 3 ≤ n) (hodd : Odd n) :
    (∀ U : Submodule (ZMod 2) (Fin n → ZMod 2), U ≤ evenSubspace n →
      (∀ (σ : Perm (Fin n)) (v : Fin n → ZMod 2), v ∈ U → permVec σ v ∈ U) →
        U = ⊥ ∨ U = evenSubspace n) ∧
    CFSG.IsElementaryAbelian 2 (signSubgroup n) ∧ Nat.card (signSubgroup n) = 2 ^ (n - 1) ∧
    signSubgroup n ≤ commutator (W n) :=
  ⟨fun _ hU hinv => evenSubspace_eq_bot_or_eq hodd hU hinv, isElementaryAbelian_signSubgroup,
    card_signSubgroup (by omega), signSubgroup_le_commutator hn⟩

end CFSG.ComponentClassification.PresentationLocal
