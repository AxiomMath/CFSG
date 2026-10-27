module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaTorEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {N j : ℕ}

section Form

@[expose] def IsFVec (j : ℕ) (x : Fin N ⊕ Fin N → K) : Prop := ∀ r, spABlk j r ≠ 1 → x r = 0

variable (j) in
@[expose] def spBForm (x y : Fin N ⊕ Fin N → K) : K := spForm (spANil K N j *ᵥ x) y

theorem spANil_mulVec_inl (x : Fin N ⊕ Fin N → K) (k : Fin N) :
    (spANil K N j *ᵥ x) (Sum.inl k) = ∑ m, spARepMat N j k m * x (Sum.inr m) := by
  simp [spANil, mulVec, dotProduct]

theorem spANil_mulVec_inr (x : Fin N ⊕ Fin N → K) (k : Fin N) :
    (spANil K N j *ᵥ x) (Sum.inr k) = 0 := by
  simp [spANil, fromBlocks_mulVec]

theorem spForm_spANil_spANil (x y : Fin N ⊕ Fin N → K) :
    spForm (spANil K N j *ᵥ x) (spANil K N j *ᵥ y) = 0 := by
  rw [spForm_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [spANil_mulVec_inr, spANil_mulVec_inr, mul_zero, zero_mul, sub_zero]

theorem spBForm_eq_sum (x y : Fin N ⊕ Fin N → K) :
    spBForm j x y = ∑ i, ∑ m, spARepMat N j i m * x (Sum.inr m) * y (Sum.inr i) := by
  rw [spBForm, spForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spANil_mulVec_inl, spANil_mulVec_inr, zero_mul, sub_zero, Finset.sum_mul]

theorem spBForm_comm (x y : Fin N ⊕ Fin N → K) : spBForm j x y = spBForm j y x := by
  have hs : ∀ a b : Fin N, (spARepMat N j : Matrix (Fin N) (Fin N) K) a b = spARepMat N j b a :=
    fun a b => by
      rw [← transpose_apply (spARepMat N j : Matrix (Fin N) (Fin N) K) b a, spARepMat_transpose]
  rw [spBForm_eq_sum, spBForm_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hs a b]
  ring

theorem spBForm_add_left (x y z : Fin N ⊕ Fin N → K) :
    spBForm j (x + y) z = spBForm j x z + spBForm j y z := by
  rw [spBForm, mulVec_add, spForm_add_left]
  rfl

theorem spBForm_add_right (x y z : Fin N ⊕ Fin N → K) :
    spBForm j x (y + z) = spBForm j x y + spBForm j x z :=
  spForm_add_right

theorem spBForm_sub_left (x y z : Fin N ⊕ Fin N → K) :
    spBForm j (x - y) z = spBForm j x z - spBForm j y z := by
  rw [spBForm, mulVec_sub, spForm_sub_left]
  rfl

theorem spBForm_sub_right (x y z : Fin N ⊕ Fin N → K) :
    spBForm j x (y - z) = spBForm j x y - spBForm j x z :=
  spForm_sub_right

theorem spBForm_smul_left (c : K) (x y : Fin N ⊕ Fin N → K) :
    spBForm j (c • x) y = c * spBForm j x y := by
  rw [spBForm, mulVec_smul, spForm_smul_left]
  rfl

theorem spBForm_smul_right (c : K) (x y : Fin N ⊕ Fin N → K) :
    spBForm j x (c • y) = c * spBForm j x y :=
  spForm_smul_right c

theorem spBForm_self [CharP K 2] (hjn : 2 * j ≤ N) (x : Fin N ⊕ Fin N → K) :
    spBForm j x x = 0 := by
  rw [spBForm, spForm_apply]
  have e : ∀ i, (spANil K N j *ᵥ x) (Sum.inl i) * x (Sum.inr i) -
      (spANil K N j *ᵥ x) (Sum.inr i) * x (Sum.inl i) =
      (if i.val < 2 * j then x (Sum.inr (spAPar i)) else 0) * x (Sum.inr i) := by
    intro i
    rw [spANil_mulVec_inl, spANil_mulVec_inr, zero_mul, sub_zero,
      sum_spARepMat_mul hjn (fun m => x (Sum.inr m)) i]
  simp only [e]
  refine Finset.sum_ninvolution (fun i => if i.val < 2 * j then spAPar i else i) (fun i => ?_)
    (fun i hi => ?_) (fun i => Finset.mem_univ _) (fun i => ?_)
  · by_cases hi : i.val < 2 * j
    · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left (spAPar_lt hjn hi), spAPar_spAPar hjn hi,
        mul_comm (x (Sum.inr i)), ← two_mul, CharTwo.two_eq_zero, zero_mul]
    · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hi, zero_mul, zero_add]
  · by_cases hi' : i.val < 2 * j
    · rw [ite_eq_left hi']
      intro h
      have hv := spAPar_val hjn hi'
      rw [h] at hv
      split_ifs at hv <;> omega
    · rw [ite_eq_right hi'] at hi
      simp at hi
  · by_cases hi : i.val < 2 * j
    · rw [ite_eq_left hi, ite_eq_left (spAPar_lt hjn hi), spAPar_spAPar hjn hi]
    · rw [ite_eq_right hi, ite_eq_right hi]

theorem IsFVec.add {x y : Fin N ⊕ Fin N → K} (hx : IsFVec j x) (hy : IsFVec j y) :
    IsFVec j (x + y) := fun r hr => by
  rw [Pi.add_apply, hx r hr, hy r hr, add_zero]

theorem IsFVec.sub {x y : Fin N ⊕ Fin N → K} (hx : IsFVec j x) (hy : IsFVec j y) :
    IsFVec j (x - y) := fun r hr => by
  rw [Pi.sub_apply, hx r hr, hy r hr, sub_zero]

theorem IsFVec.smul (c : K) {x : Fin N ⊕ Fin N → K} (hx : IsFVec j x) : IsFVec j (c • x) :=
  fun r hr => by rw [Pi.smul_apply, hx r hr, smul_zero]

theorem spABlk_inl_ne_one (k : Fin N) : spABlk j (Sum.inl k : Fin N ⊕ Fin N) ≠ 1 := by
  rw [spABlk_inl]
  split_ifs <;> decide

theorem spForm_eq_zero_of_isFVec {x y : Fin N ⊕ Fin N → K} (hx : IsFVec j x) (hy : IsFVec j y) :
    spForm x y = 0 := by
  rw [spForm_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hx _ (spABlk_inl_ne_one i), hy _ (spABlk_inl_ne_one i), zero_mul, mul_zero, sub_zero]

theorem isFVec_single {k : Fin N} (hk : k.val < 2 * j) :
    IsFVec j (Pi.single (Sum.inr k) (1 : K) : Fin N ⊕ Fin N → K) := by
  intro r hr
  rw [Pi.single_apply, ite_eq_right]
  rintro rfl
  exact hr (by simp [hk])

theorem exists_spBForm_ne_zero (hjn : 2 * j ≤ N) {x : Fin N ⊕ Fin N → K} (hx : IsFVec j x)
    (hx0 : x ≠ 0) : ∃ y, IsFVec j y ∧ spBForm j x y ≠ 0 := by
  obtain ⟨r, hr⟩ : ∃ r, x r ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx0 (funext h)
  have hr1 : spABlk j r = 1 := by
    by_contra h
    exact hr (hx r h)
  obtain ⟨k, rfl, hk⟩ : ∃ k, r = Sum.inr k ∧ k.val < 2 * j := by
    rcases r with k | k
    · exact absurd hr1 (spABlk_inl_ne_one k)
    · rw [spABlk_inr] at hr1
      by_cases h : k.val < 2 * j
      · exact ⟨k, rfl, h⟩
      · rw [ite_eq_right h] at hr1
        exact absurd hr1 (by decide)
  refine ⟨Pi.single (Sum.inr (spAPar k)) 1, isFVec_single (spAPar_lt hjn hk), ?_⟩
  rw [spBForm, spForm_apply, Finset.sum_eq_single (spAPar k)]
  · rw [Pi.single_eq_same, spANil_mulVec_inl, spANil_mulVec_inr, zero_mul, sub_zero, mul_one,
      sum_spARepMat_mul hjn (fun m => x (Sum.inr m)), ite_eq_left (spAPar_lt hjn hk),
      spAPar_spAPar hjn hk]
    exact hr
  · intro i _ hi
    rw [spANil_mulVec_inr, zero_mul, sub_zero, Pi.single_apply, ite_eq_right (by simpa using hi),
      mul_zero]
  · simp

end Form

section Levi

variable (hjn : 2 * j ≤ N) {s : StatedSp N K}
include hjn

theorem mat_eq_zero_of_mem_range_spALeviHom (hs : s ∈ (spALeviHom hjn).range)
    {r t : Fin N ⊕ Fin N} (h : spABlk j r ≠ spABlk j t) : mat N K s r t = 0 := by
  obtain ⟨g, rfl⟩ := hs
  rw [mat_spALeviHom, spALeviPart_apply, ite_eq_right h]

theorem isFVec_mulVec_of_mem_range (hs : s ∈ (spALeviHom hjn).range)
    {x : Fin N ⊕ Fin N → K} (hx : IsFVec j x) : IsFVec j (mat N K s *ᵥ x) := by
  intro r hr
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : spABlk j t = 1
  · rw [mat_eq_zero_of_mem_range_spALeviHom hjn hs (fun h => hr (h.trans ht)), zero_mul]
  · rw [hx t ht, mul_zero]

theorem mat_mul_spANil_of_mem_range (hs : s ∈ (spALeviHom hjn).range) :
    mat N K s * spANil K N j = spANil K N j * mat N K s := by
  obtain ⟨g, rfl⟩ := hs
  exact commute_spARep_iff.1 (mem_centralizer_singleton_iff.1 (spALeviHom_mem_centralizer hjn g))

end Levi

section Order3

variable [CharP K 2] {s : StatedSp N K}

omit [CharP K 2] in
theorem mat_mulVec_cube (hs3 : s ^ 3 = 1) (x : Fin N ⊕ Fin N → K) :
    mat N K s *ᵥ (mat N K s *ᵥ (mat N K s *ᵥ x)) = x := by
  rw [mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul, ← pow_three', hs3, map_one, one_mulVec]

omit [CharP K 2] in
theorem spBForm_mulVec (hsN : mat N K s * spANil K N j = spANil K N j * mat N K s)
    (x y : Fin N ⊕ Fin N → K) :
    spBForm j (mat N K s *ᵥ x) (mat N K s *ᵥ y) = spBForm j x y := by
  rw [spBForm, mulVec_mulVec, ← hsN, ← mulVec_mulVec, spForm_mat_mulVec]
  rfl

theorem neg_vec_eq_self (v : Fin N ⊕ Fin N → K) : -v = v :=
  funext fun r => CharTwo.neg_eq (v r)

variable (hjn : 2 * j ≤ N) (hsN : mat N K s * spANil K N j = spANil K N j * mat N K s)
  (hsF : ∀ x, IsFVec j x → IsFVec j (mat N K s *ᵥ x)) (hs3 : s ^ 3 = 1)
include hjn hsN hsF hs3

theorem eq_zero_of_mulVec_eq_self
    (hA : ¬ ∃ v v' : Fin N ⊕ Fin N → K, IsFVec j v ∧ IsFVec j v' ∧ mat N K s *ᵥ v = v ∧
      mat N K s *ᵥ v' = v' ∧ spBForm j v v' ≠ 0)
    {x : Fin N ⊕ Fin N → K} (hx : IsFVec j x) (hsx : mat N K s *ᵥ x = x) : x = 0 := by
  by_contra hx0
  obtain ⟨y, hy, hxy⟩ := exists_spBForm_ne_zero hjn hx hx0
  have h1 : spBForm j x (mat N K s *ᵥ y) = spBForm j x y := by
    calc spBForm j x (mat N K s *ᵥ y) = spBForm j (mat N K s *ᵥ x) (mat N K s *ᵥ y) := by
          rw [hsx]
      _ = spBForm j x y := spBForm_mulVec hsN x y
  have h2 : spBForm j x (mat N K s *ᵥ (mat N K s *ᵥ y)) = spBForm j x y := by
    calc spBForm j x (mat N K s *ᵥ (mat N K s *ᵥ y)) =
        spBForm j (mat N K s *ᵥ x) (mat N K s *ᵥ (mat N K s *ᵥ y)) := by rw [hsx]
      _ = spBForm j x (mat N K s *ᵥ y) := spBForm_mulVec hsN x _
      _ = spBForm j x y := h1
  apply hA
  refine ⟨x, y + mat N K s *ᵥ y + mat N K s *ᵥ (mat N K s *ᵥ y), hx,
    (hy.add (hsF y hy)).add (hsF _ (hsF y hy)), hsx, ?_, ?_⟩
  · rw [mulVec_add, mulVec_add, mat_mulVec_cube hs3]
    abel
  · rw [spBForm_add_right, spBForm_add_right, h1, h2, CharTwo.add_self_eq_zero, zero_add]
    exact hxy

theorem mulVec_sq_add_mulVec_add_eq_zero
    (hA : ¬ ∃ v v' : Fin N ⊕ Fin N → K, IsFVec j v ∧ IsFVec j v' ∧ mat N K s *ᵥ v = v ∧
      mat N K s *ᵥ v' = v' ∧ spBForm j v v' ≠ 0)
    {x : Fin N ⊕ Fin N → K} (hx : IsFVec j x) :
    mat N K s *ᵥ (mat N K s *ᵥ x) + mat N K s *ᵥ x + x = 0 := by
  apply eq_zero_of_mulVec_eq_self hjn hsN hsF hs3 hA (((hsF _ (hsF x hx)).add (hsF x hx)).add hx)
  rw [mulVec_add, mulVec_add, mat_mulVec_cube hs3]
  abel

omit hjn hsF in
theorem exists_spBForm_mulVec_ne_zero {P : (Fin N ⊕ Fin N → K) → Prop}
    (hPadd : ∀ x y, P x → P y → P (x + y)) (hPs : ∀ x, P x → P (mat N K s *ᵥ x))
    (hPnd : ∀ x, P x → x ≠ 0 → ∃ y, P y ∧ spBForm j x y ≠ 0)
    (hPfix : ∀ x, P x → mat N K s *ᵥ x = x → x = 0) {x₀ : Fin N ⊕ Fin N → K} (hx₀ : P x₀)
    (hx₀0 : x₀ ≠ 0) : ∃ w, P w ∧ spBForm j w (mat N K s *ᵥ w) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hpol : ∀ x y, P x → P y →
      spBForm j x (mat N K s *ᵥ y) + spBForm j y (mat N K s *ᵥ x) = 0 := by
    intro x y hx hy
    have h := hcon (x + y) (hPadd x y hx hy)
    rw [mulVec_add, spBForm_add_left, spBForm_add_right, spBForm_add_right, hcon x hx,
      hcon y hy] at h
    rw [← h]
    ring
  have hz0 : x₀ + mat N K s *ᵥ (mat N K s *ᵥ x₀) = 0 := by
    by_contra hz0
    obtain ⟨y, hy, hzy⟩ := hPnd _ (hPadd _ _ hx₀ (hPs _ (hPs _ hx₀))) hz0
    apply hzy
    have hy₀ : P (mat N K s *ᵥ (mat N K s *ᵥ y)) := hPs _ (hPs _ hy)
    have hyy : mat N K s *ᵥ (mat N K s *ᵥ (mat N K s *ᵥ y)) = y := mat_mulVec_cube hs3 y
    rw [← hyy, spBForm_add_left, spBForm_mulVec hsN, spBForm_comm (mat N K s *ᵥ x₀)]
    exact hpol x₀ _ hx₀ hy₀
  have h2 : mat N K s *ᵥ (mat N K s *ᵥ x₀) = x₀ := by
    have h' : x₀ = -(mat N K s *ᵥ (mat N K s *ᵥ x₀)) := add_eq_zero_iff_eq_neg.1 hz0
    calc mat N K s *ᵥ (mat N K s *ᵥ x₀) = -(mat N K s *ᵥ (mat N K s *ᵥ x₀)) :=
          (neg_vec_eq_self _).symm
      _ = x₀ := h'.symm
  have h1 : mat N K s *ᵥ x₀ = x₀ := by
    calc mat N K s *ᵥ x₀ = mat N K s *ᵥ (mat N K s *ᵥ (mat N K s *ᵥ x₀)) := by rw [h2]
      _ = x₀ := mat_mulVec_cube hs3 x₀
  exact hx₀0 (hPfix x₀ hx₀ h1)

theorem exists_fixedPair_or_fpf [Finite K] (hK : Nat.card K = 2) (hj : 2 ≤ j) :
    (∃ v v' : Fin N ⊕ Fin N → K, IsFVec j v ∧ IsFVec j v' ∧ mat N K s *ᵥ v = v ∧
      mat N K s *ᵥ v' = v' ∧ spBForm j v v' = 1) ∨
    ((∀ x : Fin N ⊕ Fin N → K, IsFVec j x →
        mat N K s *ᵥ (mat N K s *ᵥ x) + mat N K s *ᵥ x + x = 0) ∧
      ∃ v w : Fin N ⊕ Fin N → K, IsFVec j v ∧ IsFVec j w ∧
        spBForm j v (mat N K s *ᵥ v) = 1 ∧ spBForm j w (mat N K s *ᵥ w) = 1 ∧
        spBForm j w v = 0 ∧ spBForm j w (mat N K s *ᵥ v) = 0) := by
  have h01 : ∀ c : K, c ≠ 0 → c = 1 := fun c hc =>
    (eq_zero_or_eq_one_of_natCard_two hK c).resolve_left hc
  by_cases hA : ∃ v v' : Fin N ⊕ Fin N → K, IsFVec j v ∧ IsFVec j v' ∧ mat N K s *ᵥ v = v ∧
      mat N K s *ᵥ v' = v' ∧ spBForm j v v' ≠ 0
  · obtain ⟨v, v', hv, hv', h1, h2, h3⟩ := hA
    exact Or.inl ⟨v, v', hv, hv', h1, h2, h01 _ h3⟩
  right
  set S := mat N K s with hSdef
  have hfix : ∀ x, IsFVec j x → S *ᵥ x = x → x = 0 := fun x hx hsx =>
    eq_zero_of_mulVec_eq_self hjn hsN hsF hs3 hA hx hsx
  have hsq : ∀ x, IsFVec j x → S *ᵥ (S *ᵥ x) + S *ᵥ x + x = 0 := fun x hx =>
    mulVec_sq_add_mulVec_add_eq_zero hjn hsN hsF hs3 hA hx
  refine ⟨hsq, ?_⟩
  have hf0 : IsFVec j (Pi.single (Sum.inr (⟨0, by omega⟩ : Fin N)) (1 : K)) :=
    isFVec_single (by simp only; omega)
  obtain ⟨v, hv, hvsv⟩ := exists_spBForm_mulVec_ne_zero hsN hs3 (P := IsFVec j)
    (fun x y hx hy => hx.add hy) hsF (fun x hx hx0 => exists_spBForm_ne_zero hjn hx hx0) hfix
    hf0 (fun h => by simpa using congrFun h (Sum.inr ⟨0, by omega⟩))
  have hvsv1 : spBForm j v (S *ᵥ v) = 1 := h01 _ hvsv
  have hsv := hsF v hv
  have hvv : spBForm j v v = 0 := spBForm_self hjn v
  have hsvsv : spBForm j (S *ᵥ v) (S *ᵥ v) = 0 := spBForm_self hjn _
  have hsvv : spBForm j (S *ᵥ v) v = 1 := by rw [spBForm_comm, hvsv1]
  have hssv : S *ᵥ (S *ᵥ v) = S *ᵥ v + v := by
    have h := hsq v hv
    have h' : S *ᵥ (S *ᵥ v) = -(S *ᵥ v + v) := by
      rw [add_assoc] at h
      exact add_eq_zero_iff_eq_neg.1 h
    rw [h', neg_vec_eq_self]
  set P : (Fin N ⊕ Fin N → K) → Prop := fun x =>
    IsFVec j x ∧ spBForm j x v = 0 ∧ spBForm j x (S *ᵥ v) = 0 with hP
  set π : (Fin N ⊕ Fin N → K) → (Fin N ⊕ Fin N → K) := fun y =>
    y - spBForm j y (S *ᵥ v) • v - spBForm j y v • (S *ᵥ v) with hπ
  have hπP : ∀ y, IsFVec j y → P (π y) := by
    intro y hy
    refine ⟨(hy.sub (hv.smul _)).sub (hsv.smul _), ?_, ?_⟩
    · simp only [hπ, spBForm_sub_left, spBForm_smul_left, hvv, hsvv]
      ring
    · simp only [hπ, spBForm_sub_left, spBForm_smul_left, hvsv1, hsvsv]
      ring
  have hπb : ∀ x y, P x → spBForm j x (π y) = spBForm j x y := by
    rintro x y ⟨-, hxv, hxsv⟩
    simp only [hπ, spBForm_sub_right, spBForm_smul_right, hxv, hxsv]
    ring
  have hPs : ∀ x, P x → P (S *ᵥ x) := by
    rintro x ⟨hx, hxv, hxsv⟩
    refine ⟨hsF x hx, ?_, ?_⟩
    · have e : spBForm j (S *ᵥ x) v = spBForm j x (S *ᵥ v + v) := by
        rw [← hssv, ← spBForm_mulVec hsN x (S *ᵥ (S *ᵥ v)), mat_mulVec_cube hs3]
      rw [e, spBForm_add_right, hxv, hxsv, add_zero]
    · rw [spBForm_mulVec hsN, hxv]
  have hex : ∃ x₀, P x₀ ∧ x₀ ≠ 0 := by
    classical
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    set f : Fin 4 → (Fin N ⊕ Fin N → K) := fun i =>
      Pi.single (Sum.inr (⟨i.val, by omega⟩ : Fin N)) 1 with hf
    have hfF : ∀ i, IsFVec j (f i) := fun i => isFVec_single (by simp only; omega)
    have hmem : ∀ i, f i ∈ ({v, S *ᵥ v, v + S *ᵥ v} : Finset (Fin N ⊕ Fin N → K)) := by
      intro i
      have h0 := hno _ (hπP _ (hfF i))
      have e : f i = spBForm j (f i) (S *ᵥ v) • v + spBForm j (f i) v • (S *ᵥ v) := by
        rw [← sub_eq_zero, ← h0]
        simp only [hπ]
        abel
      have hne : f i ≠ 0 := fun h => by
        simpa [hf] using congrFun h (Sum.inr ⟨i.val, by omega⟩)
      rcases eq_zero_or_eq_one_of_natCard_two hK (spBForm j (f i) (S *ᵥ v)) with h1 | h1 <;>
        rcases eq_zero_or_eq_one_of_natCard_two hK (spBForm j (f i) v) with h2 | h2 <;>
        rw [h1, h2] at e <;> simp only [zero_smul, one_smul, zero_add, add_zero] at e
      · exact absurd e hne
      · simp [e]
      · simp [e]
      · simp [e]
    have hinj : Set.InjOn f (Finset.univ : Finset (Fin 4)) := by
      intro i _ i' _ h
      have := congrFun h (Sum.inr ⟨i.val, by omega⟩)
      by_contra hii
      have hval : i.val ≠ i'.val := fun h' => hii (Fin.ext h')
      simp [hf, hval] at this
    have hcard := Finset.card_le_card_of_injOn f (fun i _ => hmem i) hinj
    have h3 : ({v, S *ᵥ v, v + S *ᵥ v} : Finset (Fin N ⊕ Fin N → K)).card ≤ 3 :=
      Finset.card_le_three
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨x₀, hx₀, hx₀0⟩ := hex
  obtain ⟨w, ⟨hw, hwv, hwsv⟩, hwsw⟩ := exists_spBForm_mulVec_ne_zero hsN hs3 (P := P)
    (fun x y hx hy => ⟨hx.1.add hy.1, by rw [spBForm_add_left, hx.2.1, hy.2.1, add_zero],
      by rw [spBForm_add_left, hx.2.2, hy.2.2, add_zero]⟩)
    hPs (fun x hx hx0 => by
      obtain ⟨y, hy, hxy⟩ := exists_spBForm_ne_zero hjn hx.1 hx0
      exact ⟨π y, hπP y hy, by rwa [hπb x y hx]⟩)
    (fun x hx hsx => hfix x hx.1 hsx) hx₀ hx₀0
  exact ⟨v, w, hv, hw, hvsv1, h01 _ hwsw, hwv, hwsv⟩

end Order3

end CFSG.SeitzReduction.SymplecticPilot
