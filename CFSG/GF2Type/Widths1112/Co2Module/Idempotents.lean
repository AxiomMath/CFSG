module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GF2Type.Widths1112.Co2Module

open Finset

abbrev F3Vec : Type := Fin 4 → ZMod 3

@[expose] def hyp (w : F3Vec) : Finset F3Vec := univ.filter fun v => w ⬝ᵥ v = 0

theorem mem_hyp {w v : F3Vec} : v ∈ hyp w ↔ w ⬝ᵥ v = 0 := by simp [hyp]

@[expose] def phi (w : F3Vec) : F3Vec →+ ZMod 3 where
  toFun v := w ⬝ᵥ v
  map_zero' := dotProduct_zero w
  map_add' := dotProduct_add w

theorem phi_apply (w v : F3Vec) : phi w v = w ⬝ᵥ v := rfl

theorem card_univ_F3Vec : (univ : Finset F3Vec).card = 81 := by
  simp

theorem exists_coord_ne_zero {w : F3Vec} (hw : w ≠ 0) : ∃ i, w i ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  exact ⟨i, hi⟩

theorem phi_surjective {w : F3Vec} (hw : w ≠ 0) : Function.Surjective (phi w) := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hw
  intro y
  refine ⟨Pi.single i (y * (w i)⁻¹), ?_⟩
  rw [phi_apply, dotProduct_single]
  field_simp

theorem card_hyp_of_ne_zero {w : F3Vec} (hw : w ≠ 0) : (hyp w).card = 27 := by
  have hsurj := phi_surjective hw
  have hfib : ∀ y : ZMod 3, (univ.filter fun v : F3Vec => phi w v = y).card = (hyp w).card := by
    intro y
    have := AddMonoidHom.card_fiber_eq_of_mem_range (phi w) (hsurj y) (hsurj 0)
    have hyp_eq : hyp w = univ.filter fun g => phi w g = 0 := by
      ext g; rw [mem_hyp, Finset.mem_filter]; simp [phi_apply]
    rw [hyp_eq]
    convert this
  have hsum := Finset.card_eq_sum_card_fiberwise (f := phi w) (s := (univ : Finset F3Vec))
    (t := (univ : Finset (ZMod 3))) (fun _ _ => mem_univ _)
  simp only [hfib, sum_const, card_univ, smul_eq_mul] at hsum
  simp at hsum
  omega

theorem hyp_zero : hyp 0 = univ := by
  ext v; simp [mem_hyp]

theorem odd_card_hyp (w : F3Vec) : Odd (hyp w).card := by
  by_cases hw : w = 0
  · subst hw; rw [hyp_zero, card_univ_F3Vec]; decide
  · rw [card_hyp_of_ne_zero hw]; decide

@[expose] def Nonprop (w w' : F3Vec) : Prop :=
  ∀ s t : ZMod 3, s • w + t • w' = 0 → s = 0 ∧ t = 0

theorem Nonprop.left_ne_zero {w w' : F3Vec} (h : Nonprop w w') : w ≠ 0 := by
  intro h0
  have := (h 1 0 (by simp [h0])).1
  exact one_ne_zero this

theorem Nonprop.exists_hyp_not_hyp {w w' : F3Vec} (h : Nonprop w w') :
    ∃ b, w ⬝ᵥ b = 0 ∧ w' ⬝ᵥ b ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ b, w ⬝ᵥ b = 0 → w' ⬝ᵥ b = 0 := fun b hb => by
    by_contra h1; exact hcon ⟨b, hb, h1⟩
  obtain ⟨i, hi⟩ := exists_coord_ne_zero h.left_ne_zero
  have hwa : w ⬝ᵥ (Pi.single i (w i)⁻¹ : F3Vec) = 1 := by
    rw [dotProduct_single]; field_simp
  have key : w' - (w' ⬝ᵥ (Pi.single i (w i)⁻¹ : F3Vec)) • w = 0 := by
    apply dotProduct_eq_zero
    intro x
    have hx : w ⬝ᵥ (x - (w ⬝ᵥ x) • (Pi.single i (w i)⁻¹ : F3Vec)) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hwa]; simp
    have := hcon' _ hx
    rw [dotProduct_sub, dotProduct_smul] at this
    rw [sub_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul] at this ⊢
    linear_combination this
  obtain ⟨c, hc⟩ : ∃ c : ZMod 3, w' = c • w := ⟨_, sub_eq_zero.mp key⟩
  have := (h c (-1) (by rw [hc, neg_smul, one_smul, add_neg_cancel])).2
  exact absurd this (by decide)

theorem zmod_three_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 := by decide

theorem eq_smul_of_smul_add_eq_zero {w w' : F3Vec} {s t : ZMod 3} (ht : t ≠ 0)
    (h : s • w + t • w' = 0) : w' = (-(t⁻¹ * s)) • w := by
  funext i
  have hi := congr_fun h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hi

theorem smul_eq_zero_of_coord {w : F3Vec} {t : ZMod 3} (hw : w ≠ 0) (h : t • w = 0) : t = 0 := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hw
  have := congr_fun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_right hi

structure IsLineReps (R : Finset F3Vec) : Prop where
  ne_zero : ∀ w ∈ R, w ≠ 0
  mem_or_neg_mem : ∀ w : F3Vec, w ≠ 0 → w ∈ R ∨ -w ∈ R
  neg_notMem : ∀ w ∈ R, -w ∉ R

theorem IsLineReps.nonprop {R : Finset F3Vec} (hR : IsLineReps R) {w w' : F3Vec} (hw : w ∈ R)
    (hw' : w' ∈ R) (hne : w ≠ w') : Nonprop w w' := by
  intro s t hst
  have hw0 := hR.ne_zero w hw
  have hw'0 := hR.ne_zero w' hw'
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨smul_eq_zero_of_coord hw0 hst, rfl⟩
  · by_cases hs : s = 0
    · subst hs
      simp only [zero_smul, zero_add] at hst
      exact absurd (smul_eq_zero_of_coord hw'0 hst) ht
    · exfalso
      have h1 := eq_smul_of_smul_add_eq_zero ht hst
      have hu : -(t⁻¹ * s) ≠ 0 := by simp [hs, ht]
      rcases zmod_three_cases (-(t⁻¹ * s)) with h | h | h
      · exact hu h
      · rw [h, one_smul] at h1
        exact hne h1.symm
      · rw [h, neg_smul, one_smul] at h1
        exact hR.neg_notMem w hw (h1 ▸ hw')

theorem IsLineReps.two_mul_card_filter {R : Finset F3Vec} (hR : IsLineReps R)
    (P : F3Vec → Prop) [DecidablePred P] (hP : ∀ w, P (-w) ↔ P w) :
    2 * (R.filter P).card = (univ.filter fun w => w ≠ 0 ∧ P w).card := by
  have hdisj : Disjoint (R.filter P) ((R.filter P).image (fun w => -w)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw'
    exact hR.neg_notMem a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hw).1
  have hunion : (univ.filter fun w => w ≠ 0 ∧ P w) =
      R.filter P ∪ (R.filter P).image (fun w => -w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hw0, hPw⟩
      rcases hR.mem_or_neg_mem w hw0 with h | h
      · exact Or.inl ⟨h, hPw⟩
      · exact Or.inr ⟨-w, ⟨h, (hP w).mpr hPw⟩, neg_neg w⟩
    · rintro (⟨hw, hPw⟩ | ⟨a, ⟨ha, hPa⟩, rfl⟩)
      · exact ⟨hR.ne_zero w hw, hPw⟩
      · exact ⟨neg_ne_zero.mpr (hR.ne_zero a ha), (hP a).mpr hPa⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ neg_injective]
  ring

theorem IsLineReps.card_eq {R : Finset F3Vec} (hR : IsLineReps R) : R.card = 40 := by
  have h := hR.two_mul_card_filter (fun _ => True) (fun _ => Iff.rfl)
  have h2 : (univ.filter fun w : F3Vec => w ≠ 0 ∧ True) = univ.erase 0 := by
    ext w; simp
  rw [h2, Finset.card_erase_of_mem (Finset.mem_univ _), card_univ_F3Vec,
    Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  omega

theorem IsLineReps.card_filter {R : Finset F3Vec} (hR : IsLineReps R) {v : F3Vec} (hv : v ≠ 0) :
    (R.filter fun w => w ⬝ᵥ v = 0).card = 13 := by
  have h := hR.two_mul_card_filter (fun w => w ⬝ᵥ v = 0) (fun w => by simp)
  have h2 : (univ.filter fun w : F3Vec => w ≠ 0 ∧ w ⬝ᵥ v = 0) = (hyp v).erase 0 := by
    ext w
    simp [mem_hyp, dotProduct_comm w v, and_comm]
  rw [h2, Finset.card_erase_of_mem (mem_hyp.mpr (dotProduct_zero v)),
    card_hyp_of_ne_zero hv] at h
  have h3 : 2 * (R.filter fun w => w ⬝ᵥ v = 0).card = 2 * 13 := h
  omega

@[expose] def lineReps : Finset F3Vec :=
  univ.filter fun w => ∃ i, w i = 1 ∧ ∀ j, j < i → w j = 0

theorem mem_lineReps {w : F3Vec} : w ∈ lineReps ↔ ∃ i, w i = 1 ∧ ∀ j, j < i → w j = 0 := by
  simp [lineReps]

theorem isLineReps_lineReps : IsLineReps lineReps where
  ne_zero := by
    rintro w hw rfl
    obtain ⟨i, hi, _⟩ := mem_lineReps.mp hw
    exact absurd hi (by simp)
  mem_or_neg_mem := by
    intro w hw0
    obtain ⟨i0, hi0⟩ := exists_coord_ne_zero hw0
    obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min {i : Fin 4 | w i ≠ 0} ⟨i0, hi0⟩
    have hlt : ∀ j, j < i → w j = 0 := fun j hj => by
      by_contra hne
      exact hmin j hne hj
    rcases zmod_three_cases (w i) with h | h | h
    · exact absurd h hi
    · exact Or.inl (mem_lineReps.mpr ⟨i, h, hlt⟩)
    · refine Or.inr (mem_lineReps.mpr ⟨i, ?_, fun j hj => ?_⟩)
      · simp [h]
      · simp [hlt j hj]
  neg_notMem := by
    intro w hw hneg
    obtain ⟨i, hi, hlt⟩ := mem_lineReps.mp hw
    obtain ⟨i', hi', hlt'⟩ := mem_lineReps.mp hneg
    rcases lt_trichotomy i i' with h | h | h
    · have := hlt' i h
      simp [hi] at this
    · subst h
      simp [hi] at hi'
      revert hi'
      decide
    · have := hlt i' h
      simp [this] at hi'

theorem exists_dot_ne_zero {w : F3Vec} (hw : w ≠ 0) : ∃ v, w ⬝ᵥ v ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hw
  exact ⟨Pi.single i 1, by simpa [dotProduct_single] using hi⟩

theorem zmod_smul_eq_nsmul (c : ZMod 3) (v : F3Vec) : c • v = c.val • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem isUnit_of_mul_eq_one_matrix {A B : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : A * B = 1) :
    IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse h)

instance (w w' : F3Vec) : Decidable (Nonprop w w') := by
  unfold Nonprop
  infer_instance

theorem commPow_aux {Γ : Type*} [Group Γ] (e : Fin 4 → Γ) (hc : ∀ i j, Commute (e i) (e j))
    (v : F3Vec) :
    ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).Pairwise
      (Function.onFun Commute fun i => e i ^ (v i).val) :=
  fun i _ j _ _ => (hc i j).pow_pow _ _

@[expose] noncomputable def commutingChar {Γ : Type*} [Group Γ] (e : Fin 4 → Γ)
    (hc : ∀ i j, Commute (e i) (e j)) (h3 : ∀ i, e i ^ 3 = 1) : AddChar F3Vec Γ where
  toFun v := Finset.univ.noncommProd (fun i => e i ^ (v i).val) (commPow_aux e hc v)
  map_zero_eq_one' := by
    refine Finset.noncommProd_induction _ _ _ (fun g : Γ => g = 1) (fun a b ha hb => by
      rw [ha, hb, one_mul]) rfl fun i _ => ?_
    simp
  map_add_eq_mul' u v := by
    have hfg := Finset.noncommProd_mul_distrib (s := Finset.univ) (fun i => e i ^ (u i).val)
      (fun i => e i ^ (v i).val) (commPow_aux e hc u) (commPow_aux e hc v)
      (fun i _ j _ _ => (hc i j).pow_pow _ _)
    refine Eq.trans ?_ hfg
    refine Finset.noncommProd_congr rfl (fun i _ => ?_) _
    show e i ^ ((u i + v i).val) = e i ^ (u i).val * e i ^ (v i).val
    rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ (h3 i)]

theorem commutingChar_apply {Γ : Type*} [Group Γ] (e : Fin 4 → Γ)
    (hc : ∀ i j, Commute (e i) (e j)) (h3 : ∀ i, e i ^ 3 = 1) (v : F3Vec) :
    commutingChar e hc h3 v = e 0 ^ (v 0).val * (e 1 ^ (v 1).val * (e 2 ^ (v 2).val *
      e 3 ^ (v 3).val)) := by
  show Finset.univ.noncommProd (fun i => e i ^ (v i).val) (commPow_aux e hc v) = _
  simp [Finset.noncommProd, Fin.univ_val_map, List.ofFn_succ]

theorem commutingChar_single {Γ : Type*} [Group Γ] (e : Fin 4 → Γ)
    (hc : ∀ i j, Commute (e i) (e j)) (h3 : ∀ i, e i ^ 3 = 1) (i : Fin 4) :
    commutingChar e hc h3 (Pi.single i 1) = e i := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [commutingChar_apply]
  fin_cases i <;> simp [h1]

section RingAny

variable {S : Type*} [Ring S] (θ : AddChar F3Vec S)

@[expose] def sumE : S := ∑ v : F3Vec, θ v

@[expose] def sumH (w : F3Vec) : S := ∑ v ∈ hyp w, θ v

theorem θ_comm (u v : F3Vec) : θ u * θ v = θ v * θ u := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_comm]

theorem θ_mul_sumH {w c : F3Vec} (hc : w ⬝ᵥ c = 0) : θ c * sumH θ w = sumH θ w := by
  unfold sumH
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Equiv.addLeft c) ?_ ?_
  · intro v
    simp [mem_hyp, dotProduct_add, hc]
  · intro v _
    simp [AddChar.map_add_eq_mul]

theorem θ_mul_sumE (c : F3Vec) : θ c * sumE θ = sumE θ := by
  unfold sumE
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Equiv.addLeft c) (by simp) ?_
  intro v _
  simp [AddChar.map_add_eq_mul]

theorem commute_θ_sumH (c w : F3Vec) : Commute (θ c) (sumH θ w) :=
  Commute.sum_right _ _ _ fun v _ => θ_comm θ c v

theorem commute_θ_sumE (c : F3Vec) : Commute (θ c) (sumE θ) :=
  Commute.sum_right _ _ _ fun v _ => θ_comm θ c v

theorem commute_sumH_sumE (w : F3Vec) : Commute (sumH θ w) (sumE θ) :=
  Commute.sum_left _ _ _ fun v _ => commute_θ_sumE θ v

theorem sumE_eq_sum_smul_mul_sumH {w v₀ : F3Vec} (h : w ⬝ᵥ v₀ ≠ 0) :
    sumE θ = (∑ c : ZMod 3, θ (c • v₀)) * sumH θ w := by
  rw [Finset.sum_mul]
  have e1 : ∀ c : ZMod 3, θ (c • v₀) * sumH θ w = ∑ u ∈ hyp w, θ (c • v₀ + u) := by
    intro c
    unfold sumH
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => (AddChar.map_add_eq_mul θ _ _).symm
  simp only [e1]
  rw [← Finset.sum_product']
  unfold sumE
  symm
  refine Finset.sum_nbij' (fun p => p.1 • v₀ + p.2)
    (fun v => ((w ⬝ᵥ v) * (w ⬝ᵥ v₀)⁻¹, v - ((w ⬝ᵥ v) * (w ⬝ᵥ v₀)⁻¹) • v₀)) ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_univ _
  · intro v _
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_hyp.mpr ?_⟩
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  · rintro ⟨c, u⟩ hp
    have hu : w ⬝ᵥ u = 0 := mem_hyp.mp (Finset.mem_product.mp hp).2
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hu, add_zero]
    ext <;> simp [h]
  · intro v _
    simp
  · intro p _
    rfl

theorem sum_zmod3_smul (v₀ : F3Vec) : ∑ c : ZMod 3, θ (c • v₀) = 1 + θ v₀ + θ v₀ * θ v₀ := by
  have huniv : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    zero_smul, one_smul, two_smul, AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, add_assoc]

@[expose] def sumEK (w : F3Vec) : S := sumH θ w + sumE θ

theorem commute_θ_sumEK (c w : F3Vec) : Commute (θ c) (sumEK θ w) :=
  (commute_θ_sumH θ c w).add_right (commute_θ_sumE θ c)

theorem three_add_self (v : F3Vec) : v + v + v = 0 := by
  funext i
  have h3 : ∀ x : ZMod 3, x + x + x = 0 := by decide
  simpa using h3 (v i)

theorem θ_cube (v : F3Vec) : θ v * θ v * θ v = 1 := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, three_add_self,
    AddChar.map_zero_eq_one]

end RingAny

section ZMod2Module

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem add_self_eq_zero_of_zmod2 (x : M) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

theorem nsmul_eq_zero_of_even {n : ℕ} (hn : Even n) (x : M) : n • x = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, ← nsmul_add, add_self_eq_zero_of_zmod2, nsmul_zero]

theorem nsmul_eq_self_of_odd {n : ℕ} (hn : Odd n) (x : M) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, nsmul_eq_zero_of_even ⟨k, two_mul k⟩, zero_add]

end ZMod2Module

section Char2

variable {S : Type*} [Ring S] [Algebra (ZMod 2) S] (θ : AddChar F3Vec S)

theorem add_self_eq_zero_of_algebra (s : S) : s + s = 0 := add_self_eq_zero_of_zmod2 s

theorem sumH_mul_self (w : F3Vec) : sumH θ w * sumH θ w = sumH θ w := by
  show (∑ a ∈ hyp w, θ a) * sumH θ w = sumH θ w
  rw [Finset.sum_mul,
    Finset.sum_congr rfl fun a ha => θ_mul_sumH θ (mem_hyp.mp ha), Finset.sum_const]
  exact nsmul_eq_self_of_odd (odd_card_hyp w) _

theorem sumE_mul_self : sumE θ * sumE θ = sumE θ := by
  show (∑ a : F3Vec, θ a) * sumE θ = sumE θ
  rw [Finset.sum_mul, Finset.sum_congr rfl fun a _ => θ_mul_sumE θ a, Finset.sum_const,
    card_univ_F3Vec]
  exact nsmul_eq_self_of_odd (by decide) _

theorem sumH_mul_sumE (w : F3Vec) : sumH θ w * sumE θ = sumE θ := by
  show (∑ a ∈ hyp w, θ a) * sumE θ = sumE θ
  rw [Finset.sum_mul, Finset.sum_congr rfl fun a _ => θ_mul_sumE θ a, Finset.sum_const]
  exact nsmul_eq_self_of_odd (odd_card_hyp w) _

theorem sumE_mul_sumH (w : F3Vec) : sumE θ * sumH θ w = sumE θ := by
  rw [(commute_sumH_sumE θ w).eq.symm, sumH_mul_sumE]

theorem exists_add_eq_of_nonprop {w w' : F3Vec} (h : Nonprop w w') (s : F3Vec) :
    ∃ c c' : F3Vec, w ⬝ᵥ c = 0 ∧ w' ⬝ᵥ c' = 0 ∧ c + c' = s := by
  obtain ⟨b, hb, hb'⟩ := h.exists_hyp_not_hyp
  refine ⟨((w' ⬝ᵥ b)⁻¹ * (w' ⬝ᵥ s)) • b, s - ((w' ⬝ᵥ b)⁻¹ * (w' ⬝ᵥ s)) • b, ?_, ?_, by abel⟩
  · rw [dotProduct_smul, hb, smul_zero]
  · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring

theorem sumH_mul_sumH_of_nonprop {w w' : F3Vec} (h : Nonprop w w') :
    sumH θ w * sumH θ w' = sumE θ := by
  have hA : ∀ s : F3Vec, θ s * (sumH θ w * sumH θ w') = sumH θ w * sumH θ w' := by
    intro s
    obtain ⟨c, c', hc, hc', rfl⟩ := exists_add_eq_of_nonprop h s
    have e1 : θ c' * sumH θ w = sumH θ w * θ c' := (commute_θ_sumH θ c' w).eq
    calc θ (c + c') * (sumH θ w * sumH θ w')
        = θ c * (θ c' * sumH θ w * sumH θ w') := by
          rw [AddChar.map_add_eq_mul, mul_assoc, mul_assoc]
      _ = θ c * (sumH θ w * (θ c' * sumH θ w')) := by rw [e1, mul_assoc]
      _ = (θ c * sumH θ w) * (θ c' * sumH θ w') := by rw [mul_assoc]
      _ = sumH θ w * sumH θ w' := by rw [θ_mul_sumH θ hc, θ_mul_sumH θ hc']
  have hB : sumE θ * (sumH θ w * sumH θ w') = sumH θ w * sumH θ w' := by
    show (∑ s : F3Vec, θ s) * _ = _
    rw [Finset.sum_mul, Finset.sum_congr rfl fun s _ => hA s, Finset.sum_const, card_univ_F3Vec]
    exact nsmul_eq_self_of_odd (by decide) _
  have hC : sumE θ * (sumH θ w * sumH θ w') = sumE θ := by
    rw [← mul_assoc, sumE_mul_sumH, sumE_mul_sumH]
  exact hB.symm.trans hC

theorem sumEK_mul_self (w : F3Vec) : sumEK θ w * sumEK θ w = sumEK θ w := by
  unfold sumEK
  rw [add_mul, mul_add, mul_add, sumH_mul_self, sumE_mul_self, sumH_mul_sumE, sumE_mul_sumH,
    add_self_eq_zero_of_algebra, add_zero]

theorem sumEK_mul_sumEK_of_nonprop {w w' : F3Vec} (h : Nonprop w w') :
    sumEK θ w * sumEK θ w' = 0 := by
  unfold sumEK
  rw [add_mul, mul_add, mul_add, sumH_mul_sumH_of_nonprop θ h, sumH_mul_sumE, sumE_mul_sumH,
    sumE_mul_self]
  have h2 := add_self_eq_zero_of_algebra (sumE θ)
  rw [h2, add_zero]

theorem sumE_mul_sumEK (w : F3Vec) : sumE θ * sumEK θ w = 0 := by
  unfold sumEK
  rw [mul_add, sumE_mul_sumH, sumE_mul_self, add_self_eq_zero_of_algebra]

theorem sumEK_mul_sumE (w : F3Vec) : sumEK θ w * sumE θ = 0 := by
  unfold sumEK
  rw [add_mul, sumH_mul_sumE, sumE_mul_self, add_self_eq_zero_of_algebra]

theorem sum_sumEK_add_sumE {R : Finset F3Vec} (hR : IsLineReps R) :
    ∑ w ∈ R, sumEK θ w + sumE θ = 1 := by
  have hsplit : ∑ w ∈ R, sumEK θ w = ∑ w ∈ R, sumH θ w := by
    unfold sumEK
    rw [Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_zero_of_even (by rw [hR.card_eq]; decide), add_zero]
  have hswap : ∑ w ∈ R, sumH θ w =
      ∑ v : F3Vec, (R.filter fun w => w ⬝ᵥ v = 0).card • θ v := by
    calc ∑ w ∈ R, sumH θ w = ∑ w ∈ R, ∑ v : F3Vec, if w ⬝ᵥ v = 0 then θ v else 0 := by
          refine Finset.sum_congr rfl fun w _ => ?_
          unfold sumH hyp
          rw [Finset.sum_filter]
      _ = ∑ v : F3Vec, ∑ w ∈ R, if w ⬝ᵥ v = 0 then θ v else 0 := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const]
  have hrest : ∑ v : F3Vec, (R.filter fun w => w ⬝ᵥ v = 0).card • θ v =
      ∑ v ∈ univ.erase 0, θ v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F3Vec))]
    have h0 : (R.filter fun w => w ⬝ᵥ (0 : F3Vec) = 0).card • θ 0 = 0 := by
      have : (R.filter fun w => w ⬝ᵥ (0 : F3Vec) = 0) = R := by
        apply Finset.filter_true_of_mem
        intro w _
        exact dotProduct_zero w
      rw [this, hR.card_eq]
      exact nsmul_eq_zero_of_even (by decide) _
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hR.card_filter (Finset.ne_of_mem_erase hv)]
    exact nsmul_eq_self_of_odd (by decide) _
  have hE : sumE θ = θ 0 + ∑ v ∈ univ.erase 0, θ v := by
    unfold sumE
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F3Vec))]
  rw [hsplit, hswap, hrest, hE, AddChar.map_zero_eq_one]
  have h2 := add_self_eq_zero_of_algebra (∑ v ∈ univ.erase 0, θ v)
  calc ∑ v ∈ univ.erase 0, θ v + (1 + ∑ v ∈ univ.erase 0, θ v)
      = (∑ v ∈ univ.erase 0, θ v + ∑ v ∈ univ.erase 0, θ v) + 1 := by abel
    _ = 1 := by rw [h2, zero_add]

end Char2

section Decomp

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {κ : Type*}
  [Fintype κ] [DecidableEq κ] (e : κ → Module.End K V)

@[expose] def decompMap : V →ₗ[K] ((i : κ) → LinearMap.range (e i)) :=
  LinearMap.pi fun i => (e i).rangeRestrict

omit [Fintype κ] [DecidableEq κ] in
theorem decompMap_apply (x : V) (i : κ) : ((decompMap e x i : LinearMap.range (e i)) : V) = e i x :=
  rfl

theorem decompMap_bijective (hid : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1) :
    Function.Bijective (decompMap e) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ i, e i x = 0 := fun i => by
      have := congr_fun hx i
      simpa [decompMap_apply] using congr_arg Subtype.val this
    have := LinearMap.congr_fun hsum x
    simp only [LinearMap.sum_apply, Module.End.one_apply, h0, Finset.sum_const_zero] at this
    exact this.symm
  · intro y
    refine ⟨∑ j, (y j : V), ?_⟩
    funext i
    apply Subtype.ext
    have key : ∀ j, e i (y j : V) = if j = i then (y j : V) else 0 := by
      intro j
      obtain ⟨z, hz⟩ := (y j).2
      rw [← hz]
      split_ifs with hji
      · subst hji
        have := LinearMap.congr_fun (hid j) z
        simpa using this
      · have := LinearMap.congr_fun (horth i j (Ne.symm hji)) z
        simpa using this
    rw [decompMap_apply, map_sum, Finset.sum_congr rfl fun j _ => key j]
    simp

@[expose] noncomputable def decompEquiv (hid : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1) :
    V ≃ₗ[K] ((i : κ) → LinearMap.range (e i)) :=
  LinearEquiv.ofBijective (decompMap e) (decompMap_bijective e hid horth hsum)

theorem finrank_eq_sum_finrank_range [FiniteDimensional K V] (hid : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1) :
    Module.finrank K V = ∑ i, Module.finrank K (LinearMap.range (e i)) := by
  rw [← Module.finrank_pi_fintype K]
  exact (decompEquiv e hid horth hsum).finrank_eq

end Decomp

theorem even_of_two_pow_modEq_one {d : ℕ} (h : 2 ^ d ≡ 1 [MOD 3]) : Even d := by
  rcases Nat.even_or_odd d with hd | ⟨k, rfl⟩
  · exact hd
  · exfalso
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h2 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod]
      norm_num [h4]
    have h5 : 2 ^ (2 * k + 1) % 3 = 1 % 3 := h
    rw [h2] at h5
    omega

section Rep

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

@[expose] def rhoChar : AddChar F3Vec (Module.End (ZMod 2) V) :=
  (ρ : Γ →* Module.End (ZMod 2) V).compAddChar ι

@[simp] theorem rhoChar_apply (v : F3Vec) : rhoChar ρ ι v = ρ (ι v) := rfl

@[expose] def piE : Module.End (ZMod 2) V := sumE (rhoChar ρ ι)

@[expose] def piH (w : F3Vec) : Module.End (ZMod 2) V := sumH (rhoChar ρ ι) w

@[expose] def eK (w : F3Vec) : Module.End (ZMod 2) V := sumEK (rhoChar ρ ι) w

theorem piE_def : piE ρ ι = ∑ v : F3Vec, ρ (ι v) := by simp [piE, sumE]

theorem piH_def (w : F3Vec) : piH ρ ι w = ∑ v ∈ hyp w, ρ (ι v) := by simp [piH, sumH]

theorem eK_def (w : F3Vec) : eK ρ ι w = piH ρ ι w + piE ρ ι := rfl

theorem piE_mul_self : piE ρ ι * piE ρ ι = piE ρ ι := sumE_mul_self (rhoChar ρ ι)

theorem piH_mul_self (w : F3Vec) : piH ρ ι w * piH ρ ι w = piH ρ ι w :=
  sumH_mul_self (rhoChar ρ ι) w

theorem piH_mul_piE (w : F3Vec) : piH ρ ι w * piE ρ ι = piE ρ ι := sumH_mul_sumE (rhoChar ρ ι) w

theorem eK_mul_self (w : F3Vec) : eK ρ ι w * eK ρ ι w = eK ρ ι w :=
  sumEK_mul_self (rhoChar ρ ι) w

theorem eK_mul_eK_of_nonprop {w w' : F3Vec} (h : Nonprop w w') : eK ρ ι w * eK ρ ι w' = 0 :=
  sumEK_mul_sumEK_of_nonprop (rhoChar ρ ι) h

theorem piE_mul_eK (w : F3Vec) : piE ρ ι * eK ρ ι w = 0 := sumE_mul_sumEK (rhoChar ρ ι) w

theorem eK_mul_piE (w : F3Vec) : eK ρ ι w * piE ρ ι = 0 := sumEK_mul_sumE (rhoChar ρ ι) w

theorem eK_mul_eK_of_ne {R : Finset F3Vec} (hR : IsLineReps R) {w w' : F3Vec} (hw : w ∈ R)
    (hw' : w' ∈ R) (hne : w ≠ w') : eK ρ ι w * eK ρ ι w' = 0 :=
  eK_mul_eK_of_nonprop ρ ι (hR.nonprop hw hw' hne)

theorem sum_eK_add_piE {R : Finset F3Vec} (hR : IsLineReps R) :
    ∑ w ∈ R, eK ρ ι w + piE ρ ι = 1 :=
  sum_sumEK_add_sumE (rhoChar ρ ι) hR

@[expose] def fixedSpace (w : F3Vec) : Submodule (ZMod 2) V where
  carrier := {x | ∀ v, w ⬝ᵥ v = 0 → ρ (ι v) x = x}
  add_mem' := fun {x y} hx hy v hv => by rw [map_add, hx v hv, hy v hv]
  zero_mem' := fun v _ => map_zero _
  smul_mem' := fun c x hx v hv => by rw [map_smul, hx v hv]

theorem range_piH (w : F3Vec) : LinearMap.range (piH ρ ι w) = fixedSpace ρ ι w := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ v hv
    exact LinearMap.congr_fun (θ_mul_sumH (rhoChar ρ ι) hv) y
  · intro hx
    refine ⟨x, ?_⟩
    rw [piH_def, LinearMap.sum_apply,
      Finset.sum_congr rfl fun v hv => hx v (mem_hyp.mp hv), Finset.sum_const]
    exact nsmul_eq_self_of_odd (odd_card_hyp w) x

theorem eK_eq_piH_mul (w : F3Vec) : eK ρ ι w = piH ρ ι w * (1 + piE ρ ι) := by
  rw [mul_add, mul_one, piH_mul_piE, eK_def]

theorem range_eK_le_range_piH (w : F3Vec) :
    LinearMap.range (eK ρ ι w) ≤ LinearMap.range (piH ρ ι w) := by
  rw [eK_eq_piH_mul, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

theorem range_eK_le_fixedSpace (w : F3Vec) :
    LinearMap.range (eK ρ ι w) ≤ fixedSpace ρ ι w :=
  (range_eK_le_range_piH ρ ι w).trans (range_piH ρ ι w).le

theorem fixed_of_mem_range_eK {w : F3Vec} {y : V} (hy : y ∈ LinearMap.range (eK ρ ι w))
    {v : F3Vec} (hv : w ⬝ᵥ v = 0) : ρ (ι v) y = y :=
  range_eK_le_fixedSpace ρ ι w hy v hv

theorem piE_apply_of_mem_range_eK {w : F3Vec} {y : V} (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    piE ρ ι y = 0 := by
  obtain ⟨z, rfl⟩ := hy
  exact LinearMap.congr_fun (piE_mul_eK ρ ι w) z

theorem piH_apply_of_mem_range_eK {w : F3Vec} {y : V} (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    piH ρ ι w y = y := by
  obtain ⟨z, rfl⟩ := hy
  have : piH ρ ι w * eK ρ ι w = eK ρ ι w := by
    rw [eK_def, mul_add, piH_mul_self, piH_mul_piE]
  exact LinearMap.congr_fun this z

theorem piE_eq_mul_piH {w v₀ : F3Vec} (h : w ⬝ᵥ v₀ ≠ 0) :
    piE ρ ι = (1 + ρ (ι v₀) + ρ (ι v₀) * ρ (ι v₀)) * piH ρ ι w := by
  have := sumE_eq_sum_smul_mul_sumH (rhoChar ρ ι) h
  rw [sum_zmod3_smul] at this
  simp only [rhoChar_apply] at this
  exact this

theorem one_add_apply_eq_zero {w v₀ : F3Vec} (h : w ⬝ᵥ v₀ ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    y + ρ (ι v₀) y + ρ (ι v₀) (ρ (ι v₀) y) = 0 := by
  have h1 := piE_apply_of_mem_range_eK ρ ι hy
  have h2 := piH_apply_of_mem_range_eK ρ ι hy
  rw [piE_eq_mul_piH ρ ι h, Module.End.mul_apply, h2] at h1
  simpa using h1

theorem eq_zero_of_apply_eq_self {w v₀ : F3Vec} (h : w ⬝ᵥ v₀ ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w)) (hfix : ρ (ι v₀) y = y) : y = 0 := by
  have h1 := one_add_apply_eq_zero ρ ι h hy
  rw [hfix, hfix] at h1
  calc y = y + y + y := by rw [add_self_eq_zero_of_zmod2, zero_add]
    _ = 0 := h1

theorem rhoι_mul_eK (w v₀ : F3Vec) : ρ (ι v₀) * eK ρ ι w = eK ρ ι w * ρ (ι v₀) :=
  (commute_θ_sumEK (rhoChar ρ ι) v₀ w).eq

theorem apply_mem_range_eK (w v₀ : F3Vec) {y : V} (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    ρ (ι v₀) y ∈ LinearMap.range (eK ρ ι w) := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨ρ (ι v₀) z, ?_⟩
  have := LinearMap.congr_fun (rhoι_mul_eK ρ ι w v₀) z
  rw [Module.End.mul_apply, Module.End.mul_apply] at this
  rw [this]

theorem apply_cube (v₀ : F3Vec) (y : V) : ρ (ι v₀) (ρ (ι v₀) (ρ (ι v₀) y)) = y := by
  have := LinearMap.congr_fun (θ_cube (rhoChar ρ ι) v₀) y
  simpa using this

theorem even_finrank_range_eK [FiniteDimensional (ZMod 2) V] {w v₀ : F3Vec}
    (h : w ⬝ᵥ v₀ ≠ 0) : Even (Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w))) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : Fintype (LinearMap.range (eK ρ ι w)) := Fintype.ofFinite _
  let f : Function.End (LinearMap.range (eK ρ ι w)) :=
    fun y => ⟨ρ (ι v₀) y, apply_mem_range_eK ρ ι w v₀ y.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    have h3 : f ^ 3 ^ 1 = f * f * f := by
      rw [pow_one, pow_succ, pow_succ, pow_one]
    rw [h3]
    funext y
    apply Subtype.ext
    exact apply_cube ρ ι v₀ y
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, ?_⟩
    · apply Subtype.ext
      exact map_zero _
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      apply Subtype.ext
      have hy' : ρ (ι v₀) (y : V) = y := congrArg Subtype.val hy
      exact eq_zero_of_apply_eq_self ρ ι h y.2 hy'
  have hcard : Fintype.card (LinearMap.range (eK ρ ι w)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  rw [hcard, hfix] at hmod
  exact even_of_two_pow_modEq_one hmod

@[expose] def blockFamily (R : Finset F3Vec) : Option ↥R → Module.End (ZMod 2) V
  | none => piE ρ ι
  | some w => eK ρ ι w.1

theorem blockFamily_idem (R : Finset F3Vec) (i : Option ↥R) :
    blockFamily ρ ι R i * blockFamily ρ ι R i = blockFamily ρ ι R i := by
  cases i with
  | none => exact piE_mul_self ρ ι
  | some w => exact eK_mul_self ρ ι w.1

theorem blockFamily_orth {R : Finset F3Vec} (hR : IsLineReps R) (i j : Option ↥R) (hij : i ≠ j) :
    blockFamily ρ ι R i * blockFamily ρ ι R j = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some w => exact piE_mul_eK ρ ι w.1
  | some w =>
    cases j with
    | none => exact eK_mul_piE ρ ι w.1
    | some w' =>
      exact eK_mul_eK_of_ne ρ ι hR w.2 w'.2 fun h => hij (by rw [Subtype.ext h])

theorem blockFamily_sum {R : Finset F3Vec} (hR : IsLineReps R) :
    ∑ i, blockFamily ρ ι R i = 1 := by
  rw [Fintype.sum_option]
  have h1 : ∑ i : ↥R, blockFamily ρ ι R (some i) = ∑ w ∈ R, eK ρ ι w :=
    Finset.sum_coe_sort R (fun w => eK ρ ι w)
  rw [h1]
  exact (add_comm _ _).trans (sum_eK_add_piE ρ ι hR)

theorem finrank_eq_finrank_range_piE_add_sum [FiniteDimensional (ZMod 2) V] {R : Finset F3Vec}
    (hR : IsLineReps R) :
    Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) +
      ∑ w ∈ R, Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
  classical
  have h := finrank_eq_sum_finrank_range (blockFamily ρ ι R) (blockFamily_idem ρ ι R)
    (blockFamily_orth ρ ι hR) (blockFamily_sum ρ ι hR)
  rw [h, Fintype.sum_option]
  congr 1
  exact Finset.sum_coe_sort R (fun w => Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)))

theorem ι_smul (c : ZMod 3) (v : F3Vec) : ι (c • v) = ι v ^ c.val := by
  rw [zmod_smul_eq_nsmul, AddChar.map_nsmul_eq_pow]

theorem apply_ι_of_mem_range_eK {w v₀ : F3Vec} (h : w ⬝ᵥ v₀ ≠ 0) (u : F3Vec) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    ρ (ι u) y = (ρ (ι v₀) ^ ((w ⬝ᵥ u) * (w ⬝ᵥ v₀)⁻¹).val) y := by
  set c : ZMod 3 := (w ⬝ᵥ u) * (w ⬝ᵥ v₀)⁻¹ with hc
  have hperp : w ⬝ᵥ (u - c • v₀) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hc]
    field_simp
    ring
  have hu : u = c • v₀ + (u - c • v₀) := by abel
  have h1 : ρ (ι (u - c • v₀)) y = y := fixed_of_mem_range_eK ρ ι hy hperp
  conv_lhs => rw [hu, AddChar.map_add_eq_mul, map_mul, Module.End.mul_apply, h1, ι_smul, map_pow]

structure ConjAct (ι : AddChar F3Vec Γ) (g : Γ) (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Prop where
  isUnit : IsUnit A
  conj : ∀ v, g * ι v * g⁻¹ = ι (A.mulVec v)

theorem ConjAct.mul_apply {ι : AddChar F3Vec Γ} {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : ConjAct ι g A) (v : F3Vec) : g * ι v = ι (A.mulVec v) * g :=
  mul_inv_eq_iff_eq_mul.mp (h.conj v)

theorem ConjAct.bijective {ι : AddChar F3Vec Γ} {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : ConjAct ι g A) : Function.Bijective A.mulVec :=
  (Finite.injective_iff_bijective).mp (Matrix.mulVec_injective_iff_isUnit.mpr h.isUnit)

variable {ι}

theorem conj_mul_piH {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : ConjAct ι g A)
    {w w' : F3Vec} {c : ZMod 3} (hc : c ≠ 0) (hw : Matrix.vecMul w' A = c • w) :
    ρ g * piH ρ ι w = piH ρ ι w' * ρ g := by
  rw [piH_def, piH_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_equiv (Equiv.ofBijective _ h.bijective) ?_ ?_
  · intro v
    simp only [mem_hyp, Equiv.ofBijective_apply, Matrix.dotProduct_mulVec, hw,
      smul_dotProduct, smul_eq_mul, mul_eq_zero, hc, false_or]
  · intro v _
    simp only [Equiv.ofBijective_apply]
    rw [← map_mul, h.mul_apply, map_mul]

theorem conj_mul_piE {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : ConjAct ι g A) :
    ρ g * piE ρ ι = piE ρ ι * ρ g := by
  rw [piE_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_equiv (Equiv.ofBijective _ h.bijective) (by simp) ?_
  intro v _
  simp only [Equiv.ofBijective_apply]
  rw [← map_mul, h.mul_apply, map_mul]

theorem conj_mul_eK {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : ConjAct ι g A)
    {w w' : F3Vec} {c : ZMod 3} (hc : c ≠ 0) (hw : Matrix.vecMul w' A = c • w) :
    ρ g * eK ρ ι w = eK ρ ι w' * ρ g := by
  rw [eK_def, eK_def, mul_add, add_mul, conj_mul_piH ρ h hc hw, conj_mul_piE ρ h]

theorem rho_apply_inv_apply (g : Γ) (z : V) : ρ g (ρ g⁻¹ z) = z := by
  simp

theorem range_eK_eq_map {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : ConjAct ι g A)
    {w w' : F3Vec} {c : ZMod 3} (hc : c ≠ 0) (hw : Matrix.vecMul w' A = c • w) :
    LinearMap.range (eK ρ ι w') = (LinearMap.range (eK ρ ι w)).map (ρ g) := by
  have key := conj_mul_eK ρ h hc hw
  have hsurj : LinearMap.range (ρ g⁻¹) = ⊤ :=
    LinearMap.range_eq_top.mpr fun z => ⟨ρ g z, by simp⟩
  have e1 : eK ρ ι w' = ρ g * eK ρ ι w * ρ g⁻¹ := by
    have : ρ g * eK ρ ι w * ρ g⁻¹ = eK ρ ι w' * ρ g * ρ g⁻¹ := by rw [key]
    rw [this, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [e1, Module.End.mul_eq_comp, LinearMap.range_comp_of_range_eq_top _ hsurj,
    Module.End.mul_eq_comp, LinearMap.range_comp]

@[expose] def rhoEquiv (g : Γ) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by ext z; exact rho_apply_inv_apply ρ g z)
    (by ext z; simp)

@[simp] theorem rhoEquiv_apply (g : Γ) (z : V) : rhoEquiv ρ g z = ρ g z := rfl

theorem finrank_range_eK_eq {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : ConjAct ι g A)
    {w w' : F3Vec} {c : ZMod 3} (hc : c ≠ 0) (hw : Matrix.vecMul w' A = c • w) :
    Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')) =
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
  rw [range_eK_eq_map ρ h hc hw]
  exact LinearEquiv.finrank_map_eq (rhoEquiv ρ g) _

theorem finrank_range_eK_eq_of_eqvGen {κ : Type*} (g : κ → Γ)
    (A : κ → Matrix (Fin 4) (Fin 4) (ZMod 3)) (hg : ∀ k, ConjAct ι (g k) (A k)) {w w' : F3Vec}
    (hww' : Relation.EqvGen
      (fun a b : F3Vec => ∃ k, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (A k) = c • a) w w') :
    Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')) := by
  induction hww' with
  | rel a b hab =>
    obtain ⟨k, c, hc, hw⟩ := hab
    exact (finrank_range_eK_eq ρ (hg k) hc hw).symm
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem ConjAct.one : ConjAct ι (1 : Γ) 1 where
  isUnit := isUnit_one
  conj v := by simp

theorem ConjAct.mul {g₁ g₂ : Γ} {A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h₁ : ConjAct ι g₁ A₁)
    (h₂ : ConjAct ι g₂ A₂) : ConjAct ι (g₁ * g₂) (A₁ * A₂) where
  isUnit := h₁.isUnit.mul h₂.isUnit
  conj v := by
    have e : g₁ * g₂ * ι v * (g₁ * g₂)⁻¹ = g₁ * (g₂ * ι v * g₂⁻¹) * g₁⁻¹ := by group
    rw [e, h₂.conj, h₁.conj, Matrix.mulVec_mulVec]

theorem ConjAct.inv {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h : ConjAct ι g A) :
    ConjAct ι g⁻¹ A⁻¹ where
  isUnit := (Matrix.isUnit_nonsing_inv_iff).mpr h.isUnit
  conj v := by
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.isUnit
    have e : g * ι (A⁻¹.mulVec v) * g⁻¹ = ι v := by
      rw [h.conj, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
    rw [inv_inv, ← e]
    group

theorem ConjAct.ofBasis {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)} (hA : IsUnit A)
    (h : ∀ i, g * ι (Pi.single i 1) * g⁻¹ = ι (A.mulVec (Pi.single i 1))) : ConjAct ι g A where
  isUnit := hA
  conj := by
    have hadd : ∀ u v : F3Vec, g * ι u * g⁻¹ = ι (A.mulVec u) → g * ι v * g⁻¹ = ι (A.mulVec v) →
        g * ι (u + v) * g⁻¹ = ι (A.mulVec (u + v)) := by
      intro u v hu hv
      rw [AddChar.map_add_eq_mul, Matrix.mulVec_add, AddChar.map_add_eq_mul, ← hu, ← hv]
      group
    have hzero : g * ι (0 : F3Vec) * g⁻¹ = ι (A.mulVec 0) := by
      simp
    have hsingle : ∀ (i : Fin 4) (c : ZMod 3),
        g * ι (Pi.single i c) * g⁻¹ = ι (A.mulVec (Pi.single i c)) := by
      intro i c
      rcases zmod_three_cases c with rfl | rfl | rfl
      · simp
      · exact h i
      · have h2 : (Pi.single i (-1 : ZMod 3) : F3Vec) = Pi.single i 1 + Pi.single i 1 := by
          rw [← Pi.single_add]
          congr 1
        rw [h2]
        exact hadd _ _ (h i) (h i)
    intro v
    rw [← Finset.univ_sum_single v]
    exact Finset.sum_induction _ (fun v : F3Vec => g * ι v * g⁻¹ = ι (A.mulVec v)) hadd hzero
      (fun i _ => hsingle i (v i))

end Rep

end CFSG.GF2Type.Widths1112.Co2Module
