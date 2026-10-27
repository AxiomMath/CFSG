module

public import CFSG.Blueprint.ChevalleyWeyl

public noncomputable section

namespace CFSG.AGLEmbedding.E6Nine

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Matrix

abbrev I6 : Type := Fin Tag.E6.rank

def word9 : List I6 := ([4, 5, 2, 1, 3, 4, 1, 3, 1, 0] : List (Fin 6))

def Rm (i : I6) : Matrix I6 I6 ℤ :=
  fun a b => (if a = b then 1 else 0) - (if a = i then Tag.E6.cartan i b else 0)

theorem reflect_eq (i : I6) (v : I6 → ℤ) : reflect Tag.E6 i v = Rm i *ᵥ v := by
  funext a
  unfold reflect
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [Rm, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    one_mul]
  rw [Finset.sum_ite_eq]
  by_cases h : a = i
  · subst h; simp
  · simp [h]

def Wm : List I6 → Matrix I6 I6 ℤ
  | [] => 1
  | a :: l => Rm a * Wm l

def wordApply : List I6 → (I6 → ℤ) → (I6 → ℤ)
  | [], v => v
  | a :: l, v => reflect Tag.E6 a (wordApply l v)

theorem wordApply_eq (l : List I6) (v : I6 → ℤ) : wordApply l v = Wm l *ᵥ v := by
  induction l with
  | nil => simp [wordApply, Wm]
  | cons a l ih => rw [wordApply, ih, reflect_eq, Wm, Matrix.mulVec_mulVec]

theorem wordApply_iterate (l : List I6) (n : ℕ) (v : I6 → ℤ) :
    (wordApply l)^[n] v = (Wm l) ^ n *ᵥ v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, wordApply_eq, Matrix.mulVec_mulVec, ← pow_succ']

theorem Wm_pow_nine : (Wm word9) ^ 9 = 1 := by decide +kernel

def i0 : I6 := (0 : Fin 6)

def e0 : I6 → ℤ := Pi.single i0 1

theorem Wm_pow_three_noncomm :
    Rm i0 *ᵥ ((Wm word9) ^ 3 *ᵥ e0) ≠ (Wm word9) ^ 3 *ᵥ (Rm i0 *ᵥ e0) := by
  unfold i0 e0
  decide

theorem cartan_symm (j a : I6) : Tag.E6.cartan j a = Tag.E6.cartan a j := by
  fin_cases j <;> fin_cases a <;> rfl

theorem isRoot_wordApply (l : List I6) {α : I6 → ℤ} (hα : IsRoot Tag.E6 α) :
    IsRoot Tag.E6 (wordApply l α) := by
  induction l with
  | nil => exact hα
  | cons a l ih => exact IsRoot.reflect a ih

theorem isRoot_iterate (l : List I6) (n : ℕ) {α : I6 → ℤ} (hα : IsRoot Tag.E6 α) :
    IsRoot Tag.E6 ((wordApply l)^[n] α) := by
  induction n with
  | zero => exact hα
  | succ n ih => rw [Function.iterate_succ_apply']; exact isRoot_wordApply l ih

@[expose] def nElt {K : Type*} [Field K]
    (i : I6) : ModGL Tag.E6 K := weylElt Tag.E6 K i 1

@[expose] def wordElt {K : Type*} [Field K]
    (l : List I6) : ModGL Tag.E6 K := (l.map nElt).prod

theorem wordElt_nil {K : Type*} [Field K] :
    wordElt ([] : List I6) = (1 : ModGL Tag.E6 K) := by
  simp [wordElt]

theorem wordElt_cons {K : Type*} [Field K]
    (a : I6) (l : List I6) :
    wordElt (a :: l) = (nElt a : ModGL Tag.E6 K) * wordElt l := by
  simp [wordElt]

theorem nElt_mem {K : Type*} [Field K]
    (i : I6) : (nElt i : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K :=
  weylElt_mem_adjointGroup i 1

theorem wordElt_mem {K : Type*} [Field K]
    (l : List I6) :
    (wordElt l : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K := by
  unfold wordElt
  exact Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact nElt_mem i)

theorem rootVec_of_isRoot {K : Type*} [Field K] {α : I6 → ℤ} (hα : IsRoot Tag.E6 α) :
    rootVec Tag.E6 K α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := by
  simp [rootVec, hα]

theorem rootVec_injective {K : Type*} [Field K] {α β : I6 → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h : rootVec Tag.E6 K α = rootVec Tag.E6 K β) : α = β := by
  rw [rootVec_of_isRoot hα, rootVec_of_isRoot hβ, Finsupp.single_left_inj one_ne_zero] at h
  exact congrArg Subtype.val (Sum.inr_injective h)

theorem nElt_rootVec {K : Type*} [Field K] [CharP K 2]
    (i : I6) {α : I6 → ℤ} (hα : IsRoot Tag.E6 α) :
    ((nElt i : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α) =
      rootVec Tag.E6 K (reflect Tag.E6 i α) := by
  unfold nElt
  rw [weylElt_rootVec i 1 hα]
  have h1 : (-1 : K) ^ stringDown Tag.E6 i α = 1 := by rw [CharTwo.neg_eq, one_pow]
  simp [h1]

theorem wordElt_rootVec {K : Type*} [Field K] [CharP K 2]
    (l : List I6) {α : I6 → ℤ} (hα : IsRoot Tag.E6 α) :
    ((wordElt l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α) =
      rootVec Tag.E6 K (wordApply l α) := by
  induction l with
  | nil => simp [wordElt_nil, wordApply]
  | cons a l ih =>
    rw [wordElt_cons, Units.val_mul, Module.End.mul_apply, ih, wordApply,
      nElt_rootVec a (isRoot_wordApply l hα)]

theorem wordElt_pow_rootVec {K : Type*} [Field K] [CharP K 2]
    (l : List I6) (n : ℕ) {α : I6 → ℤ} (hα : IsRoot Tag.E6 α) :
    (((wordElt l : ModGL Tag.E6 K) ^ n : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K α) = rootVec Tag.E6 K ((wordApply l)^[n] α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih,
      wordElt_rootVec l (isRoot_iterate l n hα), Function.iterate_succ_apply']

theorem natAbs_cast_charTwo {K : Type*} [Field K] [CharP K 2] (z : ℤ) :
    ((z.natAbs : ℕ) : K) = ((z : ℤ) : K) := by
  rcases Int.natAbs_eq z with h | h
  · conv_rhs => rw [h]
    simp
  · conv_rhs => rw [h]
    simp [CharTwo.neg_eq]

def hSpan {K : Type*} [Field K] (u : I6 → K) : RootModule Tag.E6 K :=
  ∑ j, u j • hVec Tag.E6 K j

theorem castRm_mulVec {K : Type*} [Field K] (a b : I6) (u : I6 → K) :
    ((Int.castRingHom K).mapMatrix (Rm a) *ᵥ u) b =
      u b - if b = a then ∑ j, ((Tag.E6.cartan a j : ℤ) : K) * u j else 0 := by
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Rm,
    Int.coe_castRingHom, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  by_cases h : b = a
  · subst h; simp
  · simp [h]

theorem nElt_hSpan {K : Type*} [Field K] [CharP K 2]
    (a : I6) (u : I6 → K) :
    ((nElt a : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (hSpan u) =
      hSpan ((Int.castRingHom K).mapMatrix (Rm a) *ᵥ u) := by
  have h1 : ∀ j, ((nElt a : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      (u j • hVec Tag.E6 K j) = u j • hVec Tag.E6 K j -
        (u j * ((Tag.E6.cartan a j : ℤ) : K)) • hVec Tag.E6 K a := by
    intro j
    rw [map_smul, nElt, weylElt_hVec, smul_sub, smul_smul, natAbs_cast_charTwo, cartan_symm]
  have hL : ((nElt a : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (hSpan u) =
      hSpan u - (∑ j, u j * ((Tag.E6.cartan a j : ℤ) : K)) • hVec Tag.E6 K a := by
    unfold hSpan
    rw [map_sum]
    simp only [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_smul]
  have hR : hSpan ((Int.castRingHom K).mapMatrix (Rm a) *ᵥ u) =
      hSpan u - (∑ j, ((Tag.E6.cartan a j : ℤ) : K) * u j) • hVec Tag.E6 K a := by
    unfold hSpan
    simp only [castRm_mulVec, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ a (fun b => (∑ j, ((Tag.E6.cartan a j : ℤ) : K) * u j) •
      hVec Tag.E6 K b)]
    simp
  rw [hL, hR]
  congr 2
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hVec_eq_hSpan {K : Type*} [Field K] (j : I6) : hVec Tag.E6 K j = hSpan (Pi.single j 1) := by
  unfold hSpan
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem wordElt_hSpan {K : Type*} [Field K] [CharP K 2]
    (l : List I6) (u : I6 → K) :
    ((wordElt l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (hSpan u) =
      hSpan ((Int.castRingHom K).mapMatrix (Wm l) *ᵥ u) := by
  induction l generalizing u with
  | nil => simp [wordElt_nil, Wm]
  | cons a l ih =>
    rw [wordElt_cons, Units.val_mul, Module.End.mul_apply, ih, nElt_hSpan, Wm, map_mul,
      Matrix.mulVec_mulVec]

theorem wordElt_pow_hSpan {K : Type*} [Field K] [CharP K 2]
    (l : List I6) (n : ℕ) (u : I6 → K) :
    (((wordElt l : ModGL Tag.E6 K) ^ n : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (hSpan u) =
      hSpan ((Int.castRingHom K).mapMatrix ((Wm l) ^ n) *ᵥ u) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, wordElt_hSpan, pow_succ', map_mul,
      Matrix.mulVec_mulVec]

theorem wordElt_pow_nine {K : Type*} [Field K] [CharP K 2] :
    (wordElt word9 : ModGL Tag.E6 K) ^ 9 = 1 := by
  refine Units.ext (Finsupp.basisSingleOne.ext fun b => ?_)
  rw [Finsupp.coe_basisSingleOne, Units.val_one, Module.End.one_apply]
  beta_reduce
  rcases b with j | ⟨α, hα⟩
  · have h1 : (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hSpan (Pi.single j 1) :=
      hVec_eq_hSpan j
    rw [h1, wordElt_pow_hSpan, Wm_pow_nine, map_one, Matrix.one_mulVec]
  · have h1 := wordElt_pow_rootVec (K := K) word9 9 hα
    rw [rootVec_of_isRoot hα, wordApply_iterate, Wm_pow_nine, Matrix.one_mulVec,
      ← rootVec_of_isRoot hα] at h1
    rw [← rootVec_of_isRoot hα, h1]

def gG {K : Type*} [Field K] :
    ↥(adjointGroup Tag.E6 K) := ⟨wordElt word9, wordElt_mem word9⟩

theorem comm_apply {K : Type*} [Field K] {g h : ModGL Tag.E6 K} (hgh : g * h = h * g)
    (v : RootModule Tag.E6 K) :
    (g : Module.End K (RootModule Tag.E6 K)) ((h : Module.End K (RootModule Tag.E6 K)) v) =
      (h : Module.End K (RootModule Tag.E6 K)) ((g : Module.End K (RootModule Tag.E6 K)) v) := by
  have := congrArg (fun x : ModGL Tag.E6 K => (x : Module.End K (RootModule Tag.E6 K)) v) hgh
  simpa only [Units.val_mul, Module.End.mul_apply] using this

theorem gG_pow_nine {K : Type*} [Field K] [CharP K 2] :
    (gG : ↥(adjointGroup Tag.E6 K)) ^ 9 = 1 :=
  Subtype.ext wordElt_pow_nine

theorem gG_pow_three_not_central {K : Type*} [Field K] [CharP K 2] :
    (gG : ↥(adjointGroup Tag.E6 K)) ^ 3 ∉ Subgroup.center ↥(adjointGroup Tag.E6 K) := by
  intro h
  have hc := Subgroup.mem_center_iff.mp h ⟨nElt i0, nElt_mem i0⟩
  have h0 : IsRoot Tag.E6 e0 := IsRoot.basis i0
  have hg3 : ((gG ^ 3 : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      (wordElt word9 : ModGL Tag.E6 K) ^ 3 := by
    rw [Subgroup.coe_pow]; rfl
  have hc' : (nElt i0 : ModGL Tag.E6 K) * (wordElt word9) ^ 3 =
      (wordElt word9) ^ 3 * (nElt i0 : ModGL Tag.E6 K) := by
    have := congrArg Subtype.val hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hg3] at this
    exact this
  have h2 := comm_apply hc' (rootVec Tag.E6 K e0)
  rw [wordElt_pow_rootVec word9 3 h0, nElt_rootVec i0 (isRoot_iterate word9 3 h0),
    nElt_rootVec i0 h0, wordElt_pow_rootVec word9 3 (IsRoot.reflect i0 h0)] at h2
  have h4 := rootVec_injective (K := K) (IsRoot.reflect _ (isRoot_iterate word9 3 h0))
    (isRoot_iterate word9 3 (IsRoot.reflect _ h0)) h2
  rw [reflect_eq, reflect_eq, wordApply_iterate, wordApply_iterate] at h4
  exact Wm_pow_three_noncomm h4

theorem exists_pow_nine_not_central {K : Type*} [Field K] [CharP K 2] :
    ∃ g : ↥(adjointGroup Tag.E6 K),
      g ^ 9 = 1 ∧ g ^ 3 ∉ Subgroup.center ↥(adjointGroup Tag.E6 K) :=
  ⟨gG, gG_pow_nine, gG_pow_three_not_central⟩

end CFSG.AGLEmbedding.E6Nine
