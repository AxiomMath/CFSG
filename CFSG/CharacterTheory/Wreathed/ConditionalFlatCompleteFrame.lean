module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteCore
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

structure Frame {I H K : Type*} [DecidableEq I] (d : I → ℤ) (A : H → I → ℤ) (E : K → I → ℤ)
    (Ys : I → ℤ) (Y : K → I → ℤ) (C : I → ℤ) (i₀ i₁ i₂ i₃ i₄ : I) (p : H → I)
    (q : K → Fin 4 → I) (δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ) (η : K → Fin 4 → ℤ) (D : ℤ) : Prop where
  inj : Function.Injective
    (Sum.elim ![i₀, i₁, i₂, i₃, i₄] (Sum.elim p fun x : K × Fin 4 => q x.1 x.2))
  sδ₀ : δ₀ = 1 ∨ δ₀ = -1
  sδ₁ : δ₁ = 1 ∨ δ₁ = -1
  sδ₂ : δ₂ = 1 ∨ δ₂ = -1
  sδ₃ : δ₃ = 1 ∨ δ₃ = -1
  sδ₄ : δ₄ = 1 ∨ δ₄ = -1
  sα : α = 1 ∨ α = -1
  sη : ∀ k l, η k l = 1 ∨ η k l = -1
  formA : ∀ h, A h = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ +
    Pi.single (p h) (2 * α)
  formYs : Ys = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ - Pi.single i₂ δ₂ - Pi.single i₃ δ₃
  formC : C = Pi.single i₀ δ₀ - Pi.single i₁ δ₁ + Pi.single i₂ δ₂ - Pi.single i₃ δ₃ +
    Pi.single i₄ (2 * δ₄)
  formE : ∀ k, E k = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ +
    ∑ r, Pi.single (q k r) (η k r)
  formY : ∀ k, Y k = Pi.single (q k 0) (η k 0) + Pi.single (q k 1) (η k 1) -
    Pi.single (q k 2) (η k 2) - Pi.single (q k 3) (η k 3)
  Dpos : 0 < D
  dp : ∀ h, d (p h) = D
  dcore : δ₀ * d i₀ + δ₁ * d i₁ + δ₂ * d i₂ + δ₃ * d i₃ = -2 * α * D
  dpair : ∀ k, η k 0 * d (q k 0) + η k 1 * d (q k 1) = α * D ∧
    η k 2 * d (q k 2) + η k 3 * d (q k 3) = α * D

@[expose] noncomputable def outK {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (i₀ i₁ i₂ i₃ i₄ : I) (p : H → I) (q : Fin 4 → I) : Finset I :=
  Finset.univ.filter fun i => i ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I) ∧ (∀ h, p h ≠ i) ∧
    ∀ l, q l ≠ i

theorem mem_outK {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H] {i₀ i₁ i₂ i₃ i₄ : I}
    {p : H → I} {q : Fin 4 → I} {i : I} :
    i ∈ outK i₀ i₁ i₂ i₃ i₄ p q ↔ i ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I) ∧ (∀ h, p h ≠ i) ∧
      ∀ l, q l ≠ i := by
  simp [outK]

namespace Frame

variable {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype K]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

section Distinct

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype I] [Fintype H] [Fintype K] in
theorem core_inj : Function.Injective ![i₀, i₁, i₂, i₃, i₄] := fun a b h =>
  Sum.inl_injective (F.inj (a₁ := Sum.inl a) (a₂ := Sum.inl b) h)

omit [Fintype I] [Fintype H] [Fintype K] in
theorem p_inj : Function.Injective p := fun a b h =>
  Sum.inl_injective (Sum.inr_injective (F.inj (a₁ := Sum.inr (Sum.inl a))
    (a₂ := Sum.inr (Sum.inl b)) h))

omit [Fintype I] [Fintype H] [Fintype K] in
theorem q_inj {k k' : K} {l l' : Fin 4} (h : q k l = q k' l') : k = k' ∧ l = l' := by
  have h' := Sum.inr_injective (Sum.inr_injective (F.inj (a₁ := Sum.inr (Sum.inr (k, l)))
    (a₂ := Sum.inr (Sum.inr (k', l'))) h))
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

omit [Fintype I] [Fintype H] [Fintype K] in
theorem p_ne_core (h : H) (t : Fin 5) : p h ≠ ![i₀, i₁, i₂, i₃, i₄] t := fun he =>
  Sum.inr_ne_inl (F.inj (a₁ := Sum.inr (Sum.inl h)) (a₂ := Sum.inl t) he)

omit [Fintype I] [Fintype H] [Fintype K] in
theorem q_ne_core (k : K) (l : Fin 4) (t : Fin 5) : q k l ≠ ![i₀, i₁, i₂, i₃, i₄] t := fun he =>
  Sum.inr_ne_inl (F.inj (a₁ := Sum.inr (Sum.inr (k, l))) (a₂ := Sum.inl t) he)

omit [Fintype I] [Fintype H] [Fintype K] in
theorem q_ne_p (k : K) (l : Fin 4) (h : H) : q k l ≠ p h := fun he => by
  have := F.inj (a₁ := Sum.inr (Sum.inr (k, l))) (a₂ := Sum.inr (Sum.inl h)) he
  simp at this

omit [Fintype I] [Fintype H] [Fintype K] in
theorem p_notMem_core (h : H) : p h ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I) := by
  have h0 : p h ≠ i₀ := F.p_ne_core h 0
  have h1 : p h ≠ i₁ := F.p_ne_core h 1
  have h2 : p h ≠ i₂ := F.p_ne_core h 2
  have h3 : p h ≠ i₃ := F.p_ne_core h 3
  have h4 : p h ≠ i₄ := F.p_ne_core h 4
  simp [h0, h1, h2, h3, h4]

omit [Fintype I] [Fintype H] [Fintype K] in
theorem q_notMem_core (k : K) (l : Fin 4) : q k l ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I) := by
  have h0 : q k l ≠ i₀ := F.q_ne_core k l 0
  have h1 : q k l ≠ i₁ := F.q_ne_core k l 1
  have h2 : q k l ≠ i₂ := F.q_ne_core k l 2
  have h3 : q k l ≠ i₃ := F.q_ne_core k l 3
  have h4 : q k l ≠ i₄ := F.q_ne_core k l 4
  simp [h0, h1, h2, h3, h4]

omit [Fintype I] [Fintype H] [Fintype K] in
theorem core_ne : i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₀ ≠ i₃ ∧ i₀ ≠ i₄ ∧ i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₁ ≠ i₄ ∧
    i₂ ≠ i₃ ∧ i₂ ≠ i₄ ∧ i₃ ≠ i₄ :=
  ⟨F.core_inj.ne (by decide : (0 : Fin 5) ≠ 1), F.core_inj.ne (by decide : (0 : Fin 5) ≠ 2),
    F.core_inj.ne (by decide : (0 : Fin 5) ≠ 3), F.core_inj.ne (by decide : (0 : Fin 5) ≠ 4),
    F.core_inj.ne (by decide : (1 : Fin 5) ≠ 2), F.core_inj.ne (by decide : (1 : Fin 5) ≠ 3),
    F.core_inj.ne (by decide : (1 : Fin 5) ≠ 4), F.core_inj.ne (by decide : (2 : Fin 5) ≠ 3),
    F.core_inj.ne (by decide : (2 : Fin 5) ≠ 4), F.core_inj.ne (by decide : (3 : Fin 5) ≠ 4)⟩

omit [Fintype I] [Fintype H] [Fintype K] in
theorem split_inj (k : K) :
    Function.Injective (Sum.elim ![i₀, i₁, i₂, i₃, i₄] (Sum.elim p (q k))) := by
  intro a b hab
  rcases a with a | a | a <;> rcases b with b | b | b
  · exact congrArg Sum.inl (F.core_inj hab)
  · exact absurd hab.symm (F.p_ne_core b a)
  · exact absurd hab.symm (F.q_ne_core k b a)
  · exact absurd hab (F.p_ne_core a b)
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (F.p_inj hab)
  · exact absurd hab.symm (F.q_ne_p k b a)
  · exact absurd hab (F.q_ne_core k a b)
  · exact absurd hab (F.q_ne_p k a b)
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (F.q_inj hab).2

omit [Fintype K] in
theorem sum_split (k : K) (f : I → ℤ) :
    ∑ i, f i = f i₀ + f i₁ + f i₂ + f i₃ + f i₄ + ∑ h, f (p h) + ∑ l, f (q k l) +
      ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), f i := by
  set g : Fin 5 ⊕ H ⊕ Fin 4 → I := Sum.elim ![i₀, i₁, i₂, i₃, i₄] (Sum.elim p (q k)) with hg
  have hginj : Function.Injective g := F.split_inj k
  have hcompl : (Finset.univ.image g)ᶜ = outK i₀ i₁ i₂ i₃ i₄ p (q k) := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists,
      mem_outK]
    constructor
    · intro hi
      refine ⟨?_, fun h => hi (Sum.inr (Sum.inl h)), fun l => hi (Sum.inr (Sum.inr l))⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi (Sum.inl 0) h.symm, fun h => hi (Sum.inl 1) h.symm,
        fun h => hi (Sum.inl 2) h.symm, fun h => hi (Sum.inl 3) h.symm,
        fun h => hi (Sum.inl 4) h.symm⟩
    · rintro ⟨hc, hp, hq⟩ x
      rcases x with t | h | l
      · intro he
        apply hc
        rw [← he]
        fin_cases t <;> simp [g]
      · exact hp h
      · exact hq l
  rw [← Finset.sum_add_sum_compl (Finset.univ.image g),
    Finset.sum_image (fun a _ b _ h => hginj h), hcompl, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fin.sum_univ_five]
  simp only [hg, Sum.elim_inl, Sum.elim_inr]
  have h0 : ![i₀, i₁, i₂, i₃, i₄] 0 = i₀ := rfl
  have h1 : ![i₀, i₁, i₂, i₃, i₄] 1 = i₁ := rfl
  have h2 : ![i₀, i₁, i₂, i₃, i₄] 2 = i₂ := rfl
  have h3 : ![i₀, i₁, i₂, i₃, i₄] 3 = i₃ := rfl
  have h4 : ![i₀, i₁, i₂, i₃, i₄] 4 = i₄ := rfl
  rw [h0, h1, h2, h3, h4]
  ring

end Distinct

section Pairings

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype H] [Fintype K] in
theorem dot_A (v : I → ℤ) (h : H) :
    v ⬝ᵥ A h = δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ + 2 * α * v (p h) := by
  rw [F.formA h]
  simp only [dotProduct_add, dotProduct_single]
  ring

omit [Fintype H] [Fintype K] in
theorem dot_Ys (v : I → ℤ) :
    v ⬝ᵥ Ys = δ₀ * v i₀ + δ₁ * v i₁ - δ₂ * v i₂ - δ₃ * v i₃ := by
  rw [F.formYs]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_single]
  ring

omit [Fintype H] [Fintype K] in
theorem dot_C (v : I → ℤ) :
    v ⬝ᵥ C = δ₀ * v i₀ - δ₁ * v i₁ + δ₂ * v i₂ - δ₃ * v i₃ + 2 * δ₄ * v i₄ := by
  rw [F.formC]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_single]
  ring

omit [Fintype H] [Fintype K] in
theorem dot_E (v : I → ℤ) (k : K) :
    v ⬝ᵥ E k = δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ +
      (η k 0 * v (q k 0) + η k 1 * v (q k 1) + η k 2 * v (q k 2) + η k 3 * v (q k 3)) := by
  rw [F.formE k]
  simp only [dotProduct_add, dotProduct_single, Fin.sum_univ_four]
  ring

omit [Fintype H] [Fintype K] in
theorem dot_Y (v : I → ℤ) (k : K) :
    v ⬝ᵥ Y k = η k 0 * v (q k 0) + η k 1 * v (q k 1) - η k 2 * v (q k 2) -
      η k 3 * v (q k 3) := by
  rw [F.formY k]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_single]
  ring

end Pairings

section Shape

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype K] in
theorem column_shape (hH : 2 ≤ Fintype.card H) (k : K) {v : I → ℤ}
    (hvA : ∀ h, v ⬝ᵥ A h = 0) (hvYs : v ⬝ᵥ Ys = 0) (hvC : v ⬝ᵥ C = 6) (hvE : v ⬝ᵥ E k = 0)
    (hvY : v ⬝ᵥ Y k = 0) (hN : v ⬝ᵥ v - ∑ l, v (q k l) * v (q k l) ≤ 7) :
    (∀ h, v (p h) = 0) ∧
    η k 0 * v (q k 0) + η k 1 * v (q k 1) = 0 ∧ η k 2 * v (q k 2) + η k 3 * v (q k 3) = 0 ∧
    ∃ a : Fin 3, v i₀ = δ₀ * caseZ0 a ∧ v i₁ = -(δ₁ * caseZ0 a) ∧ v i₂ = δ₂ * caseZ2 a ∧
      v i₃ = -(δ₃ * caseZ2 a) ∧ v i₄ = δ₄ * caseW a ∧
      ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i * v i =
        v ⬝ᵥ v - ∑ l, v (q k l) * v (q k l) - caseNorm a := by
  obtain ⟨h₀⟩ : Nonempty H := Fintype.card_pos_iff.mp (by omega)
  have s₀ := sign_mul_self F.sδ₀
  have s₁ := sign_mul_self F.sδ₁
  have s₂ := sign_mul_self F.sδ₂
  have s₃ := sign_mul_self F.sδ₃
  have s₄ := sign_mul_self F.sδ₄
  have sα := sign_mul_self F.sα
  have hα0 : α ≠ 0 := by rcases F.sα with h | h <;> rw [h] <;> norm_num
  have eA := fun h => (F.dot_A v h).symm.trans (hvA h)
  have hκ : ∀ h, α * v (p h) = α * v (p h₀) := by
    intro h
    linarith [eA h, eA h₀]
  set κ := α * v (p h₀) with hκdef
  have hsq : ∀ h, v (p h) * v (p h) = κ * κ := by
    intro h
    rw [← hκ h]
    linear_combination -(v (p h) * v (p h)) * sα
  have hodd : ∑ h, v (p h) * v (p h) = (Fintype.card H : ℤ) * (κ * κ) := by
    rw [Finset.sum_congr rfl fun h _ => hsq h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit := F.sum_split k fun i => v i * v i
  have hvv : v ⬝ᵥ v = ∑ i, v i * v i := rfl
  set R := ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i * v i with hRdef
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have eYs := (F.dot_Ys v).symm.trans hvYs
  have eC := (F.dot_C v).symm.trans hvC
  have eE := (F.dot_E v k).symm.trans hvE
  have eY := (F.dot_Y v k).symm.trans hvY
  obtain ⟨hκ0, a, e0, e1, e2, e3, e4, eR⟩ := core_cases' (z₀ := δ₀ * v i₀) (z₁ := δ₁ * v i₁)
    (z₂ := δ₂ * v i₂) (z₃ := δ₃ * v i₃) (w := δ₄ * v i₄) (κ := κ) (R := R)
    (N := v ⬝ᵥ v - ∑ l, v (q k l) * v (q k l)) (M := Fintype.card H) (by exact_mod_cast hH)
    hN hR (by linear_combination eA h₀) (by linear_combination eYs)
    (by linear_combination eC) (by
      rw [hvv, hsplit, hodd]
      linear_combination (v i₀ * v i₀) * s₀ + (v i₁ * v i₁) * s₁ + (v i₂ * v i₂) * s₂ +
        (v i₃ * v i₃) * s₃ + (v i₄ * v i₄) * s₄)
  refine ⟨fun h => ?_, ?_, ?_, a, ?_, ?_, ?_, ?_, ?_, eR⟩
  · have h1 : α * v (p h) = 0 := by rw [hκ h, hκ0]
    exact (mul_eq_zero.mp h1).resolve_left hα0
  · have hz : δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ = 0 := by
      linear_combination eA h₀ - 2 * hκ0
    linarith
  · have hz : δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ = 0 := by
      linear_combination eA h₀ - 2 * hκ0
    linarith
  · linear_combination δ₀ * e0 - v i₀ * s₀
  · linear_combination δ₁ * e1 - v i₁ * s₁
  · linear_combination δ₂ * e2 - v i₂ * s₂
  · linear_combination δ₃ * e3 - v i₃ * s₃
  · linear_combination δ₄ * e4 - v i₄ * s₄

end Shape

end Frame

end CFSG.Wreathed.FlatComplete
