module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.SectionRank.ClassicalOdd

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type*} [Field K]

@[expose] def linBlock (n a b : ℕ) (s : Fin a × Fin b → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if h : i.val < a ∧ a ≤ j.val ∧ j.val < a + b then
    s (⟨i.val, h.1⟩, ⟨j.val - a, by omega⟩) else 0

theorem linBlock_add (n a b : ℕ) (s s' : Fin a × Fin b → K) :
    linBlock n a b (s + s') = linBlock n a b s + linBlock n a b s' := by
  ext i j
  by_cases h : i.val < a ∧ a ≤ j.val ∧ j.val < a + b <;> simp [linBlock, h]

theorem linBlock_zero (n a b : ℕ) : linBlock n a b (0 : Fin a × Fin b → K) = 0 := by
  ext i j
  simp [linBlock]

theorem linBlock_mul (n a b : ℕ) (s s' : Fin a × Fin b → K) :
    linBlock n a b s * linBlock n a b s' = 0 := by
  ext i k
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [linBlock, of_apply]
  split_ifs with h1 h2 <;> first | omega | simp

theorem linBlock_injective {n a b : ℕ} (hab : a + b ≤ n) :
    Function.Injective (linBlock (K := K) n a b) := by
  intro s s' h
  funext x
  obtain ⟨i, j⟩ := x
  have h1 := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨a + j.val, by omega⟩
  simp only [linBlock, of_apply] at h1
  rw [dite_eq_left ⟨i.2, by omega, by omega⟩, dite_eq_left ⟨i.2, by omega, by omega⟩] at h1
  simpa using h1

@[expose] noncomputable def linHom (n a b : ℕ) :
    Multiplicative (Fin a × Fin b → K) →* GL (Fin n) K :=
  glOfAdd (fun s => 1 + linBlock n a b s) (by rw [linBlock_zero, add_zero]) (fun s s' => by
    simp only [linBlock_add, mul_add, add_mul, one_mul, mul_one, linBlock_mul, add_zero]
    abel)

theorem linHom_injective {n a b : ℕ} (hab : a + b ≤ n) :
    Function.Injective (linHom (K := K) n a b) :=
  glOfAdd_injective fun _ _ h => linBlock_injective hab (add_left_cancel h)

theorem linHom_mulVec {n a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ n) (s) :
    (linHom (K := K) n a b s : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single ⟨0, by omega⟩ 1 =
      Pi.single ⟨0, by omega⟩ 1 := by
  rw [linHom, coe_glOfAdd, add_mulVec, one_mulVec, mulVec_single_one, add_eq_left]
  ext i
  simp only [col_apply, linBlock, of_apply, Pi.zero_apply]
  split_ifs with h
  · have := h.2.1
    simp at this
    omega
  · rfl

theorem le_pRank_SL {n a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ n) {K : Type} [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f) :
    f * (a * b) ≤ pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  have := charP_of_card hK
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) ?_ (linHom n a b) (linHom_injective hab)
    (fun s => Subgroup.subset_closure (det_eq_one_of_hom (p := p) _ s))
    (v := Pi.single ⟨0, by omega⟩ 1) (by simp) (linHom_mulVec ha hab)
  rw [card_multiplicative_fun hK, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end CFSG.SectionRank.ClassicalOdd
