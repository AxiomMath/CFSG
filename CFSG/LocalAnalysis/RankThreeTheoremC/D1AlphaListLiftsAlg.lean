module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE1
public import CFSG.LocalAnalysis.AGLEmbedding.CoverCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

section Relations

variable {G : Type} [Group G]

theorem HasLiftableTriple.of_relations (y : Fin 3 → G) (hy3 : ∀ i, y i * y i * y i = 1)
    (hcomm : ∀ i j, y i * y j = y j * y i)
    (hind : ∀ a b c : ZMod 3, y 0 ^ a.val * y 1 ^ b.val * y 2 ^ c.val = 1 →
      a = 0 ∧ b = 0 ∧ c = 0)
    (ninv : Fin 3 → G) (hinv : ∀ i, ninv i * y i = y i * y i * ninv i)
    (nsw : Fin 3 → Fin 3 → G)
    (hsw : ∀ i j, i < j → nsw i j * y i = y j * nsw i j ∧ nsw i j * y j = y i * nsw i j) :
    HasLiftableTriple G := by
  have hinvy : ∀ i, (y i)⁻¹ = y i * y i := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hy3 i)
  let D : ModuleSpec G 3 :=
    { n := 3
      m := 0
      a := y
      g := fun j => j.elim0
      M := fun j => j.elim0
      comm := hcomm
      pow := fun i => by rw [pow_succ, pow_two]; exact hy3 i
      indep := fun c hc => by
        have h : y 0 ^ (c 0).val * y 1 ^ (c 1).val * y 2 ^ (c 2).val = 1 := by
          have h1 : (List.finRange 3).map (fun k => y k ^ (c k).val) =
              [y 0 ^ (c 0).val, y 1 ^ (c 1).val, y 2 ^ (c 2).val] := rfl
          rw [h1] at hc
          simpa [mul_assoc] using hc
        obtain ⟨h0, h1, h2⟩ := hind _ _ _ h
        funext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      act := fun j => j.elim0 }
  have hcard : Nat.card (Subgroup.closure (Set.range y)) = 3 ^ 3 :=
    D.card_span Nat.prime_three
  refine ⟨y, fun i => by rw [pow_succ, pow_two]; exact hy3 i, fun i j => hcomm i j, ?_, ?_, ?_⟩
  · rw [hcard]; norm_num
  · intro i
    refine ⟨ninv i, ?_⟩
    rw [hinvy i, mul_inv_eq_iff_eq_mul]
    exact hinv i
  · intro i j hij
    obtain ⟨h1, h2⟩ := hsw i j hij
    refine ⟨nsw i j, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · rw [mul_inv_eq_iff_eq_mul]; exact h1
    · rw [mul_inv_eq_iff_eq_mul]; exact h2

end Relations

theorem primePower_eq_three {q : TauCeti.PrimePower} (h : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 :=
  (Nat.Prime.pow_eq_iff Nat.prime_three).mp (by rw [← TauCeti.PrimePower.card_def]; exact h)

section Module

variable {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p)

theorem moduleSpec_elt_pow [NeZero p] (c : Fin D.n → ZMod p) (k : ℕ) :
    D.elt c ^ k = D.elt (k • c) := by
  induction k with
  | zero => simp [ModuleSpec.elt_zero]
  | succ k ih => rw [pow_succ, ih, ← ModuleSpec.elt_add, succ_nsmul]

theorem moduleSpec_elt_list_sum [NeZero p] (l : List (Fin D.n → ZMod p)) :
    (l.map D.elt).prod = D.elt l.sum := by
  induction l with
  | nil => simp [ModuleSpec.elt_zero]
  | cons u l ih => rw [List.map_cons, List.prod_cons, ih, List.sum_cons, ModuleSpec.elt_add]

theorem sum_smul_col_eq_mulVec [NeZero p] {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p))
    (c : Fin n → ZMod p) :
    ((List.finRange n).map fun k => (c k).val • fun r => M r k).sum = M.mulVec c := by
  funext r
  rw [Pi.list_sum_apply, List.map_map, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Function.comp_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

theorem moduleSpec_conj_elt [Fact p.Prime] (j : Fin D.m) (c : Fin D.n → ZMod p) :
    D.g j * D.elt c * (D.g j)⁻¹ = D.elt ((D.M j).mulVec c) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : D.g j * D.elt c * (D.g j)⁻¹ =
      ((List.finRange D.n).map fun k => (D.g j * D.a k * (D.g j)⁻¹) ^ (c k).val).prod := by
    unfold ModuleSpec.elt
    have h := map_list_prod (MulAut.conj (D.g j))
      ((List.finRange D.n).map fun k => D.a k ^ (c k).val)
    simp only [MulAut.conj_apply] at h
    rw [h, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    rw [map_pow, MulAut.conj_apply]
  have h2 : ((List.finRange D.n).map fun k => (D.g j * D.a k * (D.g j)⁻¹) ^ (c k).val) =
      ((List.finRange D.n).map fun k => (c k).val • fun r => D.M j r k).map D.elt := by
    rw [List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, moduleSpec_elt_pow, ← D.elt_col]
  rw [h1, h2, moduleSpec_elt_list_sum D, sum_smul_col_eq_mulVec]

theorem moduleSpec_conj_elt_list [Fact p.Prime] (w : List (Fin D.m)) (c : Fin D.n → ZMod p) :
    (w.map D.g).prod * D.elt c * ((w.map D.g).prod)⁻¹ = D.elt (((w.map D.M).prod).mulVec c) := by
  induction w generalizing c with
  | nil => simp
  | cons j w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_inv_rev,
      show D.g j * (w.map D.g).prod * D.elt c * ((w.map D.g).prod⁻¹ * (D.g j)⁻¹) =
        D.g j * ((w.map D.g).prod * D.elt c * (w.map D.g).prod⁻¹) * (D.g j)⁻¹ by group,
      ih, moduleSpec_conj_elt, Matrix.mulVec_mulVec]

theorem HasLiftableTriple.of_moduleSpec (D : ModuleSpec X 3) (v : Fin 3 → (Fin D.n → ZMod 3))
    (hv : ∀ a b c : ZMod 3, a • v 0 + b • v 1 + c • v 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (winv : Fin 3 → List (Fin D.m))
    (hinv : ∀ i, ((winv i).map D.M).prod.mulVec (v i) = -v i)
    (wsw : Fin 3 → Fin 3 → List (Fin D.m))
    (hsw : ∀ i j, i < j → ((wsw i j).map D.M).prod.mulVec (v i) = v j ∧
      ((wsw i j).map D.M).prod.mulVec (v j) = v i) : HasLiftableTriple X := by
  have hcube : ∀ u : Fin D.n → ZMod 3, u + u + u = 0 := by
    intro u
    funext r
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize u r = x
    revert x
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : ∀ i, D.elt (v i) * D.elt (v i) * D.elt (v i) = 1 := fun i => by
    rw [← D.elt_add, ← D.elt_add, hcube, D.elt_zero]
  have hinvy : ∀ i, (D.elt (v i))⁻¹ = D.elt (v i) * D.elt (v i) := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hy3 i)
  refine HasLiftableTriple.of_relations (fun i => D.elt (v i)) hy3
    (fun i j => D.mul_comm_of_mem (D.elt_mem _) (D.elt_mem _)) ?_
    (fun i => ((winv i).map D.g).prod) (fun i => ?_) (fun i j => ((wsw i j).map D.g).prod)
    (fun i j hij => ?_)
  · intro a b c h
    simp only [moduleSpec_elt_pow] at h
    rw [← D.elt_add, ← D.elt_add, ← D.elt_zero] at h
    have h0 := D.elt_injective h
    simp only [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val] at h0
    exact hv a b c h0
  · have h := moduleSpec_conj_elt_list D (winv i) (v i)
    have e : D.elt (-v i) = (D.elt (v i))⁻¹ := D.elt_neg (v i)
    rw [hinv i, e, hinvy i] at h
    exact (mul_inv_eq_iff_eq_mul.mp h)
  · obtain ⟨h1, h2⟩ := hsw i j hij
    have e1 := moduleSpec_conj_elt_list D (wsw i j) (v i)
    have e2 := moduleSpec_conj_elt_list D (wsw i j) (v j)
    rw [h1] at e1
    rw [h2] at e2
    exact ⟨mul_inv_eq_iff_eq_mul.mp e1, mul_inv_eq_iff_eq_mul.mp e2⟩

end Module

end CFSG.LocalAnalysis.RankThreeTheoremC
