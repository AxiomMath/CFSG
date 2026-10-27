module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Ly.KeySpec

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped MatrixGroups

theorem isQuasisimple_sl25 : CFSG.IsQuasisimple (SL(2, ZMod 5)) := by
  have h4 : ∃ s : Finset (ZMod 5), s.card = 4 := ⟨{0, 1, 2, 3}, by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := ZMod 5) (n := 2) le_rfl
    (Or.inr h4)
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 5) (n := 2)
    le_rfl (Or.inr h4)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hpq : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = ⊥ := by
    rw [_root_.commutator_def, eq_bot_iff, commutator_le]
    intro a _ b _
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab a b)]
    exact one_mem _
  have hpq' : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = ⊤ := by
    have h1 := (Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' (center (SL(2, ZMod 5)))) (QuotientGroup.mk'_surjective _)).1
    exact h1
  rw [hpq] at hpq'
  obtain ⟨x, hx⟩ := exists_ne (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))
  have : x ∈ (⊥ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) :=
    hpq' ▸ mem_top x
  exact hx (mem_bot.mp this)

@[expose] def sl25NegOne : SL(2, ZMod 5) :=
  ⟨Matrix.scalar (Fin 2) (4 : ZMod 5), by decide⟩

theorem coe_sl25NegOne : ((sl25NegOne : SL(2, ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 5)) = -1 := by
  decide

theorem coe_sl25NegOne_scalar :
    ((sl25NegOne : SL(2, ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      Matrix.scalar (Fin 2) (4 : ZMod 5) :=
  rfl

theorem sl25NegOne_mul_comm (g : SL(2, ZMod 5)) : g * sl25NegOne = sl25NegOne * g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl25NegOne_scalar]
  exact (Matrix.scalar_commute (4 : ZMod 5) (fun r => Commute.all _ r) _).eq.symm

theorem orderOf_sl25NegOne : orderOf sl25NegOne = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [sq, Matrix.SpecialLinearGroup.coe_mul, coe_sl25NegOne_scalar,
      Matrix.SpecialLinearGroup.coe_one]
    decide
  · intro h
    have h1 := congrArg (fun g : SL(2, ZMod 5) => (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) h
    simp only [coe_sl25NegOne_scalar, Matrix.SpecialLinearGroup.coe_one] at h1
    exact absurd h1 (by decide)

theorem zmod5_mul_eq_zero : ∀ x y : ZMod 5, x * y = 0 → x = 0 ∨ y = 0 := by decide

theorem zmod5_sq_eq_one : ∀ x : ZMod 5, x * x = 1 → x = 1 ∨ x = -1 := by decide

theorem zmod5_two_ne_zero : (2 : ZMod 5) ≠ 0 := by decide

theorem zmod5_one_eq : (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![1, 0; 0, 1] := by decide

theorem zmod5_neg_one_eq : (-1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![-1, 0; 0, -1] := by decide

theorem sl25_eq_one_or_eq_negOne {g : SL(2, ZMod 5)} (hg : g * g = 1) :
    g = 1 ∨ g = sl25NegOne := by
  obtain ⟨M, hM⟩ := g
  have hMM : M * M = 1 := congrArg Subtype.val hg
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hM
    exact hM
  have e00 := congrFun (congrFun hMM 0) 0
  have e01 := congrFun (congrFun hMM 0) 1
  have e10 := congrFun (congrFun hMM 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10
  set a := M 0 0 with ha
  set b := M 0 1 with hb
  set c := M 1 0 with hc
  set d := M 1 1 with hd
  by_cases hs : a + d = 0
  · exfalso
    exact zmod5_two_ne_zero (by linear_combination -(e00 + hdet) + a * hs)
  have hb0 : b = 0 := (zmod5_mul_eq_zero b (a + d) (by linear_combination e01)).resolve_right hs
  have hc0 : c = 0 := (zmod5_mul_eq_zero c (a + d) (by linear_combination e10)).resolve_right hs
  rw [hb0, hc0] at hdet e00
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at e00
    simp only [mul_zero, add_zero] at e00
    exact absurd e00 (by decide)
  have hda : d = a := by
    have h1 := (zmod5_mul_eq_zero a (d - a) (by linear_combination hdet - e00)).resolve_left ha0
    linear_combination h1
  have hMeq : ∀ x : ZMod 5, a = x → M = !![x, 0; 0, x] := by
    intro x hx
    ext i j
    fin_cases i <;> fin_cases j
    · exact hx
    · exact hb0
    · exact hc0
    · exact hda.trans hx
  rcases zmod5_sq_eq_one a (by linear_combination e00) with h | h
  · left
    apply Subtype.ext
    change M = 1
    rw [hMeq 1 h, zmod5_one_eq]
  · right
    apply Subtype.ext
    rw [coe_sl25NegOne]
    change M = -1
    rw [hMeq (-1) h, zmod5_neg_one_eq]

theorem pRank_le_one_of_forall_sq_eq_one {X : Type*} [Group X] [Finite X] (z : X)
    (h : ∀ x : X, x ^ 2 = 1 → x = 1 ∨ x = z) : CFSG.pRank 2 X ≤ 1 := by
  rw [SectionRank.pRank_eq_open_pRank_top]
  refine SectionRank.pRank_le one_lt_two fun E _ hE => ?_
  rw [pow_one]
  have hsub : (E : Set X) ⊆ {1, z} := fun x hx => by
    rcases h x (hE.2 x hx) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  calc Nat.card E = Nat.card ↥(E : Set X) := rfl
    _ = (E : Set X).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, z} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({z} : Set X).ncard + 1 := Set.ncard_insert_le 1 {z}
    _ = 2 := by rw [Set.ncard_singleton]

theorem pRank_le_one_of_mulEquiv_sl25 {X : Type*} [Group X] [Finite X]
    (e : X ≃* SL(2, ZMod 5)) : CFSG.pRank 2 X ≤ 1 := by
  refine pRank_le_one_of_forall_sq_eq_one (e.symm sl25NegOne) fun x hx => ?_
  have h1 : e x * e x = 1 := by rw [← map_mul, ← sq, hx, map_one]
  rcases sl25_eq_one_or_eq_negOne h1 with h2 | h2
  · left
    rw [← e.symm_apply_apply x, h2, map_one]
  · right
    rw [← e.symm_apply_apply x, h2]

end CFSG.ComponentClassification.FooteLit
