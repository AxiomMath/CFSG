module

public import Certificates.Data.Kernel.HMathieu.Avoid
public import CFSG.Quasithin.Background.HMathieuAvoid
import CFSG.Certificates.Kernel.HMathieu.GreedySound

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

variable {n : Nat}

theorem val_inj {x y : Msk n} (h : x.val = y.val) : x = y := Msk.ext' h

theorem map_subprods (l : List (Msk n)) : (subprods l).map Msk.val = subX (l.map Msk.val) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [subprods, List.map_append, List.map_map, List.map_cons, subX, ← ih, List.map_map]
    rfl

theorem idxOf_map_val (R : List (Msk n)) (x : Msk n) :
    (R.map Msk.val).idxOf x.val = R.idxOf x := by
  induction R with
  | nil => rfl
  | cons a R ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons]
    by_cases h : a = x
    · subst h
      simp
    · have h' : a.val ≠ x.val := fun e => h (val_inj e)
      simp [h, h', ih]

theorem mem_subprods_val {l : List (Msk n)} {x : Msk n} :
    x ∈ subprods l ↔ x.val ∈ subX (l.map Msk.val) := by
  rw [← map_subprods, List.mem_map]
  exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => val_inj e ▸ hy⟩

theorem map_greedyExt (R l : List (Msk n)) :
    (greedyExt R l).map Msk.val = gExtX (R.map Msk.val) (l.map Msk.val) := by
  have hst : startX (R.map Msk.val) (l.map Msk.val) = startPos R l := by
    cases l with
    | nil => rfl
    | cons a l => simp [startX, startPos, pos, idxOf_map_val]
  unfold greedyExt gExtX
  rw [hst, ← List.map_drop, List.filter_map]
  congr 1
  refine List.filter_congr fun x _ => ?_
  simp only [Function.comp_apply]
  have hc : (l.all fun y => decide (x * y = y * x)) = true :=
    List.all_eq_true.2 fun y _ => decide_eq_true (Msk.mul_comm' x y)
  rw [hc, Bool.true_and]
  congr 1
  · rw [Bool.eq_iff_iff, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not,
      ← Bool.not_eq_true, List.contains_iff_mem, mem_subprods_val]
  · rw [← map_subprods, List.all_map]
    refine all_congr_mem fun s _ => ?_
    simp only [Function.comp_apply]
    have h1 : decide (s = 1) = (s.val == 0) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
      exact ⟨fun h => h ▸ rfl, fun h => val_inj h⟩
    rw [h1, pos, pos, ← idxOf_map_val R x, ← idxOf_map_val R (x * s)]
    rfl

theorem forallGreedy_val (R : List (Msk n)) (pred : List (Msk n) → Bool)
    (pred' : List Nat → Bool) (hp : ∀ l, pred l = pred' (l.map Msk.val)) :
    ∀ k l, forallGreedy R pred k l = fGX (R.map Msk.val) pred' k (l.map Msk.val) := by
  intro k
  induction k with
  | zero => intro l; exact hp l
  | succ k ih =>
    intro l
    rw [forallGreedy, fGX, ← map_greedyExt, List.all_map]
    refine all_congr_mem fun x _ => ?_
    simp only [Function.comp_apply]
    rw [ih (x :: l), List.map_cons]

theorem map_avoidList (O F : List Nat) :
    (avoidList n O F).map Msk.val = avoidListX n O F := by
  unfold avoidList avoidListX
  generalize (F.filter fun m => m != 0 && !(m ∈ O)) = G
  induction G with
  | nil => rfl
  | cons m G ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h : m < 2 ^ n
    · simp [h, ih]
    · simp [h, ih]

theorem avoidOK_eq (b : Nat) (O F : List Nat) : avoidOK n b O F = avoidK n b O F := by
  unfold avoidOK avoidK
  rw [forallGreedy_val _ _ (fun l => (subX l).any fun x => x ∈ O), map_avoidList]
  · rfl
  · intro l
    rw [← map_subprods, List.any_map]
    rfl

end CFSG.KC.HMathieu

end
