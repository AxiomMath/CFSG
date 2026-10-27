module

public import CFSG.Monster.B.Pinned.Primes.ThreeAction
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

open CFSG.Monster.B.Pinned
open scoped Matrix

private def letU : ℕ → GL (Fin 8) (ZMod 3)
  | 0 => XThreeU | 1 => XThreeU⁻¹ | 2 => YThreeU | _ => YThreeU⁻¹

private def letRows : ℕ → List (List ℕ)
  | 0 => threeXRows | 1 => threeXiRows | 2 => threeYRows | _ => threeYiRows

private def wordU (w : List ℕ) : GL (Fin 8) (ZMod 3) := w.foldl (fun g l => g * letU l) 1

private def wRows (w : List ℕ) : List (List ℕ) :=
  w.foldl (fun R l => lmul R (letRows l)) (lpow threeXRows 0)

private def Rep (s : GL (Fin 8) (ZMod 3)) (R : List (List ℕ)) : Prop :=
  R.length = 8 ∧ (s : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 R

private theorem Rep.mul {s t : GL (Fin 8) (ZMod 3)} {R R' : List (List ℕ)} (hs : Rep s R)
    (ht : Rep t R') : Rep (s * t) (lmul R R') :=
  ⟨by rw [lmul_length, hs.1], by rw [Units.val_mul, hs.2, ht.2, rowsMat_lmul hs.1]⟩

private theorem Rep.pow {s : GL (Fin 8) (ZMod 3)} {R : List (List ℕ)} (hs : Rep s R) (e : ℕ) :
    Rep (s ^ e) (lpow R e) :=
  ⟨lpow_length R e, by rw [Units.val_pow_eq_pow_val, hs.2, rowsMat_lpow]⟩

private theorem Rep.eq {s t : GL (Fin 8) (ZMod 3)} {R R' : List (List ℕ)} (hs : Rep s R)
    (ht : Rep t R') (h : R = R') : s = t := Units.ext (by rw [hs.2, ht.2, h])

private theorem Rep.ne {s t : GL (Fin 8) (ZMod 3)} {R R' : List (List ℕ)} (hs : Rep s R)
    (ht : Rep t R') (h : rowsMat 3 8 R ≠ rowsMat 3 8 R') : s ≠ t :=
  fun e => h (by rw [← hs.2, ← ht.2, e])

private theorem rep_letU (l : ℕ) : Rep (letU l) (letRows l) := by
  match l with
  | 0 | 1 | 2 | _ + 3 => exact ⟨rfl, rfl⟩

private theorem rep_foldl (w : List ℕ) : ∀ (g : GL (Fin 8) (ZMod 3)) (R : List (List ℕ)),
    Rep g R →
      Rep (w.foldl (fun g l => g * letU l) g) (w.foldl (fun R l => lmul R (letRows l)) R) := by
  induction w with
  | nil => exact fun _ _ h => h
  | cons l w ih => exact fun g R h => ih (g * letU l) (lmul R (letRows l)) (h.mul (rep_letU l))

private theorem rep_wordU (w : List ℕ) : Rep (wordU w) (wRows w) :=
  rep_foldl w 1 _ ⟨lpow_length _ 0, by rw [Units.val_one, rowsMat_lpow, pow_zero]⟩

private theorem wordU_mem (w : List ℕ) : wordU w ∈ KThree := by
  have hX : XThreeU ∈ KThree := Subgroup.subset_closure (Set.mem_insert _ _)
  have hY : YThreeU ∈ KThree := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hl : ∀ l, letU l ∈ KThree
    | 0 => hX | 1 => inv_mem hX | 2 => hY | _ + 3 => inv_mem hY
  suffices h : ∀ g ∈ KThree, w.foldl (fun g l => g * letU l) g ∈ KThree from h 1 (one_mem _)
  induction w with
  | nil => exact fun g hg => hg
  | cons l w ih => exact fun g hg => ih _ (mul_mem hg (hl l))

def ga : GL (Fin 8) (ZMod 3) := wordU [0, 2, 1, 3, 1, 2]

def gb : GL (Fin 8) (ZMod 3) := wordU [0, 2, 2, 1, 3, 0, 2, 0, 2, 1]

def gc : GL (Fin 8) (ZMod 3) := wordU [1, 2, 1, 1, 1, 2, 1, 1, 1, 2]

def gx : GL (Fin 8) (ZMod 3) := wordU [0, 0, 3, 0, 0, 3, 3, 1, 3, 1]

private def aR : List (List ℕ) := wRows [0, 2, 1, 3, 1, 2]
private def bR : List (List ℕ) := wRows [0, 2, 2, 1, 3, 0, 2, 0, 2, 1]
private def cR : List (List ℕ) := wRows [1, 2, 1, 1, 1, 2, 1, 1, 1, 2]
private def xR : List (List ℕ) := wRows [0, 0, 3, 0, 0, 3, 3, 1, 3, 1]
private theorem rep_ga : Rep ga aR := rep_wordU _
private theorem rep_gb : Rep gb bR := rep_wordU _
private theorem rep_gc : Rep gc cR := rep_wordU _
private theorem rep_gx : Rep gx xR := rep_wordU _

private def aEl (k j i : ℕ) : List (List ℕ) := lmul (lpow cR k) (lmul (lpow bR j) (lpow aR i))

private theorem rep_aEl (k j i : ℕ) : Rep (gc ^ k * (gb ^ j * ga ^ i)) (aEl k j i) :=
  (rep_gc.pow k).mul ((rep_gb.pow j).mul (rep_ga.pow i))

theorem gens_mem_KThree : ga ∈ KThree ∧ gb ∈ KThree ∧ gc ∈ KThree ∧ gx ∈ KThree :=
  ⟨wordU_mem _, wordU_mem _, wordU_mem _, wordU_mem _⟩

private theorem pow_three_of_rep {s : GL (Fin 8) (ZMod 3)} {R : List (List ℕ)} (hs : Rep s R)
    (h : lpow R 3 = lpow R 0) : s ^ 3 = 1 := ((hs.pow 3).eq (hs.pow 0) h).trans (pow_zero s)

theorem gens_pow_three : ga ^ 3 = 1 ∧ gb ^ 3 = 1 ∧ gc ^ 3 = 1 ∧ gx ^ 3 = 1 :=
  ⟨pow_three_of_rep rep_ga (by decide +kernel), pow_three_of_rep rep_gb (by decide +kernel),
    pow_three_of_rep rep_gc (by decide +kernel), pow_three_of_rep rep_gx (by decide +kernel)⟩

theorem ga_ne_one : ga ≠ 1 := fun h =>
  rep_ga.ne (rep_ga.pow 0) (by decide +kernel) (h.trans (pow_zero ga).symm)

theorem gens_comm : ga * gb = gb * ga ∧ ga * gc = gc * ga ∧ gb * gc = gc * gb :=
  ⟨(rep_ga.mul rep_gb).eq (rep_gb.mul rep_ga) (by decide +kernel),
    (rep_ga.mul rep_gc).eq (rep_gc.mul rep_ga) (by decide +kernel),
    (rep_gb.mul rep_gc).eq (rep_gc.mul rep_gb) (by decide +kernel)⟩

theorem gx_conj : gx⁻¹ * ga * gx = gb * gc ∧ gx⁻¹ * gb * gx = gb ∧
    gx⁻¹ * gc * gx = ga ^ 2 * (gb ^ 2 * gc ^ 2) := by
  rw [inv_eq_of_mul_eq_one_right ((pow_succ' gx 2).symm.trans gens_pow_three.2.2.2)]
  have h2 := rep_gx.pow 2
  exact ⟨((h2.mul rep_ga).mul rep_gx).eq (rep_gb.mul rep_gc) (by decide +kernel),
    ((h2.mul rep_gb).mul rep_gx).eq rep_gb (by decide +kernel),
    ((h2.mul rep_gc).mul rep_gx).eq ((rep_ga.pow 2).mul ((rep_gb.pow 2).mul (rep_gc.pow 2)))
      (by decide +kernel)⟩

theorem gb_ne_pow : ∀ i < 3, gb ≠ ga ^ i := by
  have h : ∀ i < 3, rowsMat 3 8 bR ≠ rowsMat 3 8 (lpow aR i) := by decide +kernel
  exact fun i hi => rep_gb.ne (rep_ga.pow i) (h i hi)

theorem gc_ne_mul : ∀ j < 3, ∀ i < 3, gc ≠ gb ^ j * ga ^ i := by
  have h : ∀ j < 3, ∀ i < 3, rowsMat 3 8 cR ≠ rowsMat 3 8 (lmul (lpow bR j) (lpow aR i)) := by
    decide +kernel
  exact fun j hj i hi => rep_gc.ne ((rep_gb.pow j).mul (rep_ga.pow i)) (h j hj i hi)

theorem gx_ne_mul : ∀ k < 3, ∀ j < 3, ∀ i < 3, gx ≠ gc ^ k * (gb ^ j * ga ^ i) := by
  have h : ∀ k < 3, ∀ j < 3, ∀ i < 3, rowsMat 3 8 xR ≠ rowsMat 3 8 (aEl k j i) := by
    decide +kernel
  exact fun k hk j hj i hi => rep_gx.ne (rep_aEl k j i) (h k hk j hj i hi)

theorem eq_zero_of_comm_gx : ∀ k < 3, ∀ j < 3, ∀ i < 3,
    gc ^ k * (gb ^ j * ga ^ i) * gx = gx * (gc ^ k * (gb ^ j * ga ^ i)) → k = 0 ∧ i = 0 := by
  have h : ∀ k < 3, ∀ j < 3, ∀ i < 3,
      rowsMat 3 8 (lmul (aEl k j i) xR) = rowsMat 3 8 (lmul xR (aEl k j i)) → k = 0 ∧ i = 0 := by
    decide +kernel
  exact fun k hk j hj i hi e => h k hk j hj i hi (by
    rw [← ((rep_aEl k j i).mul rep_gx).2, ← (rep_gx.mul (rep_aEl k j i)).2, e])

private def badN : List ℕ := [0, 5, 7, 9, 13, 18, 26]

private def elt (t : ℕ) : GL (Fin 8) (ZMod 3) :=
  gx ^ (t / 27) * (gc ^ (t / 9 % 3) * (gb ^ (t / 3 % 3) * ga ^ (t % 3)))
private def eltR (t : ℕ) : List (List ℕ) :=
  lmul (lpow xR (t / 27)) (aEl (t / 9 % 3) (t / 3 % 3) (t % 3))

private theorem rep_elt (t : ℕ) : Rep (elt t) (eltR t) := (rep_gx.pow _).mul (rep_aEl _ _ _)

theorem card_le_seven {S : Set (GL (Fin 8) (ZMod 3))}
    (hS : ∀ s ∈ S, ∃ n < 3, ∃ k < 3, ∃ j < 3, ∃ i < 3, s = gx ^ n * (gc ^ k * (gb ^ j * ga ^ i)))
    (hsq : ∀ s ∈ S, ((s : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) * (s - 1) = 0) :
    Nat.card S ≤ 7 := by
  have h : ∀ t < 81, (rowsMat 3 8 (eltR t) - 1) * (rowsMat 3 8 (eltR t) - 1) = 0 → t ∈ badN := by
    decide +kernel
  classical
  have hsub : S ⊆ ((badN.map elt).toFinset : Set (GL (Fin 8) (ZMod 3))) := by
    intro s hs
    have hs2 := hsq s hs
    obtain ⟨n, hn, k, hk, j, hj, i, hi, rfl⟩ := hS s hs
    have e : gx ^ n * (gc ^ k * (gb ^ j * ga ^ i)) = elt (27 * n + 9 * k + 3 * j + i) := by
      rw [elt, show (27 * n + 9 * k + 3 * j + i) / 27 = n by omega,
        show (27 * n + 9 * k + 3 * j + i) / 9 % 3 = k by omega,
        show (27 * n + 9 * k + 3 * j + i) / 3 % 3 = j by omega,
        show (27 * n + 9 * k + 3 * j + i) % 3 = i by omega]
    rw [e, (rep_elt _).2] at hs2
    rw [e, Finset.mem_coe, List.mem_toFinset]
    exact List.mem_map.2 ⟨_, h _ (by omega) hs2, rfl⟩
  calc Nat.card S ≤ (badN.map elt).toFinset.card := by
        rw [← Nat.card_eq_finsetCard]; exact Nat.card_mono (Finset.finite_toSet _) hsub
    _ ≤ 7 := List.toFinset_card_le _

theorem isometry_gens {s : GL (Fin 8) (ZMod 3)} (hs : s = ga ∨ s = gb ∨ s = gc ∨ s = gx)
    (u v : Fin 8 → ZMod 3) :
    (u ᵥ* (s : Matrix (Fin 8) (Fin 8) (ZMod 3))) ⬝ᵥ
      (MThree *ᵥ (v ᵥ* (s : Matrix (Fin 8) (Fin 8) (ZMod 3)))) = u ⬝ᵥ (MThree *ᵥ v) := by
  obtain ⟨R, hR, hRM⟩ : ∃ R, Rep s R ∧ rowsMat 3 8 R * MThree * (rowsMat 3 8 R)ᵀ = MThree := by
    rcases hs with rfl | rfl | rfl | rfl
    exacts [⟨_, rep_ga, by decide +kernel⟩, ⟨_, rep_gb, by decide +kernel⟩,
      ⟨_, rep_gc, by decide +kernel⟩, ⟨_, rep_gx, by decide +kernel⟩]
  rw [← Matrix.mulVec_transpose _ v, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hR.2, hRM]

private def fixB1 : List (List ℕ) :=
  [[0, 0, 2, 0, 1, 0, 2, 1], [1, 0, 1, 1, 0, 1, 2, 2], [2, 0, 1, 0, 0, 2, 1, 0],
    [0, 0, 1, 2, 0, 1, 1, 0], [], [1, 0, 0, 2, 0, 1, 2, 0]]
private def fixB2 : List (List ℕ) := [[], [0, 0, 1, 2, 2, 1, 1, 0]]
private def fixB3 : List (List ℕ) := [[], [0, 0, 0, 1, 1, 2, 1, 2]]

theorem eq_smul_of_fix {u : Fin 8 → ZMod 3}
    (ha : u ᵥ* (ga : Matrix (Fin 8) (Fin 8) (ZMod 3)) = u)
    (hb : u ᵥ* (gb : Matrix (Fin 8) (Fin 8) (ZMod 3)) = u)
    (hc : u ᵥ* (gc : Matrix (Fin 8) (Fin 8) (ZMod 3)) = u) :
    ∃ r : ZMod 3, u = r • ![0, 2, 2, 1, 0, 1, 1, 0] := by
  have h1 : (rowsMat 3 8 aR - 1) * rowsMat 3 8 fixB1 + (rowsMat 3 8 bR - 1) * rowsMat 3 8 fixB2 +
      (rowsMat 3 8 cR - 1) * rowsMat 3 8 fixB3 +
      Matrix.vecMulVec ![0, 2, 0, 0, 0, 0, 0, 0] ![0, 2, 2, 1, 0, 1, 1, 0] = 1 := by
    decide +kernel
  simp only [rep_ga.2, rep_gb.2, rep_gc.2] at ha hb hc
  refine ⟨u ⬝ᵥ ![0, 2, 0, 0, 0, 0, 0, 0], ?_⟩
  have h := congrArg (u ᵥ* ·) h1
  simp only [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, Matrix.vecMul_sub, Matrix.vecMul_one, ha,
    hb, hc, sub_self, Matrix.zero_vecMul, zero_add, Matrix.vecMul_vecMulVec] at h
  exact h.symm

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

end
