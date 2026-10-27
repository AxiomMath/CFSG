module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LPres
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import Certificates.Certificate442316
public import Certificates.Data.Y2L.Coset

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem y2l_canon_foldl : ∀ (w c : List ℕ), canon14 c = true →
    canon14 (w.foldl (fun acc i => mul14 acc (y2l_ngGen i)) c) = true
  | [], _, h => h
  | _ :: w, _, _ => y2l_canon_foldl w _ (canon14_mul14 _ _)

theorem y2l_ng_check :
    (∀ i ∈ [0, 1, 2, 3], y2l_ngWord [i, i, i] = one14) ∧
      (∀ r ∈ y2l_ws26 1 true, y2l_ngWord (y2l_ngSubst (y2l_ngW ()) r) = one14) ∧
      ∀ r ∈ y2l_ws7 1, y2l_ngWord (y2l_ngSubst (y2l_ngW ()) r) ≠ one14 := by
  have h := (Certificates.certificate442316 : y2l_ngCheck () = true)
  simp only [y2l_ngCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] noncomputable def y2l_ngGenR (i : ℕ) : ↥R3 :=
  [⟨gX 0, gX_mem 0⟩, ⟨gX 1, gX_mem 1⟩, ⟨gY 0, gY_mem 0⟩, ⟨gY 1, gY_mem 1⟩].getD i 1

theorem y2l_coe_ngGenR : ∀ i : ℕ,
    (((y2l_ngGenR i : ↥R3) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      dec14 (y2l_ngGen i)
  | 0 => coe_gX0
  | 1 => coe_gX1
  | 2 => coe_gY0
  | 3 => coe_gY1
  | _ + 4 => by
    show (((1 : ↥R3) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 one14
    simp [dec14_one14]

@[expose] noncomputable def y2l_ngEltR (w : List ℕ) : ↥R3 := (w.map y2l_ngGenR).prod

theorem y2l_ngEltR_append (w w' : List ℕ) :
    y2l_ngEltR (w ++ w') = y2l_ngEltR w * y2l_ngEltR w' := by
  simp only [y2l_ngEltR, List.map_append, List.prod_append]

theorem y2l_ngEltR_cons (i : ℕ) (w : List ℕ) :
    y2l_ngEltR (i :: w) = y2l_ngGenR i * y2l_ngEltR w := by
  simp only [y2l_ngEltR, List.map_cons, List.prod_cons]

theorem y2l_coe_mul_ngEltR : ∀ (w : List ℕ) (g : ↥R3) (c : List ℕ),
    ((g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 c →
    (((g * y2l_ngEltR w : ↥R3) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      dec14 (w.foldl (fun acc i => mul14 acc (y2l_ngGen i)) c)
  | [], g, c, h => by
    rw [y2l_ngEltR, List.map_nil, List.prod_nil, mul_one, List.foldl_nil]
    exact h
  | i :: w, g, c, h => by
    rw [y2l_ngEltR_cons, ← mul_assoc, List.foldl_cons]
    refine y2l_coe_mul_ngEltR w _ _ ?_
    rw [Subgroup.coe_mul, Units.val_mul, h, y2l_coe_ngGenR, dec14_mul14]

theorem y2l_coe_ngEltR (w : List ℕ) :
    (((y2l_ngEltR w : ↥R3) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      dec14 (y2l_ngWord w) := by
  have h := y2l_coe_mul_ngEltR w 1 one14 (by simp [dec14_one14])
  rwa [one_mul] at h

theorem y2l_ngEltR_eq_one_iff (w : List ℕ) : y2l_ngEltR w = 1 ↔ y2l_ngWord w = one14 := by
  constructor
  · intro h
    refine dec14_injective (y2l_canon_foldl w one14 canon14_one14) canon14_one14 ?_
    rw [← y2l_coe_ngEltR, h, dec14_one14]
    simp
  · intro h
    apply Subtype.ext
    apply Units.ext
    rw [y2l_coe_ngEltR, h, dec14_one14]
    simp

theorem y2l_ngGenR_cube (i : ℕ) : y2l_ngGenR i ^ 3 = 1 := by
  by_cases hi : i < 4
  · have h := y2l_ng_check.1 i (by interval_cases i <;> decide)
    rw [← y2l_ngEltR_eq_one_iff, y2l_ngEltR_cons, y2l_ngEltR_cons, y2l_ngEltR_cons,
      y2l_ngEltR, List.map_nil, List.prod_nil, mul_one] at h
    rw [pow_three, h]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
    show (1 : ↥R3) ^ 3 = 1
    exact one_pow 3

theorem y2l_ngEltR_ngInv (w : List ℕ) :
    y2l_ngEltR (y2l_ngInv w) = (y2l_ngEltR w)⁻¹ := by
  induction w with
  | nil => simp [y2l_ngInv, y2l_ngEltR]
  | cons i w ih =>
    have e : y2l_ngInv (i :: w) = y2l_ngInv w ++ [i, i] := by
      simp [y2l_ngInv]
    have hi : (y2l_ngGenR i)⁻¹ = y2l_ngGenR i * y2l_ngGenR i :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_three, y2l_ngGenR_cube])
    have h2 : y2l_ngEltR [i, i] = y2l_ngGenR i * y2l_ngGenR i := by
      simp only [y2l_ngEltR, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
    rw [e, y2l_ngEltR_append, ih, h2, y2l_ngEltR_cons, _root_.mul_inv_rev, hi]

@[expose] noncomputable def y2l_ngElt (i : Fin 5) : ↥R3 := y2l_ngEltR ((y2l_ngW ()).getD i [])

theorem y2l_lift_ngElt (r : List (Fin 5 × Bool)) :
    FreeGroup.lift y2l_ngElt (FreeGroup.mk r) = y2l_ngEltR (y2l_ngSubst (y2l_ngW ()) r) := by
  rw [FreeGroup.lift_mk]
  induction r with
  | nil => simp [y2l_ngSubst, y2l_ngEltR]
  | cons l r ih =>
    simp only [y2l_ngSubst, List.flatMap_cons, List.map_cons, List.prod_cons,
      y2l_ngEltR_append] at ih ⊢
    rw [ih]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [y2l_ngElt, y2l_ngEltR_ngInv]

theorem y2l_ng_rels :
    (∀ x ∈ rels26 1 true, FreeGroup.lift y2l_ngElt x = 1) ∧
      ∀ y ∈ y2l_ws7 1, FreeGroup.lift y2l_ngElt (FreeGroup.mk y) ≠ 1 := by
  obtain ⟨-, hrel, h7⟩ := y2l_ng_check
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [y2l_rels26_eq, Set.mem_setOf_eq] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    rw [y2l_lift_ngElt, y2l_ngEltR_eq_one_iff]
    exact hrel r hr
  · rw [y2l_lift_ngElt, Ne, y2l_ngEltR_eq_one_iff]
    exact h7 y hy

end CFSG.OddStandard.HigherRank.G2Three.Sec2
