module

public import CFSG.RankThree.PartOne.KE8F.Stab5Fix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE8F
open CFSG.RankThree.E6 (charVal charVal_add charVal_neg charVal_smul charVal_single)

@[expose] def dualReflect {R : Type*} [CommRing R] (τ : Tag) (i : Fin τ.rank) (z : Fin τ.rank → R) :
    Fin τ.rank → R :=
  fun j => z j - (τ.cartan i j : R) * z i

theorem charVal_reflect {R : Type*} [CommRing R] (τ : Tag) (i : Fin τ.rank) (z : Fin τ.rank → R)
    (v : Fin τ.rank → ℤ) : charVal z (reflect τ i v) = charVal (dualReflect τ i z) v := by
  have h : charVal z (reflect τ i v) =
      charVal z v - ((∑ j, τ.cartan i j * v j : ℤ) : R) * z i := by
    rw [reflect, sub_eq_add_neg, charVal_add, charVal_neg, charVal_smul, charVal_single,
      sub_eq_add_neg]
  rw [h]
  simp only [charVal, dualReflect, mul_sub, Finset.sum_sub_distrib, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem charVal_wordProd_smul {R : Type*} [CommRing R] (τ : Tag) (ω : List (Fin τ.rank))
    (z : Fin τ.rank → R) (v : Fin τ.rank → ℤ) :
    charVal z ((coxeterSystem τ).wordProd ω • v) =
      charVal (ω.foldl (fun z i => dualReflect τ i z) z) v := by
  induction ω generalizing z with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, simple_smul, charVal_reflect, ih, List.foldl_cons]

theorem exists_smul_eq_single_four_of_foldl {z : Fin Tag.E8.rank → ZMod 5}
    {ω : List (Fin Tag.E8.rank)}
    (h : ω.foldl (fun z i => dualReflect Tag.E8 i z) z = Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal z (u • v) = charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v :=
  ⟨(coxeterSystem Tag.E8).wordProd ω, fun v => by rw [charVal_wordProd_smul, h]⟩

@[expose] def e8FiveOrbTab : List (List (Fin Tag.E8.rank)) :=
  [[],
   [2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3,
     4],
   [0, 2, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2,
     1, 3, 4],
   [0, 2, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3,
     4],
   [2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2,
     1, 3, 4],
   [],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3,
     4],
   [3, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2,
     1, 3, 4],
   [1, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3,
     4],
   [3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2,
     1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3,
     0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
   [2, 3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3,
     4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2,
     1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4,
     2, 3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2,
     3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4,
     2, 3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3,
     0, 2, 1, 3, 4],
   [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1,
     3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
   [3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3,
     4],
   [3, 2, 1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2,
     1, 3, 4],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5,
     4, 3, 0, 2, 1, 3, 4],
   [],
   [3, 2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0,
     2, 1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1,
     3, 4],
   [3, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 2,
     3, 0, 2, 1, 3, 4],
   [],
   [4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [2, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1,
     3, 4],
   [3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
     2, 1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3,
     0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0,
     2, 1, 3, 4],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
     2, 1, 3, 4],
   [2, 1, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0,
     2, 1, 3, 4],
   [1, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
     2, 1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2,
     3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4],
   [1, 3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0,
     2, 1, 3, 4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4,
     3, 0, 2, 1, 3, 4],
   [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1,
     3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
   [0, 2, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4],
   [2, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4],
   [],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4],
   [3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3,
     4, 5, 4, 2, 3, 0, 2, 1, 3, 4],
   [],
   [4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [2, 1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0,
     2, 1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0,
     2, 1, 3, 4],
   [1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
     2, 1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3,
     0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
   [3, 2, 1, 3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
     2, 1, 3, 4],
   [2, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1,
     3, 4],
   [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 2,
     3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2,
     3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4],
   [0, 2, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [2, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0,
     2, 1, 3, 4],
   [3, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2,
     3, 0, 2, 1, 3, 4],
   [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1,
     3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
   [1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1,
     3, 4],
   [2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0,
     2, 1, 3, 4],
   [],
   [2, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3,
     4],
   [1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3,
     4],
   [2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2,
     1, 3, 4],
   [],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3,
     4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2,
     1, 3, 4],
   [0, 2, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2,
     1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3,
     0, 2, 1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3,
     0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
   [2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4],
   [4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4],
   [3, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2,
     1, 3, 4],
   [3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2,
     1, 3, 4],
   [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2,
     3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4],
   [3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4],
   [3, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2,
     1, 3, 4],
   [4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3,
     4],
   [2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4,
     2, 3, 0, 2, 1, 3, 4],
   [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1,
     3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
   [0, 2, 1, 3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3,
     4],
   [0, 2, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3,
     4],
   [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5,
     2, 3, 0, 2, 1, 3, 4],
   [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5,
     4, 3, 0, 2, 1, 3, 4]]

@[expose] def e8FiveOrbWord (m : ℕ) (a b : ZMod 5) : List (Fin Tag.E8.rank) :=
  e8FiveOrbTab.getD (25 * (m - 1) + 5 * a.val + b.val) []

theorem e8FiveOrbCheck1 : ∀ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) →
    (e8FiveOrbWord 1 a b).foldl (fun z i => dualReflect Tag.E8 i z) (e8FiveFixH1 ![a, b]) =
      Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5) := by
  decide +kernel

theorem e8FiveOrbCheck2 : ∀ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) →
    (e8FiveOrbWord 2 a b).foldl (fun z i => dualReflect Tag.E8 i z) (e8FiveFixH2 ![a, b]) =
      Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5) := by
  decide +kernel

theorem e8FiveOrbCheck3 : ∀ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) →
    (e8FiveOrbWord 3 a b).foldl (fun z i => dualReflect Tag.E8 i z) (e8FiveFixH3 ![a, b]) =
      Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5) := by
  decide +kernel

theorem e8FiveOrbCheck4 : ∀ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) →
    (e8FiveOrbWord 4 a b).foldl (fun z i => dualReflect Tag.E8 i z) (e8FiveFixH4 ![a, b]) =
      Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5) := by
  decide +kernel

theorem e8FiveOrb_exists_coords {c : Fin 2 → ZMod 5} (hc : c ≠ 0) :
    ∃ a b : ZMod 5, c = ![a, b] ∧ (a ≠ 0 ∨ b ≠ 0) := by
  refine ⟨c 0, c 1, funext fun i => by fin_cases i <;> rfl, ?_⟩
  by_contra h
  obtain ⟨h0, h1⟩ := not_or.1 h
  exact hc (funext fun i => by fin_cases i <;> simp [not_not.1 h0, not_not.1 h1])

theorem e8FiveFixH1_orbit (c : Fin 2 → ZMod 5) (hc : c ≠ 0) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal (e8FiveFixH1 c) (u • v) =
        charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  obtain ⟨a, b, rfl, hab⟩ := e8FiveOrb_exists_coords hc
  exact exists_smul_eq_single_four_of_foldl (e8FiveOrbCheck1 a b hab)

theorem e8FiveFixH2_orbit (c : Fin 2 → ZMod 5) (hc : c ≠ 0) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal (e8FiveFixH2 c) (u • v) =
        charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  obtain ⟨a, b, rfl, hab⟩ := e8FiveOrb_exists_coords hc
  exact exists_smul_eq_single_four_of_foldl (e8FiveOrbCheck2 a b hab)

theorem e8FiveFixH3_orbit (c : Fin 2 → ZMod 5) (hc : c ≠ 0) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal (e8FiveFixH3 c) (u • v) =
        charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  obtain ⟨a, b, rfl, hab⟩ := e8FiveOrb_exists_coords hc
  exact exists_smul_eq_single_four_of_foldl (e8FiveOrbCheck3 a b hab)

theorem e8FiveFixH4_orbit (c : Fin 2 → ZMod 5) (hc : c ≠ 0) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal (e8FiveFixH4 c) (u • v) =
        charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  obtain ⟨a, b, rfl, hab⟩ := e8FiveOrb_exists_coords hc
  exact exists_smul_eq_single_four_of_foldl (e8FiveOrbCheck4 a b hab)

section FixSet


theorem orbit_of_param {z : Fin Tag.E8.rank → ZMod 5}
    {F : (Fin 2 → ZMod 5) → Fin Tag.E8.rank → ZMod 5} (hF0 : F 0 = 0) (hzF : z = F ![z 4, z 7])
    (hz0 : z ≠ 0)
    (horb : ∀ c : Fin 2 → ZMod 5, c ≠ 0 → ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal (F c) (u • v) = charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal z (u • v) = charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  have hc : (![z 4, z 7] : Fin 2 → ZMod 5) ≠ 0 := fun h => hz0 (by rw [hzF, h, hF0])
  rw [hzF]
  exact horb _ hc

theorem fixSet_e8FiveH_orbit {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet (e8FiveH m)) (hz0 : z ≠ 0) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal z (u • v) = charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  interval_cases m
  · exact orbit_of_param (by decide) (fixSet_h1_param hz) hz0 e8FiveFixH1_orbit
  · exact orbit_of_param (by decide) (fixSet_h2_param hz) hz0 e8FiveFixH2_orbit
  · exact orbit_of_param (by decide) (fixSet_h3_param hz) hz0 e8FiveFixH3_orbit
  · exact orbit_of_param (by decide) (fixSet_h4_param hz) hz0 e8FiveFixH4_orbit

end FixSet

end CFSG.LieType.SeitzGeneration.ExcHigh
