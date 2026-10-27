module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.ClassicalInvolution.Q3.Q3ZEval
public import CFSG.ClassicalInvolution.WeakCT.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (mem_closure_sl2)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt E mat_elt)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock longBlock_sl2Upper
  longBlock_sl2Lower shortBlock_sl2Upper shortBlock_sl2Lower)
open TauCeti.GLSymplecticFin (RootSubgroupIndex)
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

section Cube

variable {m : ℕ}

@[expose] def evalCube {M : Type*} [Monoid M] (n : Fin m → M) (w : List (Fin m × Bool)) : M :=
  (w.map fun p => if p.2 then n p.1 else n p.1 * n p.1).prod

theorem map_evalW {G M : Type*} [Group G] [Monoid M] (ρ : G →* M) (g : Fin m → G)
    (hg : ∀ i, g i * g i * g i = 1) (w : List (Fin m × Bool)) :
    ρ (evalW g w) = evalCube (fun i => ρ (g i)) w := by
  induction w with
  | nil => simp [evalCube]
  | cons p w ih =>
    rw [evalW_cons, map_mul, ih]
    simp only [evalCube, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := p
    cases b
    · have h : (g i)⁻¹ = g i * g i :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hg i)
      simp [h]
    · simp

theorem relsHold_of_evalCube {G M : Type*} [Group G] [Monoid M] (ρ : G →* M)
    (hρ : Function.Injective ρ) (g : Fin m → G) (n : Fin m → M) (hn : ∀ i, ρ (g i) = n i)
    (hcube : ∀ i, n i * n i * n i = 1) {ws : List (List (Fin m × Bool))}
    (h : ∀ w ∈ ws, evalCube n w = 1) : RelsHold g ws := by
  have hg : ∀ i, g i * g i * g i = 1 := fun i =>
    hρ (by rw [map_mul, map_mul, map_one, hn]; exact hcube i)
  intro w hw
  apply hρ
  rw [map_evalW ρ g hg, map_one]
  have h' : (fun i => ρ (g i)) = n := funext hn
  rw [h']
  exact h w hw

end Cube

@[expose] noncomputable def xpS : SL(2, ZMod 3) := sl2Upper 1

@[expose] noncomputable def xmS : SL(2, ZMod 3) := sl2Lower 1

theorem xpS_eq : xpS = sl2Upper 1 := rfl

theorem xmS_eq : xmS = sl2Lower 1 := rfl

theorem coe_xpS : (xpS : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 1; 0, 1] := rfl

theorem coe_xmS : (xmS : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 0; 1, 1] := rfl

private theorem sl2Upper_mem_closure (c : ZMod 3) :
    sl2Upper c ∈ Subgroup.closure ({xpS, xmS} : Set SL(2, ZMod 3)) := by
  have hp : xpS ∈ Subgroup.closure ({xpS, xmS} : Set SL(2, ZMod 3)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases h c with rfl | rfl | rfl
  · have h0 : sl2Upper (0 : ZMod 3) = 1 := Subtype.ext (by decide +kernel)
    rw [h0]
    exact Subgroup.one_mem _
  · exact hp
  · have h2 : sl2Upper (2 : ZMod 3) = xpS * xpS := Subtype.ext (by decide +kernel)
    rw [h2]
    exact Subgroup.mul_mem _ hp hp

private theorem sl2Lower_mem_closure (c : ZMod 3) :
    sl2Lower c ∈ Subgroup.closure ({xpS, xmS} : Set SL(2, ZMod 3)) := by
  have hm : xmS ∈ Subgroup.closure ({xpS, xmS} : Set SL(2, ZMod 3)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases h c with rfl | rfl | rfl
  · have h0 : sl2Lower (0 : ZMod 3) = 1 := Subtype.ext (by decide +kernel)
    rw [h0]
    exact Subgroup.one_mem _
  · exact hm
  · have h2 : sl2Lower (2 : ZMod 3) = xmS * xmS := Subtype.ext (by decide +kernel)
    rw [h2]
    exact Subgroup.mul_mem _ hm hm

theorem closure_xp_xm : Subgroup.closure ({xpS, xmS} : Set SL(2, ZMod 3)) = ⊤ := by
  rw [eq_top_iff]
  intro A _
  refine (Subgroup.closure_le _).2 ?_ (mem_closure_sl2 A)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact sl2Upper_mem_closure c
  · exact sl2Lower_mem_closure c

@[expose] noncomputable def elemSL (i j : Fin 3) (_ : i ≠ j) : SL(3, ZMod 3) :=
  ⟨1 + Matrix.single i j 1, by revert i j; decide +kernel⟩

@[expose] noncomputable def a2Mat : Fin 6 → SL(3, ZMod 3) :=
  ![blockSL (ZMod 3) 3 2 0 (by omega) xpS, blockSL (ZMod 3) 3 2 0 (by omega) xmS,
    elemSL 0 2 (by decide), elemSL 2 0 (by decide),
    blockSL (ZMod 3) 3 2 1 (by omega) xpS, blockSL (ZMod 3) 3 2 1 (by omega) xmS]

@[expose] def c2Root : Fin 8 → RootSubgroupIndex 2 :=
  ![.positiveLong 0, .negativeLong 0, .positiveLong 1, .negativeLong 1,
    .positiveSum 0 1 (by decide), .difference 0 1 (by decide), .difference 1 0 (by decide),
    .negativeSum 0 1 (by decide)]

@[expose] def v6Root : Fin 12 → RootSubgroupIndex 3 :=
  ![.positiveLong 1, .negativeLong 1, .positiveLong 2, .negativeLong 2,
    .difference 0 1 (by decide), .difference 1 0 (by decide), .difference 0 2 (by decide),
    .difference 2 0 (by decide), .positiveSum 1 2 (by decide), .difference 1 2 (by decide),
    .difference 2 1 (by decide), .negativeSum 1 2 (by decide)]

@[expose] noncomputable def c2Mat : Fin 8 → StatedSp 2 (ZMod 3) := fun j => elt (c2Root j) 1

@[expose] noncomputable def v6Mat : Fin 12 → StatedSp 3 (ZMod 3) := fun i => elt (v6Root i) 1

private noncomputable def slMat3 : SL(3, ZMod 3) →* Matrix (Fin 3) (Fin 3) (ZMod 3) where
  toFun A := A
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem slMat3_injective : Function.Injective slMat3 := fun _ _ h => Subtype.ext h

private noncomputable def c2N (j : Fin 8) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  1 + (1 : ZMod 3) • E (ZMod 3) (c2Root j)

private noncomputable def v6N (i : Fin 12) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3) :=
  1 + (1 : ZMod 3) • E (ZMod 3) (v6Root i)

theorem a2_relsHold : RelsHold a2Mat a2Words := by
  refine relsHold_of_evalCube slMat3 slMat3_injective a2Mat (fun i => (a2Mat i : Matrix _ _ _))
    (fun _ => rfl) ?_ ?_
  · decide +kernel
  · decide +kernel

theorem c2_relsHold : RelsHold c2Mat c2Words := by
  refine relsHold_of_evalCube (mat 2 (ZMod 3)) mat_injective c2Mat c2N
    (fun j => mat_elt (c2Root j) 1) ?_ ?_
  · decide +kernel
  · decide +kernel

theorem v6_relsHold : RelsHold v6Mat v6Words := by
  refine relsHold_of_evalCube (mat 3 (ZMod 3)) mat_injective v6Mat v6N
    (fun i => mat_elt (v6Root i) 1) ?_ ?_
  · decide +kernel
  · decide +kernel

theorem a2Mat_zero : a2Mat 0 = blockSL (ZMod 3) 3 2 0 (by omega) xpS := rfl

theorem a2Mat_one : a2Mat 1 = blockSL (ZMod 3) 3 2 0 (by omega) xmS := rfl

theorem a2Mat_four : a2Mat 4 = blockSL (ZMod 3) 3 2 1 (by omega) xpS := rfl

theorem a2Mat_five : a2Mat 5 = blockSL (ZMod 3) 3 2 1 (by omega) xmS := rfl

theorem c2Mat_zero : c2Mat 0 = longBlock (ZMod 3) 2 0 xpS := (longBlock_sl2Upper 0 1).symm

theorem c2Mat_one : c2Mat 1 = longBlock (ZMod 3) 2 0 xmS := (longBlock_sl2Lower 0 1).symm

theorem c2Mat_two : c2Mat 2 = longBlock (ZMod 3) 2 1 xpS := (longBlock_sl2Upper 1 1).symm

theorem c2Mat_three : c2Mat 3 = longBlock (ZMod 3) 2 1 xmS := (longBlock_sl2Lower 1 1).symm

theorem c2Mat_five : c2Mat 5 = shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) xpS :=
  (shortBlock_sl2Upper _ 1).symm

theorem c2Mat_six : c2Mat 6 = shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) xmS :=
  (shortBlock_sl2Lower _ 1).symm

theorem v6Mat_zero : v6Mat 0 = longBlock (ZMod 3) 3 1 xpS := (longBlock_sl2Upper 1 1).symm

theorem v6Mat_one : v6Mat 1 = longBlock (ZMod 3) 3 1 xmS := (longBlock_sl2Lower 1 1).symm

theorem v6Mat_two : v6Mat 2 = longBlock (ZMod 3) 3 2 xpS := (longBlock_sl2Upper 2 1).symm

theorem v6Mat_three : v6Mat 3 = longBlock (ZMod 3) 3 2 xmS := (longBlock_sl2Lower 2 1).symm

theorem v6Mat_four : v6Mat 4 = shortBlock (ZMod 3) (show (0 : Fin 3) ≠ 1 by decide) xpS :=
  (shortBlock_sl2Upper _ 1).symm

theorem v6Mat_five : v6Mat 5 = shortBlock (ZMod 3) (show (0 : Fin 3) ≠ 1 by decide) xmS :=
  (shortBlock_sl2Lower _ 1).symm

theorem v6Mat_six : v6Mat 6 = shortBlock (ZMod 3) (show (0 : Fin 3) ≠ 2 by decide) xpS :=
  (shortBlock_sl2Upper _ 1).symm

theorem v6Mat_seven : v6Mat 7 = shortBlock (ZMod 3) (show (0 : Fin 3) ≠ 2 by decide) xmS :=
  (shortBlock_sl2Lower _ 1).symm

theorem v6Mat_nine : v6Mat 9 = shortBlock (ZMod 3) (show (1 : Fin 3) ≠ 2 by decide) xpS :=
  (shortBlock_sl2Upper _ 1).symm

theorem v6Mat_ten : v6Mat 10 = shortBlock (ZMod 3) (show (1 : Fin 3) ≠ 2 by decide) xmS :=
  (shortBlock_sl2Lower _ 1).symm

end CFSG.ClassicalInvolution.Q3.Q3Z
