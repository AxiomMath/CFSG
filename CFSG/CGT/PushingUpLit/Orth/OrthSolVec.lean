module

public import CFSG.CGT.PushingUpLit.Orth.OrthFin
public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv
open CFSG.Quasithin.G6 (coreMod coreAct)
open CFSG.CGT.PushingUpLit.BHS (vcoord vcoord_ext vcoord_mul vcoord_coreAct mkEven vcoord_mkEven
  vcoord_one sum_vcoord)

@[expose] def par (v : Vec5) : ZMod 2 := ∑ i, v i

theorem par_add (v w : Vec5) : par (v + w) = par v + par w := by
  simp only [par, Pi.add_apply, Finset.sum_add_distrib]

theorem par_permAct (σ : Perm (Fin 5)) (v : Vec5) : par (permAct σ v) = par v :=
  Equiv.sum_comp σ.symm v

theorem par_ones : par ones = 1 := by decide

theorem sum_adj : ∀ v : Vec5, ∑ i, (v i + par v) = 0 := by decide +kernel

@[expose] def evenPart (v : Vec5) : ↥(coreMod 5) := mkEven (fun i => v i + par v) (sum_adj v)

theorem vcoord_evenPart (v : Vec5) (i : Fin 5) : vcoord (evenPart v) i = v i + par v := rfl

theorem evenPart_add (v w : Vec5) : evenPart (v + w) = evenPart v * evenPart w := by
  refine vcoord_ext fun i => ?_
  rw [vcoord_mul, vcoord_evenPart, vcoord_evenPart, vcoord_evenPart, par_add, Pi.add_apply]
  ring

theorem evenPart_permAct (σ : Perm (Fin 5)) (v : Vec5) :
    evenPart (permAct σ v) = coreAct 5 σ (evenPart v) := by
  refine vcoord_ext fun i => ?_
  rw [vcoord_evenPart, vcoord_coreAct, vcoord_evenPart, par_permAct]
  rfl

theorem evenPart_ones : evenPart ones = 1 := by
  refine vcoord_ext fun i => ?_
  rw [vcoord_evenPart, vcoord_one, par_ones]
  show (1 : ZMod 2) + 1 = 0
  decide

theorem par_shift : ∀ (f : Vec5) (c : ZMod 2), par f = 0 → par (fun i => f i + c) = c := by
  decide +kernel

theorem evenPart_shift (u : ↥(coreMod 5)) (c : ZMod 2) :
    par (fun i => vcoord u i + c) = c ∧ evenPart (fun i => vcoord u i + c) = u := by
  have hp : par (fun i => vcoord u i + c) = c := par_shift _ c (sum_vcoord u)
  refine ⟨hp, vcoord_ext fun i => ?_⟩
  rw [vcoord_evenPart, hp, add_assoc]
  have : ∀ c : ZMod 2, c + c = 0 := by decide
  rw [this c, add_zero]

@[expose] def rpart {G : Type*} [One G] (r0 : G) (c : ZMod 2) : G := if c = 1 then r0 else 1

theorem rpart_zero {G : Type*} [One G] (r0 : G) : rpart r0 0 = 1 := by
  have : (0 : ZMod 2) ≠ 1 := by decide
  simp [rpart, this]

theorem rpart_one {G : Type*} [One G] (r0 : G) : rpart r0 1 = r0 := by
  simp [rpart]

theorem rpart_add {G : Type*} [Group G] {r0 : G} (hr : r0 * r0 = 1) (c d : ZMod 2) :
    rpart r0 (c + d) = rpart r0 c * rpart r0 d := by
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases h c with rfl | rfl <;> rcases h d with rfl | rfl <;>
    simp [rpart_zero, rpart_one, hr, h11]

theorem rpart_inj {G : Type*} [Group G] {r0 : G} (hr : r0 ≠ 1) {c d : ZMod 2}
    (h : rpart r0 c = rpart r0 d) : c = d := by
  have h' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h' c with rfl | rfl <;> rcases h' d with rfl | rfl
  · rfl
  · rw [rpart_zero, rpart_one] at h; exact absurd h.symm hr
  · rw [rpart_zero, rpart_one] at h; exact absurd h hr
  · rfl

theorem card_supp_evenPart : ∀ v : Vec5, (wt v = 1 ∨ wt v = 4) →
    (Finset.univ.filter fun i : Fin 5 => v i + par v = 1).card = 4 := by decide +kernel

end CFSG.CGT.PushingUpLit.Orth
