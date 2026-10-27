module

public import CFSG.ClassicalInvolution.Q3.Q3ZEval
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open scoped MatrixGroups
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (mem_closure_sl2)

@[expose] def autXp : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

@[expose] def autXm : SL(2, ZMod 3) := ⟨!![1, 0; 1, 1], by decide⟩

@[expose] def gluingAssign : Fin 12 → SL(2, ZMod 3) :=
  fun i => if i = xPlus then autXp else if i = xMinus then autXm else 1

section Generation

private theorem sl2Upper_cases :
    ∀ c : ZMod 3, sl2Upper c = 1 ∨ sl2Upper c = autXp ∨ sl2Upper c = autXp * autXp := by
  decide +kernel

private theorem sl2Lower_cases :
    ∀ c : ZMod 3, sl2Lower c = 1 ∨ sl2Lower c = autXm ∨ sl2Lower c = autXm * autXm := by
  decide +kernel

theorem closure_autXp_autXm : Subgroup.closure ({autXp, autXm} : Set SL(2, ZMod 3)) = ⊤ := by
  have hp : autXp ∈ Subgroup.closure ({autXp, autXm} : Set SL(2, ZMod 3)) :=
    Subgroup.subset_closure (by simp)
  have hm : autXm ∈ Subgroup.closure ({autXp, autXm} : Set SL(2, ZMod 3)) :=
    Subgroup.subset_closure (by simp)
  refine top_unique fun A _ => ?_
  refine ((Subgroup.closure_le _).2 ?_) (mem_closure_sl2 A)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · rcases sl2Upper_cases c with h | h | h <;> rw [h]
    · exact one_mem _
    · exact hp
    · exact mul_mem hp hp
  · rcases sl2Lower_cases c with h | h | h <;> rw [h]
    · exact one_mem _
    · exact hm
    · exact mul_mem hm hm

theorem hom_ext_of_gens {G : Type*} [Group G] {f g : SL(2, ZMod 3) →* G}
    (h1 : f autXp = g autXp) (h2 : f autXm = g autXm) : f = g := by
  ext A
  have hA : A ∈ Subgroup.closure ({autXp, autXm} : Set SL(2, ZMod 3)) := by
    rw [closure_autXp_autXm]
    exact Subgroup.mem_top A
  refine MonoidHom.eqOn_closure (s := ({autXp, autXm} : Set SL(2, ZMod 3))) ?_ hA
  rintro _ (rfl | rfl)
  · exact h1
  · exact h2

theorem alpha_eq_of_gens {α β : SL(2, ZMod 3) ≃* SL(2, ZMod 3)} (h1 : α autXp = β autXp)
    (h2 : α autXm = β autXm) : α = β :=
  MulEquiv.ext fun A => DFunLike.congr_fun
    (hom_ext_of_gens (f := α.toMonoidHom) (g := β.toMonoidHom) h1 h2) A

end Generation

section Pairs

theorem autXp_pow_three : autXp ^ 3 = 1 := by decide +kernel

theorem autXm_pow_three : autXm ^ 3 = 1 := by decide +kernel

theorem aut_braid : autXp * autXm⁻¹ * autXp = autXm⁻¹ * autXp * autXm⁻¹ := by decide +kernel

theorem aut_braid_sq_ne_one : (autXp * autXm⁻¹ * autXp) ^ 2 ≠ 1 := by decide +kernel

theorem pair_cases : ∀ a b : SL(2, ZMod 3), a ^ 3 = 1 → b ^ 3 = 1 →
    a * b⁻¹ * a = b⁻¹ * a * b⁻¹ → (a * b⁻¹ * a) ^ 2 ≠ 1 →
      ∃ k : Fin 24, a = evalW gluingAssign (gluingA k) ∧ b = evalW gluingAssign (gluingB k) := by
  decide +kernel

theorem aut_pair_cases (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) :
    ∃ k : Fin 24, α autXp = evalW gluingAssign (gluingA k) ∧
      α autXm = evalW gluingAssign (gluingB k) := by
  refine pair_cases (α autXp) (α autXm) ?_ ?_ ?_ ?_
  · rw [← map_pow, autXp_pow_three, map_one]
  · rw [← map_pow, autXm_pow_three, map_one]
  · have h := congrArg α aut_braid
    simpa only [map_mul, map_inv] using h
  · intro h
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, map_eq_one_iff _ α.injective] at h
    exact aut_braid_sq_ne_one h

end Pairs

section Letters

theorem gluingA_letters : ∀ k : Fin 24, ∀ p ∈ gluingA k, p.1 = xPlus ∨ p.1 = xMinus := by
  decide +kernel

theorem gluingB_letters : ∀ k : Fin 24, ∀ p ∈ gluingB k, p.1 = xPlus ∨ p.1 = xMinus := by
  decide +kernel

private theorem assign_xPlus : gluingAssign xPlus = autXp := by
  simp [gluingAssign]

private theorem assign_xMinus : gluingAssign xMinus = autXm := by
  have h : xMinus ≠ xPlus := by decide
  simp [gluingAssign, h]

theorem evalW_eq_map_of_letters {G : Type*} [Group G] (ι : SL(2, ZMod 3) →* G) (g : Fin 12 → G)
    (hp : g xPlus = ι autXp) (hm : g xMinus = ι autXm) {w : List (Fin 12 × Bool)}
    (hw : ∀ p ∈ w, p.1 = xPlus ∨ p.1 = xMinus) : evalW g w = ι (evalW gluingAssign w) := by
  induction w with
  | nil => simp
  | cons p w ih =>
    obtain ⟨i, b⟩ := p
    have hg : g i = ι (gluingAssign i) := by
      rcases hw (i, b) List.mem_cons_self with h | h
      · rw [show i = xPlus from h, hp, assign_xPlus]
      · rw [show i = xMinus from h, hm, assign_xMinus]
    rw [evalW_cons, evalW_cons, map_mul, ih fun q hq => hw q (List.mem_cons_of_mem _ hq)]
    cases b <;> simp [hg]

theorem evalW_gluingA_map {G : Type*} [Group G] (ι : SL(2, ZMod 3) →* G) (g : Fin 12 → G)
    (hp : g xPlus = ι autXp) (hm : g xMinus = ι autXm) (k : Fin 24) :
    evalW g (gluingA k) = ι (evalW gluingAssign (gluingA k)) :=
  evalW_eq_map_of_letters ι g hp hm (gluingA_letters k)

theorem evalW_gluingB_map {G : Type*} [Group G] (ι : SL(2, ZMod 3) →* G) (g : Fin 12 → G)
    (hp : g xPlus = ι autXp) (hm : g xMinus = ι autXm) (k : Fin 24) :
    evalW g (gluingB k) = ι (evalW gluingAssign (gluingB k)) :=
  evalW_eq_map_of_letters ι g hp hm (gluingB_letters k)

end Letters

end CFSG.ClassicalInvolution.Q3.Q3Z
