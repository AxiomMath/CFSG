module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

abbrev FzUT : Type := UT3 F4c

@[expose] def fzW : F4c := ⟨0, 1⟩

@[expose] def fzE1 : FzUT := ⟨1, 0, 0⟩

@[expose] def fzEW : FzUT := ⟨fzW, 0, 0⟩

@[expose] def fzF1 : FzUT := ⟨0, 1, 0⟩

@[expose] def fzFW : FzUT := ⟨0, fzW, 0⟩

@[ext] structure FzAutD where
  g1 : FzUT
  g2 : FzUT
  g3 : FzUT
  g4 : FzUT

instance : DecidableEq FzAutD := fun d d' =>
  decidable_of_iff (d.g1 = d'.g1 ∧ d.g2 = d'.g2 ∧ d.g3 = d'.g3 ∧ d.g4 = d'.g4)
    (by cases d; cases d'; simp)

@[expose] def fzPw {H : Type*} [Group H] (b : ZMod 2) (g : H) : H := if b = 0 then 1 else g

@[expose] def fzEv (d : FzAutD) (x : FzUT) : FzUT :=
  fzPw x.a.a d.g1 * fzPw x.a.b d.g2 * fzPw x.b.a d.g3 * fzPw x.b.b d.g4 *
    fzPw (x.c + x.a * x.b).a ⁅d.g1, d.g3⁆ * fzPw (x.c + x.a * x.b).b ⁅d.g1, d.g4⁆

@[expose] def fzIdD : FzAutD := ⟨fzE1, fzEW, fzF1, fzFW⟩

theorem fzUT_word (x : FzUT) :
    x = fzPw x.a.a fzE1 * fzPw x.a.b fzEW * fzPw x.b.a fzF1 * fzPw x.b.b fzFW *
      fzPw (x.c + x.a * x.b).a ⁅fzE1, fzF1⁆ * fzPw (x.c + x.a * x.b).b ⁅fzE1, fzFW⁆ := by
  revert x
  decide +kernel

theorem fzEv_id (x : FzUT) : fzEv fzIdD x = x := (fzUT_word x).symm

theorem fzPw_map {H H' : Type*} [Group H] [Group H'] (σ : H →* H') (b : ZMod 2) (g : H) :
    σ (fzPw b g) = fzPw b (σ g) := by
  unfold fzPw
  split_ifs
  · exact map_one σ
  · rfl

theorem fzUT_hom_apply (σ : FzUT →* FzUT) (x : FzUT) :
    σ x = fzEv ⟨σ fzE1, σ fzEW, σ fzF1, σ fzFW⟩ x := by
  conv_lhs => rw [fzUT_word x]
  simp only [map_mul, fzPw_map, map_commutatorElement, fzEv]

@[expose] def fzGens (σ : MulAut FzUT) : FzAutD := ⟨σ fzE1, σ fzEW, σ fzF1, σ fzFW⟩

theorem fzEv_gens (σ : MulAut FzUT) (x : FzUT) : fzEv (fzGens σ) x = σ x :=
  (fzUT_hom_apply σ.toMonoidHom x).symm

@[expose] def FzCheap (d : FzAutD) : Prop :=
  d.g1 ≠ 1 ∧ d.g2 ≠ 1 ∧ d.g3 ≠ 1 ∧ d.g4 ≠ 1 ∧
  d.g1 * d.g1 = 1 ∧ d.g2 * d.g2 = 1 ∧ d.g3 * d.g3 = 1 ∧ d.g4 * d.g4 = 1 ∧
  d.g1 * d.g2 = d.g2 * d.g1 ∧ d.g3 * d.g4 = d.g4 * d.g3 ∧
  ⁅d.g2, d.g3⁆ = ⁅d.g1, d.g4⁆ ∧ ⁅d.g2, d.g4⁆ = ⁅d.g1, d.g3⁆ * ⁅d.g1, d.g4⁆ ∧
  ⁅d.g1, d.g3⁆ ≠ 1

@[expose] def FzHom (d : FzAutD) : Prop := ∀ x y : FzUT, fzEv d (x * y) = fzEv d x * fzEv d y

@[expose] def FzInj (d : FzAutD) : Prop := ∀ x : FzUT, fzEv d x = 1 → x = 1

@[expose] def FzIsAut (d : FzAutD) : Prop := FzCheap d ∧ FzHom d ∧ FzInj d

instance : DecidablePred FzIsAut := fun d => by
  unfold FzIsAut FzCheap FzHom FzInj
  infer_instance

theorem fzIsAut_gens (σ : MulAut FzUT) : FzIsAut (fzGens σ) := by
  have hinj : Function.Injective σ := σ.injective
  have key : ∀ a b : FzUT, σ a * σ b = σ (a * b) := fun a b => (map_mul σ a b).symm
  have h1 : ∀ a : FzUT, a ≠ 1 → σ a ≠ 1 := fun a ha h => ha (hinj (by simpa using h))
  have hc : ∀ a b : FzUT, ⁅σ a, σ b⁆ = σ ⁅a, b⁆ := fun a b => (map_commutatorElement σ a b).symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact h1 _ (by decide +kernel)
  · exact h1 _ (by decide +kernel)
  · exact h1 _ (by decide +kernel)
  · exact h1 _ (by decide +kernel)
  · show σ fzE1 * σ fzE1 = 1
    rw [key, show fzE1 * fzE1 = 1 by decide +kernel, map_one]
  · show σ fzEW * σ fzEW = 1
    rw [key, show fzEW * fzEW = 1 by decide +kernel, map_one]
  · show σ fzF1 * σ fzF1 = 1
    rw [key, show fzF1 * fzF1 = 1 by decide +kernel, map_one]
  · show σ fzFW * σ fzFW = 1
    rw [key, show fzFW * fzFW = 1 by decide +kernel, map_one]
  · show σ fzE1 * σ fzEW = σ fzEW * σ fzE1
    rw [key, key, show fzE1 * fzEW = fzEW * fzE1 by decide +kernel]
  · show σ fzF1 * σ fzFW = σ fzFW * σ fzF1
    rw [key, key, show fzF1 * fzFW = fzFW * fzF1 by decide +kernel]
  · show ⁅σ fzEW, σ fzF1⁆ = ⁅σ fzE1, σ fzFW⁆
    rw [hc, hc, show ⁅fzEW, fzF1⁆ = ⁅fzE1, fzFW⁆ by decide +kernel]
  · show ⁅σ fzEW, σ fzFW⁆ = ⁅σ fzE1, σ fzF1⁆ * ⁅σ fzE1, σ fzFW⁆
    rw [hc, hc, hc, key,
      show ⁅fzEW, fzFW⁆ = ⁅fzE1, fzF1⁆ * ⁅fzE1, fzFW⁆ by decide +kernel]
  · show ⁅σ fzE1, σ fzF1⁆ ≠ 1
    rw [hc]
    exact h1 _ (by decide +kernel)
  · intro x y
    rw [fzEv_gens, fzEv_gens, fzEv_gens, map_mul]
  · intro x hx
    rw [fzEv_gens] at hx
    exact hinj (by simpa using hx)

@[expose] noncomputable def fzAutOf (d : FzAutD) (h : FzIsAut d) : MulAut FzUT :=
  MulEquiv.ofBijective (⟨fzEv d, h.2.1⟩ : FzUT →ₙ* FzUT) (by
    have h1 : fzEv d 1 = 1 := by
      have := h.2.1 1 1
      rw [mul_one] at this
      exact mul_left_cancel (a := fzEv d 1) (by rw [mul_one]; exact this.symm)
    have hinv : ∀ y, fzEv d y⁻¹ = (fzEv d y)⁻¹ := by
      intro y
      have := h.2.1 y y⁻¹
      rw [mul_inv_cancel, h1] at this
      exact eq_inv_of_mul_eq_one_right this.symm
    have hinj : Function.Injective (fzEv d) := by
      intro x y hxy
      have hm : fzEv d (x * y⁻¹) = 1 := by
        rw [h.2.1, hinv, hxy, mul_inv_cancel]
      exact mul_inv_eq_one.mp (h.2.2 _ hm)
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

theorem fzAutOf_apply (d : FzAutD) (h : FzIsAut d) (x : FzUT) : fzAutOf d h x = fzEv d x := rfl

private theorem fzPw_zero' {H : Type*} [Group H] (g : H) : fzPw 0 g = 1 := if_pos rfl

private theorem fzPw_one' {H : Type*} [Group H] (g : H) : fzPw 1 g = g := if_neg (by decide)

theorem fzEv_gen (d : FzAutD) : fzEv d fzE1 = d.g1 ∧ fzEv d fzEW = d.g2 ∧
    fzEv d fzF1 = d.g3 ∧ fzEv d fzFW = d.g4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show fzPw 1 d.g1 * fzPw 0 d.g2 * fzPw 0 d.g3 * fzPw 0 d.g4 * fzPw 0 ⁅d.g1, d.g3⁆ *
      fzPw 0 ⁅d.g1, d.g4⁆ = d.g1
    simp [fzPw_zero', fzPw_one']
  · show fzPw 0 d.g1 * fzPw 1 d.g2 * fzPw 0 d.g3 * fzPw 0 d.g4 * fzPw 0 ⁅d.g1, d.g3⁆ *
      fzPw 0 ⁅d.g1, d.g4⁆ = d.g2
    simp [fzPw_zero', fzPw_one']
  · show fzPw 0 d.g1 * fzPw 0 d.g2 * fzPw 1 d.g3 * fzPw 0 d.g4 * fzPw 0 ⁅d.g1, d.g3⁆ *
      fzPw 0 ⁅d.g1, d.g4⁆ = d.g3
    simp [fzPw_zero', fzPw_one']
  · show fzPw 0 d.g1 * fzPw 0 d.g2 * fzPw 0 d.g3 * fzPw 1 d.g4 * fzPw 0 ⁅d.g1, d.g3⁆ *
      fzPw 0 ⁅d.g1, d.g4⁆ = d.g4
    simp [fzPw_zero', fzPw_one']

theorem fzGens_fzAutOf (d : FzAutD) (h : FzIsAut d) : fzGens (fzAutOf d h) = d := by
  obtain ⟨h1, h2, h3, h4⟩ := fzEv_gen d
  exact FzAutD.ext (by simpa [fzGens, fzAutOf_apply] using h1)
    (by simpa [fzGens, fzAutOf_apply] using h2) (by simpa [fzGens, fzAutOf_apply] using h3)
    (by simpa [fzGens, fzAutOf_apply] using h4)

end CFSG.OddStandard.SmallF3.FritzII
