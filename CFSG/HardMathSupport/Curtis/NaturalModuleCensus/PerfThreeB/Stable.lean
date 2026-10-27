module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB.Key

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {r : ℕ}

theorem vec_add_self (x : Fin r ⊕ Fin r → ZMod 2) : x + x = 0 :=
  funext fun _ => CharTwo.add_self_eq_zero _

theorem pairedSympForm_symm_zmod_two (x y : Fin r ⊕ Fin r → ZMod 2) :
    pairedSympForm (ZMod 2) r x y = pairedSympForm (ZMod 2) r y x := by
  have h := pairedSympForm_self (k := ZMod 2) (m := r) (x + y)
  simp only [map_add, LinearMap.add_apply, pairedSympForm_self] at h
  rcases zmod_two_cases (pairedSympForm (ZMod 2) r x y) with h1 | h1 <;>
    rcases zmod_two_cases (pairedSympForm (ZMod 2) r y x) with h2 | h2 <;>
    rw [h1, h2] at h ⊢ <;> first | rfl | exact absurd h (by decide)

@[expose] def tMat (a : Fin r ⊕ Fin r → ZMod 2) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2) :=
  1 + vecMulVec a
    ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ a)

theorem tMat_mulVec (a y : Fin r ⊕ Fin r → ZMod 2) :
    tMat a *ᵥ y = y + pairedSympForm (ZMod 2) r y a • a := by
  rw [tMat, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  congr 2
  rw [pairedSympForm, Matrix.toBilin'_apply', dotProduct_comm]
  rfl

theorem tMat_mul_self (a : Fin r ⊕ Fin r → ZMod 2) : tMat a * tMat a = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, tMat_mulVec, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, pairedSympForm_self, smul_eq_mul, mul_zero,
    add_zero]
  rw [one_mulVec, add_assoc]
  convert add_zero y using 2
  exact vec_add_self _

theorem tMat_mem (a : Fin r ⊕ Fin r → ZMod 2) :
    (⟨tMat a, tMat a, tMat_mul_self a, tMat_mul_self a⟩ : GL (Fin r ⊕ Fin r) (ZMod 2)) ∈
      StatedSp r (ZMod 2) := by
  apply Subgroup.subset_closure
  show (tMat a)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * tMat a = Matrix.fromBlocks 0 1 (-1) 0
  apply Matrix.toBilin'.injective
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have hcomp : Matrix.toBilin' ((tMat a)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * tMat a) x y =
      pairedSympForm (ZMod 2) r (tMat a *ᵥ x) (tMat a *ᵥ y) := by
    rw [← Matrix.toBilin'_comp]
    rfl
  refine hcomp.trans ?_
  change _ = pairedSympForm (ZMod 2) r x y
  rw [tMat_mulVec, tMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, pairedSympForm_self,
    smul_eq_mul]
  rw [pairedSympForm_symm_zmod_two a y]
  generalize pairedSympForm (ZMod 2) r x y = p
  generalize pairedSympForm (ZMod 2) r x a = q
  generalize pairedSympForm (ZMod 2) r y a = t
  revert p q t
  decide

@[expose] def tr (a : Fin r ⊕ Fin r → ZMod 2) : StatedSp r (ZMod 2) :=
  ⟨⟨tMat a, tMat a, tMat_mul_self a, tMat_mul_self a⟩, tMat_mem a⟩

theorem spMat_ext {g h : StatedSp r (ZMod 2)} (H : ∀ y, spMat g *ᵥ y = spMat h *ᵥ y) : g = h :=
  spMat_injective (Matrix.toLin'.injective (LinearMap.ext fun y => by
    simpa only [Matrix.toLin'_apply] using H y))

theorem spMat_tr_mulVec (a y : Fin r ⊕ Fin r → ZMod 2) :
    spMat (tr a) *ᵥ y = y + pairedSympForm (ZMod 2) r y a • a := tMat_mulVec a y

theorem tr_comm {a a' : Fin r ⊕ Fin r → ZMod 2} (h : pairedSympForm (ZMod 2) r a a' = 0) :
    tr a * tr a' = tr a' * tr a := by
  have h' : pairedSympForm (ZMod 2) r a' a = 0 := by rw [pairedSympForm_symm_zmod_two, h]
  refine spMat_ext fun y => ?_
  simp only [spMat_mul, ← Matrix.mulVec_mulVec, spMat_tr_mulVec, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h, h', mul_zero, add_zero]
  abel

theorem mul_tr (v : StatedSp r (ZMod 2)) (a : Fin r ⊕ Fin r → ZMod 2) :
    v * tr a = tr (spMat v *ᵥ a) * v := by
  refine spMat_ext fun y => ?_
  simp only [spMat_mul, ← Matrix.mulVec_mulVec, spMat_tr_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, pairedSympForm_spMat_mulVec]

theorem isoData_spMat {v : StatedSp r (ZMod 2)} (hv : v ^ 3 = 1) :
    IsoData (fun x y => pairedSympForm (ZMod 2) r x y) (fun x => spMat v *ᵥ x) where
  two := vec_add_self
  Badd_l x y z := LinearMap.map_add₂ _ x y z
  Badd_r x y z := map_add (pairedSympForm (ZMod 2) r x) y z
  fadd x y := Matrix.mulVec_add _ _ _
  alt := pairedSympForm_self
  symm := pairedSympForm_symm_zmod_two
  nondeg x hx := by
    by_contra hcon
    push Not at hcon
    apply hx
    refine pairedSympForm_nondegenerate.1 x fun y => ?_
    rcases zmod_two_cases (pairedSympForm (ZMod 2) r x y) with h0 | h1
    · exact h0
    · exact absurd h1 (hcon y)
  pow3 x := by
    have h3 : spMat v * (spMat v * spMat v) = 1 := by
      rw [← spMat_mul, ← spMat_mul, ← pow_three, hv, spMat_one]
    simp only [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  isom x y := pairedSympForm_spMat_mulVec v x y

theorem false_of_stable_isotropic {v : StatedSp r (ZMod 2)} (hv : v ^ 3 = 1)
    (F : AddSubgroup (Fin r ⊕ Fin r → ZMod 2))
    (hiso : ∀ x ∈ F, ∀ y ∈ F, pairedSympForm (ZMod 2) r x y = 0) {a0 : Fin r ⊕ Fin r → ZMod 2}
    (ha0F : a0 ∈ F) (ha0 : a0 ≠ 0)
    (hstab : ∀ g : StatedSp r (ZMod 2), g * v = v * g → ∀ x ∈ F, spMat g *ᵥ x ∈ F) : False := by
  have hd := isoData_spMat hv
  have hf : ∀ x ∈ F, spMat v *ᵥ x ∈ F := fun x hx => hstab v rfl x hx
  rcases hd.key F hiso hf ha0F ha0 with
    ⟨a, haF, c, hc, hac⟩ | ⟨a, haF, b, hbq, hb0, hb1, hb2, hw⟩
  · have hcomm : tr c * v = v * tr c := by rw [mul_tr, hc]
    have hmem := hstab (tr c) hcomm a haF
    rw [spMat_tr_mulVec, hac, one_smul] at hmem
    have hcF : c ∈ F := by
      have e : a + c - a = c := by abel
      exact e ▸ F.sub_mem hmem haF
    have := hiso a haF c hcF
    rw [hac] at this
    exact one_ne_zero this
  · set b1 := spMat v *ᵥ b with hb1def
    set b2 := spMat v *ᵥ b1 with hb2def
    have hb3 : spMat v *ᵥ b2 = b := hd.pow3 b
    have hB : ∀ x y, pairedSympForm (ZMod 2) r x y = pairedSympForm (ZMod 2) r y x :=
      pairedSympForm_symm_zmod_two
    have o01 : pairedSympForm (ZMod 2) r b b1 = 0 := hbq
    have o12 : pairedSympForm (ZMod 2) r b1 b2 = 0 := by
      rw [hb2def, pairedSympForm_spMat_mulVec]; exact o01
    have o02 : pairedSympForm (ZMod 2) r b b2 = 0 := by
      have := pairedSympForm_spMat_mulVec v b b2
      rw [hb3, ← hb1def] at this
      rw [← this, hB]
      exact o01
    have hc12 : tr b1 * tr b2 = tr b2 * tr b1 := tr_comm o12
    have hc02 : tr b * tr b2 = tr b2 * tr b := tr_comm o02
    have hcomm : (tr b * tr b1 * tr b2) * v = v * (tr b * tr b1 * tr b2) := by
      have t2 : tr b2 * v = v * tr b1 := (mul_tr v b1).symm
      have t1 : tr b1 * v = v * tr b := (mul_tr v b).symm
      have t0 : tr b * v = v * tr b2 := by
        have := mul_tr v b2
        rw [hb3] at this
        exact this.symm
      have hcc : tr b2 * (tr b * tr b1) = tr b * tr b1 * tr b2 :=
        calc tr b2 * (tr b * tr b1) = (tr b2 * tr b) * tr b1 := (mul_assoc _ _ _).symm
          _ = (tr b * tr b2) * tr b1 := by rw [hc02]
          _ = tr b * (tr b2 * tr b1) := mul_assoc _ _ _
          _ = tr b * (tr b1 * tr b2) := by rw [hc12]
          _ = tr b * tr b1 * tr b2 := (mul_assoc _ _ _).symm
      calc tr b * tr b1 * tr b2 * v = tr b * tr b1 * (tr b2 * v) := by simp only [mul_assoc]
        _ = tr b * (tr b1 * (v * tr b1)) := by rw [t2, mul_assoc]
        _ = tr b * ((tr b1 * v) * tr b1) := by simp only [mul_assoc]
        _ = tr b * ((v * tr b) * tr b1) := by rw [t1]
        _ = (tr b * v) * (tr b * tr b1) := by simp only [mul_assoc]
        _ = (v * tr b2) * (tr b * tr b1) := by rw [t0]
        _ = v * (tr b2 * (tr b * tr b1)) := by simp only [mul_assoc]
        _ = v * (tr b * tr b1 * tr b2) := by rw [hcc]
    have hmem := hstab _ hcomm a haF
    have p2 : pairedSympForm (ZMod 2) r a b2 • b2 = b2 := by rw [hb2, one_smul]
    have p1 : pairedSympForm (ZMod 2) r (a + b2) b1 • b1 = b1 := by
      rw [LinearMap.map_add₂, hb1, hB b2 b1, o12]
      simp
    have p0 : pairedSympForm (ZMod 2) r (a + b2 + b1) b • b = 0 := by
      rw [LinearMap.map_add₂, LinearMap.map_add₂, hb0, hB b2 b, o02, hB b1 b, o01]
      simp
    have hga : spMat (tr b * tr b1 * tr b2) *ᵥ a = a + b2 + b1 := by
      simp only [spMat_mul, ← Matrix.mulVec_mulVec, spMat_tr_mulVec]
      rw [p2, p1, p0, add_zero]
    rw [hga] at hmem
    have hw1 : b1 + b2 ∈ F := by
      have e : a + b2 + b1 - a = b1 + b2 := by abel
      exact e ▸ F.sub_mem hmem haF
    have := hiso _ hw1 _ (hf a haF)
    exact one_ne_zero (hw.symm.trans this)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB
