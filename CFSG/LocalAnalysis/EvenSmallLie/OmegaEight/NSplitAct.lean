module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Perm
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev V7 := Fin 7 → ZMod 2

@[expose] def vOf (x : V7) : V6 := fun j => x j.castSucc

@[expose] def mk7 (v : V6) (c : ZMod 2) : V7 := fun j => if h : (j : ℕ) < 6 then v ⟨j, h⟩ else c

theorem vOf_mk7 (v : V6) (c : ZMod 2) : vOf (mk7 v c) = v := by
  ext j
  simp [vOf, mk7, j.2]

theorem mk7_last (v : V6) (c : ZMod 2) : mk7 v c 6 = c := by
  simp [mk7]

theorem mk7_vOf (x : V7) : mk7 (vOf x) (x 6) = x := by
  ext j
  by_cases h : (j : ℕ) < 6
  · simp [mk7, vOf, h]
  · have : j = 6 := by ext; simp; omega
    subst this
    simp [mk7]

theorem mk7_add (v w : V6) (c d : ZMod 2) : mk7 v c + mk7 w d = mk7 (v + w) (c + d) := by
  ext j
  by_cases h : (j : ℕ) < 6 <;> simp [mk7, h]

theorem vOf_add (x y : V7) : vOf (x + y) = vOf x + vOf y := rfl

theorem mk7_zero : mk7 0 0 = 0 := by
  ext j
  by_cases h : (j : ℕ) < 6 <;> simp [mk7, h]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

@[expose] def actV7 (σ : Equiv.Perm V6) (x : V7) : V7 := mk7 (σ (vOf x) + (x 6 + 1) • σ 0) (x 6)

theorem actV7_mk7 (σ : Equiv.Perm V6) (v : V6) (c : ZMod 2) :
    actV7 σ (mk7 v c) = mk7 (σ v + (c + 1) • σ 0) c := by
  rw [actV7, vOf_mk7, mk7_last]

theorem aff_add {ε : Eps} {σ : Equiv.Perm V6} (hσ : σ ∈ affGroup ε) (a b : V6) :
    σ (a + b) = σ a + σ b + σ 0 := by
  have := hσ.2 a b 0
  rwa [add_zero] at this

theorem actV7_add {ε : Eps} {σ : Equiv.Perm V6} (hσ : σ ∈ affGroup ε) (x y : V7) :
    actV7 σ (x + y) = actV7 σ x + actV7 σ y := by
  rw [← mk7_vOf x, ← mk7_vOf y, mk7_add, actV7_mk7, actV7_mk7, actV7_mk7, mk7_add,
    aff_add hσ]
  congr 1
  have key : (x 6 + y 6 + 1) • σ 0 + σ 0 = (x 6 + 1) • σ 0 + (y 6 + 1) • σ 0 := by
    have hc : ∀ a b : ZMod 2, a + b + 1 + 1 = a + 1 + (b + 1) := by decide
    calc (x 6 + y 6 + 1) • σ 0 + σ 0 = (x 6 + y 6 + 1 + 1) • σ 0 := by
          rw [add_smul (x 6 + y 6 + 1), one_smul]
      _ = (x 6 + 1 + (y 6 + 1)) • σ 0 := by rw [hc]
      _ = (x 6 + 1) • σ 0 + (y 6 + 1) • σ 0 := add_smul _ _ _
  calc σ (vOf x) + σ (vOf y) + σ 0 + (x 6 + y 6 + 1) • σ 0
      = σ (vOf x) + σ (vOf y) + ((x 6 + y 6 + 1) • σ 0 + σ 0) := by abel
    _ = σ (vOf x) + (x 6 + 1) • σ 0 + (σ (vOf y) + (y 6 + 1) • σ 0) := by rw [key]; abel

theorem actV7_one (x : V7) : actV7 1 x = x := by
  rw [actV7, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  have : (vOf x + (x 6 + 1) • (0 : V6)) = vOf x := by rw [smul_zero, add_zero]
  rw [this, mk7_vOf]

theorem actV7_mul {ε : Eps} {σ τ : Equiv.Perm V6} (hσ : σ ∈ affGroup ε)
    (x : V7) : actV7 (σ * τ) x = actV7 σ (actV7 τ x) := by
  rw [← mk7_vOf x, actV7_mk7, actV7_mk7, actV7_mk7]
  congr 1
  simp only [Equiv.Perm.mul_apply]
  rcases zmod2_cases (x 6) with h | h <;> simp only [h]
  · simp only [zero_add, one_smul]
    rw [aff_add hσ]
    have h0 : σ 0 + σ 0 = 0 := CharTwo.add_self_eq_zero _
    calc σ (τ (vOf x)) + σ (τ 0) = σ (τ (vOf x)) + σ (τ 0) + (σ 0 + σ 0) := by rw [h0, add_zero]
      _ = σ (τ (vOf x)) + σ (τ 0) + σ 0 + σ 0 := by abel
  · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [h2, zero_smul, add_zero]

@[expose] noncomputable def rhoE (ε : Eps) : affGroup ε →* AddMonoid.End V7 where
  toFun σ :=
    { toFun := actV7 σ
      map_zero' := by
        rw [← mk7_zero, actV7_mk7, zero_add, one_smul, CharTwo.add_self_eq_zero]
      map_add' := actV7_add σ.2 }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    exact actV7_one x
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    exact actV7_mul σ.2 x

theorem rhoE_apply (ε : Eps) (σ : affGroup ε) (x : V7) : rhoE ε σ x = actV7 σ x := rfl

section Omega


theorem gamFacts (ε : Eps) :
    ((∀ i < 7, ∀ x < 128, actECode ε i x = actEForm ε i x) ∧ (gamArr ε).size = mOf ε ∧
      (∀ v < 64, qfB ε v = false → gamIdx ε v < mOf ε ∧ (gamArr ε).getD (gamIdx ε v) 0 = v)) ∧
      ∀ g < mOf ε, (gamArr ε).getD g 0 < 64 ∧ qfB ε ((gamArr ε).getD g 0) = false ∧
        gamIdx ε ((gamArr ε).getD g 0) = g ∧ ∀ i < 7, permIdx ε i g < mOf ε ∧
          (gamArr ε).getD (permIdx ε i g) 0 = genCode ε i ((gamArr ε).getD g 0) := by
  have h : nsGamCheck ε = true := by cases ε; exact nsGamCheck_plus; exact nsGamCheck_minus
  simp only [nsGamCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨h1, h2, fun v hv hq => ?_⟩, fun g hg => ?_⟩
  · rcases h3 v hv with h | h
    · rw [hq] at h; exact absurd h (by decide)
    · exact h
  · obtain ⟨⟨⟨h5, h6⟩, h7⟩, h8⟩ := h4 g hg
    exact ⟨h5, h6, h7, fun i hi => h8 i hi⟩

@[expose] def gam (ε : Eps) (g : ℕ) : V6 := toVec 6 ((gamArr ε).getD g 0)

theorem qfV_gam (ε : Eps) {g : ℕ} (hg : g < mOf ε) : qfV ε (gam ε g) = 0 := by
  obtain ⟨h1, h2, -⟩ := (gamFacts ε).2 g hg
  rw [gam, qfV_toVec ε h1, h2]
  rfl

theorem gamIdx_lt (ε : Eps) {v : V6} (hv : qfV ε v = 0) : gamIdx ε (vecBits v) < mOf ε :=
  ((gamFacts ε).1.2.2 _ (vecBits_lt v) ((qfV_eq_zero_iff ε v).1 hv)).1

theorem gam_gamIdx (ε : Eps) {v : V6} (hv : qfV ε v = 0) : gam ε (gamIdx ε (vecBits v)) = v := by
  rw [gam, ((gamFacts ε).1.2.2 _ (vecBits_lt v) ((qfV_eq_zero_iff ε v).1 hv)).2, toVec_vecBits]

theorem gamIdx_gam (ε : Eps) {g : ℕ} (hg : g < mOf ε) : gamIdx ε (vecBits (gam ε g)) = g := by
  obtain ⟨h1, -, h3, -⟩ := (gamFacts ε).2 g hg
  rw [gam, vecBits_toVec h1, h3]

@[expose] def zEquiv (ε : Eps) : Fin (mOf ε) ≃ {v : V6 // qfV ε v = 0} where
  toFun g := ⟨gam ε g, qfV_gam ε g.2⟩
  invFun v := ⟨gamIdx ε (vecBits v.1), gamIdx_lt ε v.2⟩
  left_inv g := Fin.ext (gamIdx_gam ε g.2)
  right_inv v := Subtype.ext (gam_gamIdx ε v.2)

@[expose] def restrZ (ε : Eps) : affGroup ε →* Equiv.Perm {v : V6 // qfV ε v = 0} where
  toFun σ := (σ : Equiv.Perm V6).subtypePerm fun v => by rw [σ.2.1 v]
  map_one' := Equiv.ext fun v => rfl
  map_mul' σ τ := Equiv.ext fun v => rfl

@[expose] noncomputable def alphaZ (ε : Eps) : affGroup ε →* Equiv.Perm (Fin (mOf ε)) :=
  (zEquiv ε).symm.permCongrHom.toMonoidHom.comp (restrZ ε)

theorem gam_alphaZ (ε : Eps) (σ : affGroup ε) (g : Fin (mOf ε)) :
    gam ε (alphaZ ε σ g) = (σ : Equiv.Perm V6) (gam ε g) := by
  change ((zEquiv ε) ((zEquiv ε).symm (restrZ ε σ ((zEquiv ε) g)))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem alphaZ_val (ε : Eps) (σ : affGroup ε) (g : Fin (mOf ε)) :
    (alphaZ ε σ g : ℕ) = gamIdx ε (vecBits ((σ : Equiv.Perm V6) (gam ε g))) := by
  have h := gam_alphaZ ε σ g
  rw [← h, gamIdx_gam ε (alphaZ ε σ g).2]

theorem gam_zero (ε : Eps) : gam ε 0 = 0 := by
  cases ε <;> decide

end Omega

end CFSG.EvenSmallLie.OmegaEight.NSplit
