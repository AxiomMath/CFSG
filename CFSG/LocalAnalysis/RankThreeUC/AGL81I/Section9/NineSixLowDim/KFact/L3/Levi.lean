module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {F : Type} [Field F]

private theorem matrix_transvection_pow {i j : Fin 3} (hij : i ≠ j) (c : F) (n : ℕ) :
    Matrix.transvection i j c ^ n = Matrix.transvection i j ((n : F) * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, transvection_mul_transvection_same _ _ hij]
    push_cast; ring_nf

private theorem diagThree_mul (d e : Fin 3 → Fˣ) : diagThree d * diagThree e = diagThree (d * e) :=
  Units.ext (by simp [diagThree, diagonal_mul_diagonal])

private theorem diagThree_comm_transvection (d : Fin 3 → Fˣ) {i j : Fin 3} (hij : i ≠ j) (c : F)
    (hd : d i = d j) :
    diagThree d * GeneralLinearGroup.transvection i j hij c =
      GeneralLinearGroup.transvection i j hij c * diagThree d := by
  refine Units.ext ?_
  change diagonal _ * (1 + single i j c) = (1 + single i j c) * diagonal _
  ext a b
  simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h; simp [hd, mul_comm]
  · by_cases hab : a = b
    · subst hab; simp [h]
    · simp [h, one_apply, hab]

private theorem diagThree_eq_of_mem_center {d : Fin 3 → Fˣ}
    (h : diagThree d ∈ Subgroup.center (GL (Fin 3) F)) {i j : Fin 3} (hij : i ≠ j) : d i = d j := by
  have hc := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) i j)
    (Subgroup.mem_center_iff.mp h (GeneralLinearGroup.transvection i j hij 1))
  simp [diagThree, Matrix.transvection, diagonal_mul, mul_diagonal, hij] at hc
  exact Units.ext hc.symm

private theorem transvection_mem_fixSetThree {q : ℕ} [hq : Fact q.Prime] {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ q) {A : Subgroup (GL (Fin 3) (ZMod q))} {d : Fin 3 → (ZMod q)ˣ}
    (hdA : diagThree d ∈ A) (hnc : diagThree d ∉ Subgroup.center (GL (Fin 3) (ZMod q)))
    {i j : Fin 3} (hij : i ≠ j) (hd : d i = d j) (c : ZMod q) :
    GeneralLinearGroup.transvection i j hij c ∈ fixSetThree p A := by
  refine ⟨det_transvection_of_ne i j hij c, fun hdvd => hpq ?_,
    diagThree d, hdA, hnc, diagThree_comm_transvection d hij c hd⟩
  have hpow : GeneralLinearGroup.transvection i j hij c ^ q = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    change Matrix.transvection i j c ^ q = _
    rw [matrix_transvection_pow hij, ZMod.natCast_self, zero_mul, transvection_zero, Units.val_one]
  exact (Nat.prime_dvd_prime_iff_eq hp hq.out).mp (hdvd.trans (orderOf_dvd_of_pow_eq_one hpow))

theorem closure_fixSetThree_of_diag {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {A : Subgroup (GL (Fin 3) (ZMod q))} {ζ : (ZMod q)ˣ} (hζ : ζ ≠ 1)
    (h₁ : diagThree ![ζ, 1, 1] ∈ A) (h₂ : diagThree ![1, ζ, 1] ∈ A) :
    Subgroup.closure (fixSetThree p A) = CFSG.Open.StatedSL 3 (ZMod q) := by
  have hζ' : ¬ (ζ = 1) := hζ
  have h₃ : diagThree ![ζ, ζ, 1] ∈ A := by
    have h := A.mul_mem h₁ h₂
    rwa [diagThree_mul, show (![ζ, 1, 1] * ![1, ζ, 1] : Fin 3 → (ZMod q)ˣ) = ![ζ, ζ, 1] by
      ext k; fin_cases k <;> simp] at h
  have n₁ : diagThree ![ζ, 1, 1] ∉ Subgroup.center (GL (Fin 3) (ZMod q)) := fun h =>
    hζ' (by simpa using diagThree_eq_of_mem_center h (i := 0) (j := 1) (by decide))
  have n₂ : diagThree ![1, ζ, 1] ∉ Subgroup.center (GL (Fin 3) (ZMod q)) := fun h =>
    hζ' (by simpa [eq_comm] using diagThree_eq_of_mem_center h (i := 0) (j := 1) (by decide))
  have n₃ : diagThree ![ζ, ζ, 1] ∉ Subgroup.center (GL (Fin 3) (ZMod q)) := fun h =>
    hζ' (by simpa using diagThree_eq_of_mem_center h (i := 0) (j := 2) (by decide))
  have key : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod q),
      GeneralLinearGroup.transvection i j hij c ∈ fixSetThree p A := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact transvection_mem_fixSetThree hp hpq h₁ n₁ hij rfl c
      | exact transvection_mem_fixSetThree hp hpq h₂ n₂ hij rfl c
      | exact transvection_mem_fixSetThree hp hpq h₃ n₃ hij rfl c
  refine le_antisymm (Subgroup.closure_mono fun x hx => hx.1) ?_
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have htop := CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
    ((Subgroup.closure (fixSetThree p A)).comap SpecialLinearGroup.toGL)
    fun i j hij c => Subgroup.subset_closure (by
      convert key i j hij c using 1; exact Units.ext rfl)
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod q)).det = 1 := hg
  have hmem : SpecialLinearGroup.toGL (⟨g, hdet⟩ : SpecialLinearGroup (Fin 3) (ZMod q)) ∈
      Subgroup.closure (fixSetThree p A) :=
    Subgroup.mem_comap.mp (htop ▸ Subgroup.mem_top _)
  have hg' : SpecialLinearGroup.toGL (⟨g, hdet⟩ : SpecialLinearGroup (Fin 3) (ZMod q)) = g :=
    Units.ext rfl
  show g ∈ Subgroup.closure (fixSetThree p A)
  rwa [hg'] at hmem

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
