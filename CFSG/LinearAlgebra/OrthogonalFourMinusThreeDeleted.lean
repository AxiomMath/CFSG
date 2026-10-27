module

public import CFSG.Mathlib.GroupTheory.Perm.TwoSetStabilizer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount

noncomputable section
public section
open TauCeti
namespace CFSG.LinearAlgebra.OrthogonalFourMinusThree

open CFSG

set_option linter.style.haveILetI false

abbrev F3 := ZMod 3
abbrev Coord := Fin 6 → F3

@[expose]
def sumLinear : Coord →ₗ[F3] F3 where
  toFun z := ∑ i, z i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[simp] lemma sumLinear_apply (z : Coord) : sumLinear z = ∑ i, z i := rfl

lemma sumLinear_surjective : Function.Surjective sumLinear := by
  intro c
  refine ⟨Pi.single 0 c, ?_⟩
  simp [sumLinear]

@[expose]
def oneVec : Coord := fun _ => 1

@[simp] lemma oneVec_apply (i : Fin 6) : oneVec i = 1 := rfl

def W : Submodule F3 Coord := LinearMap.ker sumLinear

lemma mem_W_iff (z : Coord) : z ∈ W ↔ ∑ i, z i = 0 := Iff.rfl

lemma oneVec_mem_W : oneVec ∈ W := by
  rw [mem_W_iff]
  simp only [oneVec_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  decide

def oneVecW : W := ⟨oneVec, oneVec_mem_W⟩

lemma oneVecW_ne_zero : oneVecW ≠ 0 := by
  intro h
  have h' : (oneVecW : Coord) = 0 := congrArg Subtype.val h
  have := congrFun h' 0
  simp [oneVecW, oneVec] at this

def A : Submodule F3 W := Submodule.span F3 {oneVecW}

lemma finrank_A : Module.finrank F3 A = 1 := by
  rw [A, finrank_span_singleton (by simpa using oneVecW_ne_zero)]

abbrev DeletedSpace : Type := W ⧸ A

instance : AddCommGroup DeletedSpace := inferInstanceAs (AddCommGroup (W ⧸ A))
instance : Module F3 DeletedSpace := inferInstanceAs (Module F3 (W ⧸ A))

def qUp : QuadraticForm F3 W :=
  (QuadraticMap.weightedSumSquares F3 (fun _ : Fin 6 => (1 : F3))).restrict W

lemma qUp_apply (z : W) : qUp z = ∑ i, (z : Coord) i * (z : Coord) i := by
  simp [qUp, QuadraticMap.restrict_apply, QuadraticMap.weightedSumSquares_apply]

lemma qUp_apply_oneVecW : qUp oneVecW = 0 := by
  rw [qUp_apply]
  change (∑ i : Fin 6, (1 : F3) * (1 : F3)) = 0
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  decide

lemma weightedSumSquares_polar (u v : Coord) :
    QuadraticMap.polar (QuadraticMap.weightedSumSquares F3 (fun _ : Fin 6 => (1 : F3))) u v =
      2 * ∑ i, u i * v i := by
  simp only [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, Pi.add_apply,
    smul_eq_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma polar_qUp_apply (x y : W) :
    QuadraticMap.polar qUp x y = 2 * ∑ i, (x : Coord) i * (y : Coord) i := by
  simpa [qUp, QuadraticMap.polar, QuadraticMap.restrict_apply] using
    weightedSumSquares_polar (x : Coord) (y : Coord)

lemma oneVecW_mem_radical : oneVecW ∈ qUp.radical := by
  rw [QuadraticMap.mem_radical_iff']
  refine ⟨qUp_apply_oneVecW, fun n => ?_⟩
  rw [QuadraticMap.map_add (⇑qUp), qUp_apply_oneVecW, zero_add, polar_qUp_apply]
  have hsum : (∑ i, (oneVecW : Coord) i * (n : Coord) i) = 0 := by
    simp only [oneVecW, oneVec_apply, one_mul]
    exact (mem_W_iff _).mp n.2
  rw [hsum, mul_zero]
  simp

lemma A_le_radical : A ≤ qUp.radical := by
  rw [A, Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  simpa [hx] using oneVecW_mem_radical

def qDeleted : QuadraticForm F3 DeletedSpace := qUp.lift A A_le_radical

lemma qDeleted_polar_mk (x y : W) :
    QuadraticMap.polar qDeleted (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      QuadraticMap.polar qUp x y := by
  have hxy : (Submodule.Quotient.mk x + Submodule.Quotient.mk y : W ⧸ A) =
      Submodule.Quotient.mk (x + y) := (Submodule.Quotient.mk_add A).symm
  rw [QuadraticMap.polar, QuadraticMap.polar]
  rw [hxy]
  simp only [qDeleted, QuadraticMap.lift_mk]

lemma finrank_W : Module.finrank F3 W = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker sumLinear
  rw [LinearMap.range_eq_top.mpr sumLinear_surjective, finrank_top] at h
  have h1 : Module.finrank F3 F3 = 1 := Module.finrank_self F3
  have h2 : Module.finrank F3 Coord = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  change Module.finrank F3 (LinearMap.ker sumLinear) = 5
  rw [h1, h2] at h
  omega

lemma finrank_deleted : Module.finrank F3 DeletedSpace = 4 := by
  have h := Submodule.finrank_quotient_add_finrank (R := F3) (M := W) A
  change Module.finrank F3 (W ⧸ A) = 4
  rw [finrank_A, finrank_W] at h
  omega

lemma polarBilin_qDeleted_separatingLeft :
    (QuadraticMap.polarBilin qDeleted).SeparatingLeft := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change (Submodule.Quotient.mk z : W ⧸ A) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hcoord : ∀ i : Fin 5, (z : Coord) (Fin.castSucc i) = (z : Coord) 5 := by
      intro i
      let r : W := ⟨Pi.single (Fin.castSucc i) (1 : F3) - Pi.single (5 : Fin 6) 1, by
        rw [mem_W_iff]
        simp [Pi.sub_apply]⟩
      have h0 := hx (Submodule.Quotient.mk r)
      rw [QuadraticMap.polarBilin_apply_apply, qDeleted_polar_mk, polar_qUp_apply] at h0
      have hsingle (j : Fin 6) :
          (∑ x : Fin 6, (z : Coord) x * (Pi.single j (1 : F3) : Coord) x) =
            (z : Coord) j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp [Pi.single_eq_of_ne hbj]
        · intro hj
          simp at hj
      have hsum : (∑ j, (z : Coord) j * (r : Coord) j) =
          (z : Coord) (Fin.castSucc i) - (z : Coord) 5 := by
        simp only [r, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hsingle]
      rw [hsum] at h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (by decide))
    have hconst : ∀ i : Fin 6, (z : Coord) i = (z : Coord) 5 := by
      intro i
      fin_cases i
      · simpa using hcoord 0
      · simpa using hcoord 1
      · simpa using hcoord 2
      · simpa using hcoord 3
      · simpa using hcoord 4
      · rfl
    rw [A, Submodule.mem_span_singleton]
    refine ⟨(z : Coord) 5, ?_⟩
    ext i
    simp [oneVecW, oneVec, hconst i]

lemma polarBilin_qDeleted_nondegenerate :
    (QuadraticMap.polarBilin qDeleted).Nondegenerate :=
  (QuadraticMap.isSymm_polarBilin qDeleted).isRefl.nondegenerate_iff_separatingLeft.mpr
    polarBilin_qDeleted_separatingLeft

def c2Unit (x : TwoSetC2) : F3ˣ := if x = 1 then 1 else -1

@[simp] lemma c2Unit_one : c2Unit 1 = 1 := by simp [c2Unit]
@[simp] lemma c2Unit_neg : c2Unit twoSetC2neg = -1 := by
  simp [c2Unit]

lemma c2Unit_mul (x y : TwoSetC2) : c2Unit (x * y) = c2Unit x * c2Unit y := by
  rcases TwoSetC2.eq_one_or_eq_neg x with rfl | rfl <;>
    rcases TwoSetC2.eq_one_or_eq_neg y with rfl | rfl <;>
    simp [c2Unit, TwoSetC2.mul_self_eq_one]

@[simp] lemma c2Unit_inv (x : TwoSetC2) : c2Unit x⁻¹ = c2Unit x := by
  rcases TwoSetC2.eq_one_or_eq_neg x with rfl | rfl <;>
    simp [c2Unit, TwoSetC2.inv_eq_self]

lemma c2Unit_val_mul_self (x : TwoSetC2) :
    (c2Unit x : F3) * (c2Unit x : F3) = 1 := by
  rcases TwoSetC2.eq_one_or_eq_neg x with rfl | rfl <;>
    simp [c2Unit]

lemma c2Unit_eq_one_iff {x : TwoSetC2} : c2Unit x = 1 ↔ x = 1 := by
  constructor
  · intro h
    rcases TwoSetC2.eq_one_or_eq_neg x with hx | hx
    · exact hx
    · exfalso
      rw [hx] at h
      have h' : ((-1 : F3ˣ) : F3) = (1 : F3ˣ) := congrArg Units.val h
      exact (by decide : ((-1 : F3) ≠ (1 : F3))) h' 
  · rintro rfl
    simp

@[expose]
def permuteLinear (σ : Equiv.Perm (Fin 6)) : W ≃ₗ[F3] W where
  toFun z := ⟨fun i => (z : Coord) (σ.symm i), by
    rw [mem_W_iff]
    calc
      (∑ i, (z : Coord) (σ.symm i)) = ∑ i, (z : Coord) i :=
        Equiv.sum_comp σ.symm (fun i => (z : Coord) i)
      _ = 0 := (mem_W_iff _).mp z.2⟩
  invFun z := ⟨fun i => (z : Coord) (σ i), by
    rw [mem_W_iff]
    calc
      (∑ i, (z : Coord) (σ i)) = ∑ i, (z : Coord) i :=
        Equiv.sum_comp σ (fun i => (z : Coord) i)
      _ = 0 := (mem_W_iff _).mp z.2⟩
  left_inv z := by ext i; simp
  right_inv z := by ext i; simp
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

@[simp] lemma permuteLinear_apply (σ : Equiv.Perm (Fin 6)) (z : W) (i : Fin 6) :
    (permuteLinear σ z : Coord) i = (z : Coord) (σ.symm i) := rfl

lemma permuteLinear_oneVecW (σ : Equiv.Perm (Fin 6)) :
    permuteLinear σ oneVecW = oneVecW := by
  ext i
  simp [oneVecW, oneVec]

def scalarLinear (x : TwoSetC2) : W ≃ₗ[F3] W :=
  LinearEquiv.smulOfUnit (c2Unit x)

@[simp] lemma scalarLinear_apply (x : TwoSetC2) (z : W) :
    scalarLinear x z = (c2Unit x : F3) • z := by
  simp [scalarLinear, LinearEquiv.smulOfUnit, Units.smul_def]

def actionLinear (g : TwoSetC2 × Equiv.Perm (Fin 6)) : W ≃ₗ[F3] W :=
  (permuteLinear g.2).trans (scalarLinear g.1)

@[simp] lemma actionLinear_apply (g : TwoSetC2 × Equiv.Perm (Fin 6)) (z : W) (i : Fin 6) :
    (actionLinear g z : Coord) i =
      (c2Unit g.1 : F3) * (z : Coord) (g.2.symm i) := by
  simp [actionLinear, scalarLinear_apply, Pi.smul_apply]

lemma actionLinear_one :
    actionLinear (1 : TwoSetC2 × Equiv.Perm (Fin 6)) = LinearEquiv.refl F3 W := by
  ext z i
  simp [actionLinear_apply, Equiv.Perm.one_def, Equiv.refl_symm]

lemma actionLinear_mul (g h : TwoSetC2 × Equiv.Perm (Fin 6)) :
    actionLinear (g * h) = (actionLinear h).trans (actionLinear g) := by
  ext z i
  simp [actionLinear_apply, c2Unit_mul, Equiv.Perm.mul_def, mul_assoc]

lemma actionLinear_inv_apply (g : TwoSetC2 × Equiv.Perm (Fin 6)) (z : W) :
    actionLinear g (actionLinear g⁻¹ z) = z := by
  have h := congrArg (fun e : W ≃ₗ[F3] W => e z) (actionLinear_mul g g⁻¹)
  simpa [LinearEquiv.trans_apply, actionLinear_one] using h.symm

lemma actionLinear_mem_A (g : TwoSetC2 × Equiv.Perm (Fin 6)) {z : W} (hz : z ∈ A) :
    actionLinear g z ∈ A := by
  rw [actionLinear, LinearEquiv.trans_apply]
  rw [A, Submodule.mem_span_singleton] at hz ⊢
  obtain ⟨c, rfl⟩ := hz
  refine ⟨(c2Unit g.1 : F3) * c, ?_⟩
  simp [scalarLinear_apply, permuteLinear_oneVecW, smul_smul, mul_comm]

lemma map_actionLinear_A (g : TwoSetC2 × Equiv.Perm (Fin 6)) :
    A.map (actionLinear g).toLinearMap = A := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact actionLinear_mem_A g hz
  · intro z hz
    refine ⟨actionLinear g⁻¹ z, actionLinear_mem_A g⁻¹ hz, ?_⟩
    exact actionLinear_inv_apply g z

@[expose]
def actionQuot (g : TwoSetC2 × Equiv.Perm (Fin 6)) : DeletedSpace ≃ₗ[F3] DeletedSpace :=
  Submodule.Quotient.equiv A A (actionLinear g) (map_actionLinear_A g)

@[simp] lemma actionQuot_apply_mk (g : TwoSetC2 × Equiv.Perm (Fin 6)) (z : W) :
    actionQuot g (Submodule.Quotient.mk z) = Submodule.Quotient.mk (actionLinear g z) := by
  rw [actionQuot, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rfl

@[expose]
def actionQuotHom : (TwoSetC2 × Equiv.Perm (Fin 6)) →*
    (DeletedSpace ≃ₗ[F3] DeletedSpace) where
  toFun := actionQuot
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [actionQuot_apply_mk, actionLinear_one]
      rfl
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [actionQuot_apply_mk, LinearEquiv.mul_apply, actionQuot_apply_mk,
        actionQuot_apply_mk, actionLinear_mul]
      rfl

lemma qUp_permuteLinear (σ : Equiv.Perm (Fin 6)) (z : W) :
    qUp (permuteLinear σ z) = qUp z := by
  rw [qUp_apply, qUp_apply]
  simp only [permuteLinear_apply]
  exact Equiv.sum_comp σ.symm (fun i => (z : Coord) i * (z : Coord) i)

lemma qUp_actionLinear (g : TwoSetC2 × Equiv.Perm (Fin 6)) (z : W) :
    qUp (actionLinear g z) = qUp z := by
  rw [actionLinear, LinearEquiv.trans_apply, scalarLinear_apply]
  rw [QuadraticMap.map_smul, qUp_permuteLinear, c2Unit_val_mul_self, one_smul]

lemma qDeleted_apply_mk (z : W) :
    qDeleted (Submodule.Quotient.mk z) = qUp z := by
  rw [qDeleted, QuadraticMap.lift_mk]

lemma qDeleted_actionQuot (g : TwoSetC2 × Equiv.Perm (Fin 6)) (x : DeletedSpace) :
    qDeleted (actionQuot g x) = qDeleted x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [actionQuot_apply_mk, qDeleted_apply_mk, qDeleted_apply_mk, qUp_actionLinear]

@[expose]
def toOrthHom : (TwoSetC2 × Equiv.Perm (Fin 6)) →*
    TauCeti.QuadraticMap.orthogonalGroup qDeleted where
  toFun g := ⟨actionQuot g, by
    rw [QuadraticMap.mem_orthogonalGroup_iff]
    exact qDeleted_actionQuot g⟩
  map_one' := Subtype.ext (map_one actionQuotHom)
  map_mul' g h := Subtype.ext (map_mul actionQuotHom g h)

lemma toOrthHom_apply (g : TwoSetC2 × Equiv.Perm (Fin 6)) (x : DeletedSpace) :
    ((toOrthHom g : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
      DeletedSpace ≃ₗ[F3] DeletedSpace) x = actionQuot g x := rfl

def stdBasis (i : Fin 6) : Coord := Pi.single i (1 : F3)

lemma sumLinear_stdBasis (i : Fin 6) : sumLinear (stdBasis i) = 1 := by
  simp [sumLinear, stdBasis]

def root (i j : Fin 6) : Coord := stdBasis i - stdBasis j

@[expose]
def rootW (i j : Fin 6) : W :=
  ⟨root i j, by
    change sumLinear (root i j) = 0
    rw [root, map_sub, sumLinear_stdBasis, sumLinear_stdBasis, sub_self]⟩

@[simp] lemma rootW_val (i j : Fin 6) : (rootW i j : Coord) = root i j := rfl

lemma permuteLinear_rootW (σ : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    permuteLinear σ (rootW i j) = rootW (σ i) (σ j) := by
  ext k
  simp [permuteLinear_apply, rootW, root, stdBasis, Pi.sub_apply, Pi.single_apply,
    Equiv.symm_apply_eq]

lemma actionLinear_rootW (g : TwoSetC2 × Equiv.Perm (Fin 6)) (i j : Fin 6) :
    actionLinear g (rootW i j) = (c2Unit g.1 : F3) • rootW (g.2 i) (g.2 j) := by
  rw [actionLinear, LinearEquiv.trans_apply, scalarLinear_apply, permuteLinear_rootW]

def support (x : Coord) : Finset (Fin 6) := Finset.univ.filter (fun i => x i ≠ 0)

lemma eq_zero_of_mem_span_oneVec_of_support_card_le_four {x : Coord}
    (hx : x ∈ Submodule.span F3 {oneVec}) (hcard : (support x).card ≤ 4) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  by_cases hc : c = 0
  · simp [hc]
  · exfalso
    have h6 : (support (c • oneVec)).card = 6 := by
      simp [support, oneVec, hc]
    omega

lemma c2Unit_ne_zero (x : TwoSetC2) : (c2Unit x : F3) ≠ 0 :=
  (c2Unit x).ne_zero

lemma support_actionLinear_rootW_subset (g : TwoSetC2 × Equiv.Perm (Fin 6))
    (i j : Fin 6) :
    support (((actionLinear g (rootW i j) - rootW i j : W) : Coord)) ⊆
      ({i, j, g.2 i, g.2 j} : Finset (Fin 6)) := by
  intro k hk
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  by_contra hk'
  have hki : k ≠ i := fun h => hk' (by simp [h])
  have hkj : k ≠ j := fun h => hk' (by simp [h])
  have hksi : k ≠ g.2 i := fun h => hk' (by simp [h])
  have hksj : k ≠ g.2 j := fun h => hk' (by simp [h])
  have hroot1 : root i j k = 0 := by
    simp [root, stdBasis, Pi.sub_apply, hki, hkj]
  have hroot2 : root (g.2 i) (g.2 j) k = 0 := by
    simp [root, stdBasis, Pi.sub_apply, hksi, hksj]
  apply hk
  simp [Pi.sub_apply, actionLinear_rootW, hroot1, hroot2]

lemma toOrthHom_eq_one {g : TwoSetC2 × Equiv.Perm (Fin 6)}
    (hg : toOrthHom g = 1) : g = 1 := by
  have hact : actionQuot g = 1 := by
    have h : (toOrthHom g : DeletedSpace ≃ₗ[F3] DeletedSpace) = 1 :=
      congrArg Subtype.val hg
    simpa [toOrthHom] using h
  have hfix (i j : Fin 6) (hij : i ≠ j) : actionLinear g (rootW i j) = rootW i j := by
    have hq : actionQuot g (Submodule.Quotient.mk (rootW i j)) =
        Submodule.Quotient.mk (rootW i j) := by
      rw [hact]
      rfl
    rw [actionQuot_apply_mk] at hq
    have hdA : actionLinear g (rootW i j) - rootW i j ∈ A :=
      (Submodule.Quotient.eq A).mp hq
    have hxA : (((actionLinear g (rootW i j) - rootW i j : W) : Coord)) ∈
        Submodule.span F3 {oneVec} := by
      rw [A, Submodule.mem_span_singleton] at hdA
      obtain ⟨c, hc⟩ := hdA
      rw [← hc]
      change c • (oneVecW : Coord) ∈ Submodule.span F3 {oneVec}
      simpa [oneVecW] using (Submodule.smul_mem (Submodule.span F3 {oneVec}) c
        (Submodule.mem_span_singleton_self oneVec))
    have hcard : (support (((actionLinear g (rootW i j) - rootW i j : W) : Coord))).card ≤ 4 :=
      (Finset.card_le_card (support_actionLinear_rootW_subset g i j)).trans
        (by simpa using Finset.card_le_four)
    have hzero : actionLinear g (rootW i j) - rootW i j = 0 := by
      apply Subtype.ext
      exact eq_zero_of_mem_span_oneVec_of_support_card_le_four hxA hcard
    exact sub_eq_zero.mp hzero
  have hpair (i j : Fin 6) (hij : i ≠ j) : g.2 i = i ∨ g.2 i = j := by
    have hcoord : (c2Unit g.1 : F3) * root (g.2 i) (g.2 j) (g.2 i) = root i j (g.2 i) := by
      have h := congrFun (congrArg Subtype.val (hfix i j hij)) (g.2 i)
      simpa [actionLinear_rootW] using h
    by_contra h
    have h1 : g.2 i ≠ i := fun hh => h (Or.inl hh)
    have h2 : g.2 i ≠ j := fun hh => h (Or.inr hh)
    have hne : g.2 i ≠ g.2 j := fun hEq => hij (g.2.injective hEq)
    have hrootR : root i j (g.2 i) = 0 := by
      simp [root, stdBasis, Pi.sub_apply, h1, h2]
    have hrootL : root (g.2 i) (g.2 j) (g.2 i) = 1 := by
      simp [root, stdBasis, Pi.sub_apply, hne]
    rw [hrootR, hrootL, mul_one] at hcoord
    exact c2Unit_ne_zero g.1 hcoord
  have hσi (i : Fin 6) : g.2 i = i := by
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card
      (show 1 < Fintype.card (Fin 6) by decide) i
    have hij : i ≠ j := hji.symm
    obtain ⟨k, hkj, hki⟩ := Fin.exists_ne_and_ne_of_two_lt j i (by decide : 2 < 6)
    have hik : i ≠ k := hki.symm
    rcases hpair i j hij with h | h
    · exact h
    rcases hpair i k hik with h' | h'
    · exact h'
    · exfalso
      exact hkj (h.symm.trans h').symm
  have hσ : g.2 = 1 := Equiv.ext hσi
  have hc : (c2Unit g.1 : F3) = 1 := by
    have h := congrFun (congrArg Subtype.val (hfix 0 1 (by decide))) 0
    have h' : (c2Unit g.1 : F3) = 1 := by
      simpa [actionLinear_rootW, hσ, root, stdBasis, Pi.sub_apply, Pi.single_apply] using h
    exact h'
  have hg1 : g.1 = 1 := c2Unit_eq_one_iff.mp (Units.ext hc)
  exact Prod.ext hg1 hσ

lemma toOrthHom_injective : Function.Injective toOrthHom := by
  intro g h hgh
  have hker : toOrthHom (g * h⁻¹) = 1 := by
    simp [map_mul, map_inv, hgh]
  have hgh1 : g * h⁻¹ = 1 := toOrthHom_eq_one hker
  calc
    g = g * h⁻¹ * h := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = 1 * h := by rw [hgh1]
    _ = h := one_mul h

lemma natCard_twoSetC2 : Nat.card TwoSetC2 = 2 := by
  rw [show Nat.card TwoSetC2 = Nat.card (ZMod 2) from
    Nat.card_congr (Multiplicative.toAdd (α := ZMod 2))]
  exact Nat.card_zmod 2

lemma natCard_perm_six : Nat.card (Equiv.Perm (Fin 6)) = 1440 / 2 := by
  rw [Nat.card_perm, Nat.card_fin]
  decide

lemma natCard_twoSetC2_perm : Nat.card (TwoSetC2 × Equiv.Perm (Fin 6)) = 1440 := by
  rw [Nat.card_prod, natCard_twoSetC2, natCard_perm_six]

lemma natCard_orthogonalGroup_qDeleted :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup qDeleted) = 1440 := by
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype DeletedSpace := Submodule.Quotient.fintype A
  haveI : Finite (DeletedSpace ≃ₗ[F3] DeletedSpace) :=
    Finite.of_injective (fun e : DeletedSpace ≃ₗ[F3] DeletedSpace =>
      (e : DeletedSpace → DeletedSpace)) DFunLike.coe_injective
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup qDeleted) :=
    Finite.of_injective (fun e : TauCeti.QuadraticMap.orthogonalGroup qDeleted =>
      (e : DeletedSpace ≃ₗ[F3] DeletedSpace)) Subtype.coe_injective
  have hle : 1440 ≤ Nat.card (TauCeti.QuadraticMap.orthogonalGroup qDeleted) := by
    rw [← natCard_twoSetC2_perm]
    exact Nat.card_le_card_of_injective toOrthHom toOrthHom_injective
  by_cases hplus : ∃ W : Submodule F3 DeletedSpace,
      Module.finrank F3 W = 2 ∧ ∀ w ∈ W, qDeleted w = 0
  · have hcard := CFSG.StandardType.OrthF3.card_orthogonalGroup_four_plus qDeleted
      polarBilin_qDeleted_nondegenerate finrank_deleted hplus
    rw [hcard] at hle
    norm_num at hle
  · exact CFSG.StandardType.OrthF3.card_orthogonalGroup_four_minus qDeleted
      polarBilin_qDeleted_nondegenerate finrank_deleted hplus

noncomputable instance : Fintype W := Fintype.ofFinite W
noncomputable instance : Fintype DeletedSpace := Submodule.Quotient.fintype A
noncomputable instance : Finite (DeletedSpace ≃ₗ[F3] DeletedSpace) :=
  Finite.of_injective (fun e : DeletedSpace ≃ₗ[F3] DeletedSpace =>
    (e : DeletedSpace → DeletedSpace)) DFunLike.coe_injective
noncomputable instance : Finite (TauCeti.QuadraticMap.orthogonalGroup qDeleted) :=
  Finite.of_injective (fun e : TauCeti.QuadraticMap.orthogonalGroup qDeleted =>
    (e : DeletedSpace ≃ₗ[F3] DeletedSpace)) Subtype.coe_injective

def vDeleted : DeletedSpace := Submodule.Quotient.mk (rootW 0 1)

lemma qDeleted_vDeleted : qDeleted vDeleted = 2 := by
  rw [vDeleted, qDeleted_apply_mk, qUp_apply]
  simp [rootW, root, stdBasis, Pi.sub_apply, Pi.single_apply, Fin.sum_univ_six]
  norm_num

lemma qDeleted_vDeleted_ne_zero : qDeleted vDeleted ≠ 0 := by
  rw [qDeleted_vDeleted]
  decide

lemma toOrthHom_bijective : Function.Bijective toOrthHom := by
  refine toOrthHom_injective.bijective_of_nat_card_le ?_
  rw [natCard_twoSetC2_perm, natCard_orthogonalGroup_qDeleted]

@[expose]
noncomputable def toOrthEquiv :
    (TwoSetC2 × Equiv.Perm (Fin 6)) ≃*
      TauCeti.QuadraticMap.orthogonalGroup qDeleted :=
  MulEquiv.ofBijective toOrthHom toOrthHom_bijective

@[simp] lemma toOrthEquiv_apply (g : TwoSetC2 × Equiv.Perm (Fin 6)) :
    toOrthEquiv g = toOrthHom g := rfl

@[simp] lemma toOrthEquiv_symm_apply
    (a : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
    toOrthHom (toOrthEquiv.symm a) = a := by
  rw [← toOrthEquiv_apply, MulEquiv.apply_symm_apply]

lemma actionQuot_vDeleted (g : TwoSetC2 × Equiv.Perm (Fin 6)) :
    actionQuot g vDeleted =
      Submodule.Quotient.mk
        ((c2Unit g.1 : F3) • rootW (g.2 0) (g.2 1)) := by
  change actionQuot g (Submodule.Quotient.mk (rootW 0 1)) = _
  rw [actionQuot_apply_mk, actionLinear_rootW]

lemma rootW_swap (i j : Fin 6) : rootW j i = -rootW i j := by
  ext k
  simp [rootW, root, stdBasis, Pi.sub_apply]

lemma toOrthHom_vDeleted_of_mem_twoSetStabilizer
    {g : TwoSetC2 × Equiv.Perm (Fin 6)}
    (hg : g ∈ CFSG.twoSetStabilizer (0 : Fin 6) 1 (by decide)) :
    actionQuot g vDeleted = vDeleted := by
  have hperm : g.2 ∈ CFSG.twoSetStabilizerPerm (0 : Fin 6) 1 := by
    rw [← CFSG.map_snd_twoSetStabilizer (0 : Fin 6) 1 (by decide)]
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  rw [actionQuot_vDeleted]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk (rootW 0 1)
  rcases CFSG.mem_twoSetStabilizerPerm_apply_a hperm with h0 | h0
  · have h1 : g.2 1 = 1 :=
      CFSG.mem_twoSetStabilizerPerm_fixes_b_of_fixes_a (by decide) hperm h0
    have hg1 : g.1 = 1 := by
      rcases TwoSetC2.eq_one_or_eq_neg g.1 with hg1 | hg1
      · exact hg1
      · exfalso
        have hneg : g.2 0 = 1 :=
          (CFSG.twoSetStabilizer_fst_eq_neg_iff (by decide) hg).mp hg1
        exact (by decide : (0 : Fin 6) ≠ 1) (h0.symm.trans hneg)
    rw [hg1, h0, h1]
    simp [c2Unit_one]
  · have h1 : g.2 1 = 0 :=
      CFSG.mem_twoSetStabilizerPerm_maps_b_of_maps_a (by decide) hperm h0
    have hg1 : g.1 = CFSG.twoSetC2neg :=
      (CFSG.twoSetStabilizer_fst_eq_neg_iff (by decide) hg).mpr h0
    rw [hg1, h0, h1, c2Unit_neg, rootW_swap]
    simp

lemma actionQuot_vDeleted_eq_smul_of_mem_twoSetStabilizerPerm
    {g : TwoSetC2 × Equiv.Perm (Fin 6)}
    (hperm : g.2 ∈ CFSG.twoSetStabilizerPerm (0 : Fin 6) 1) :
    ∃ c : F3, actionQuot g vDeleted = c • vDeleted := by
  rw [actionQuot_vDeleted]
  rcases CFSG.mem_twoSetStabilizerPerm_apply_a hperm with h0 | h0
  · have h1 : g.2 1 = 1 :=
      CFSG.mem_twoSetStabilizerPerm_fixes_b_of_fixes_a (by decide) hperm h0
    refine ⟨(c2Unit g.1 : F3), ?_⟩
    rw [h0, h1]
    change Submodule.Quotient.mk ((c2Unit g.1 : F3) • rootW 0 1) =
      (c2Unit g.1 : F3) • Submodule.Quotient.mk (rootW 0 1)
    rw [Submodule.Quotient.mk_smul]
  · have h1 : g.2 1 = 0 :=
      CFSG.mem_twoSetStabilizerPerm_maps_b_of_maps_a (by decide) hperm h0
    refine ⟨-(c2Unit g.1 : F3), ?_⟩
    rw [h0, h1, rootW_swap]
    have hscalar : (c2Unit g.1 : F3) • (-rootW 0 1) =
        (-(c2Unit g.1 : F3)) • rootW 0 1 :=
      (smul_neg (c2Unit g.1 : F3) (rootW 0 1)).trans
        (neg_smul (c2Unit g.1 : F3) (rootW 0 1)).symm
    rw [hscalar]
    change Submodule.Quotient.mk ((-(c2Unit g.1 : F3)) • rootW 0 1) =
      (-(c2Unit g.1 : F3)) • Submodule.Quotient.mk (rootW 0 1)
    rw [Submodule.Quotient.mk_smul]

lemma toOrthHom_vDeleted_in_span_of_mem_twoSetStabilizerPerm
    {g : TwoSetC2 × Equiv.Perm (Fin 6)}
    (hperm : g.2 ∈ CFSG.twoSetStabilizerPerm (0 : Fin 6) 1) :
    ((toOrthHom g : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
      DeletedSpace ≃ₗ[F3] DeletedSpace) vDeleted ∈
        Submodule.span F3 {vDeleted} := by
  obtain ⟨c, hc⟩ := actionQuot_vDeleted_eq_smul_of_mem_twoSetStabilizerPerm hperm
  rw [toOrthHom_apply, hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self vDeleted)

theorem deletedOrthogonalGroup_eq_top_of_stabilizer_le
    {H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup qDeleted)}
    (hstab : ∀ a : TauCeti.QuadraticMap.orthogonalGroup qDeleted,
      ((a : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[F3] DeletedSpace) vDeleted = vDeleted → a ∈ H)
    (hmove : ∃ a ∈ H,
      ((a : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[F3] DeletedSpace) vDeleted ∉
          Submodule.span F3 {vDeleted}) :
    H = ⊤ := by
  let K : Subgroup (TwoSetC2 × Equiv.Perm (Fin 6)) := H.comap toOrthEquiv
  have hKS : CFSG.twoSetStabilizer (0 : Fin 6) 1 (by decide) ≤ K := by
    intro g hg
    change toOrthEquiv g ∈ H
    refine hstab (toOrthEquiv g) ?_
    rw [toOrthEquiv_apply, toOrthHom_apply]
    exact toOrthHom_vDeleted_of_mem_twoSetStabilizer hg
  obtain ⟨h, hhH, hmove⟩ := hmove
  let g : TwoSetC2 × Equiv.Perm (Fin 6) := toOrthEquiv.symm h
  have hgfix : toOrthHom g = h := by
    simp [g]
  have hgK : g ∈ K := by
    change toOrthEquiv g ∈ H
    rw [show toOrthEquiv g = h by simp [g]]
    exact hhH
  have hgP : g.2 ∉ CFSG.twoSetStabilizerPerm (0 : Fin 6) 1 := by
    intro hperm
    have hspan := toOrthHom_vDeleted_in_span_of_mem_twoSetStabilizerPerm hperm
    have hline : ((h : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[F3] DeletedSpace) vDeleted ∈
          Submodule.span F3 {vDeleted} := by
      simpa [hgfix] using hspan
    exact hmove hline
  have hKtop : K = ⊤ :=
    CFSG.twoSetStabilizer_le_of_moved_eq_top hKS ⟨g, hgK, hgP⟩
  rw [eq_top_iff]
  intro a ha
  let g : TwoSetC2 × Equiv.Perm (Fin 6) := toOrthEquiv.symm a
  have hgK : g ∈ K := by
    rw [hKtop]
    exact Subgroup.mem_top g
  change toOrthEquiv g ∈ H at hgK
  simpa [g] using hgK

lemma not_exists_isotropic_plane_qDeleted :
    ¬ ∃ U : Submodule F3 DeletedSpace,
      Module.finrank F3 U = 2 ∧ ∀ u ∈ U, qDeleted u = 0 := by
  rintro ⟨U, hU, hUzero⟩
  have hcard := CFSG.StandardType.OrthF3.card_orthogonalGroup_four_plus qDeleted
    polarBilin_qDeleted_nondegenerate finrank_deleted ⟨U, hU, hUzero⟩
  rw [natCard_orthogonalGroup_qDeleted] at hcard
  norm_num at hcard

end CFSG.LinearAlgebra.OrthogonalFourMinusThree
