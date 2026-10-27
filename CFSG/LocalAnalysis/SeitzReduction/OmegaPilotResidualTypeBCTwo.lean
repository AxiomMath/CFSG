module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCData

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le_derivedSeriesOf)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open scoped commutatorElement

section Plane

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
  (hNN : ∀ v, N (N v) = 0)

include hadj hNN in
theorem quad_sub_eq_zero_of_mem_range {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgN : ∀ x, g (N x) = N (g x))
    {w : Fin d → K} (hw : w ∈ LinearMap.range N) :
    g w - w ∈ LinearMap.range N ∧ Q (g w - w) = 0 := by
  have hgw : g w ∈ LinearMap.range N := mem_range_of_commute (g := (g : _ →ₗ[K] _)) hgN w hw
  refine ⟨sub_mem hgw hw, ?_⟩
  have h1 : QuadraticMap.polar Q (g w) w = 0 :=
    polar_mem_range_ker N hadj hgw (range_le_ker N hNN hw)
  have h2 : Q (g w) = Q w := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg w
  rw [sub_eq_add_neg, quad_add_eq, QuadraticMap.map_neg, QuadraticMap.polar_neg_right, h1, h2,
    neg_zero, add_zero, CharTwo.add_self_eq_zero]

theorem polar_sNil_self (s : matrixIsometries Q) (a : Fin d → K) :
    QuadraticMap.polar Q (sNil s.val a) a = Q (sNil s.val a) := by
  have hs : Q (matrixLinearEquiv s.val a) = Q a := (mem_matrixIsometries_iff Q s.val).mp s.2 a
  have e : matrixLinearEquiv s.val a = sNil s.val a + a := by rw [sNil_apply, sub_add_cancel]
  have h1 := quad_add_eq Q (sNil s.val a) a
  rw [← e, hs] at h1
  have h2 : Q (sNil s.val a) + Q (sNil s.val a) = 0 := CharTwo.add_self_eq_zero _
  linear_combination -h1 - h2

end Plane

section Two

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [CharP K 2] in
theorem quad_smul_add_smul (α γ : K) (u w : Fin d → K) :
    Q (α • u + γ • w) = α * α * Q u + γ * γ * Q w + α * γ * QuadraticMap.polar Q u w := by
  rw [quad_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

variable (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
  (hNN : ∀ v, N (N v) = 0)

omit [CharP K 2] in
include hadj hNN in
theorem exists_eq_smul_of_quad_eq_zero_two (hW2 : finrank K (LinearMap.range N) = 2)
    {w₁ : Fin d → K} (hw₁ : w₁ ∈ LinearMap.range N) (hQw₁ : Q w₁ ≠ 0)
    {u : Fin d → K} (hu : u ∈ LinearMap.range N) (hQu : Q u = 0) (hu0 : u ≠ 0)
    {v : Fin d → K} (hv : v ∈ LinearMap.range N) (hQv : Q v = 0) : ∃ c : K, v = c • u := by
  have hpol : ∀ {x y : Fin d → K}, x ∈ LinearMap.range N → y ∈ LinearMap.range N →
      QuadraticMap.polar Q x y = 0 := fun hx hy =>
    polar_mem_range_ker N hadj hx (range_le_ker N hNN hy)
  have hli : LinearIndependent K ![u, w₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hQ0 := congrArg Q hab
    rw [quad_smul_add_smul, hQu, hpol hu hw₁, QuadraticMap.map_zero] at hQ0
    have hb : b = 0 := by
      have : b * b * Q w₁ = 0 := by linear_combination hQ0
      rcases mul_eq_zero.mp this with h | h
      · exact mul_self_eq_zero.mp h
      · exact absurd h hQw₁
    subst hb
    rw [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hu0, rfl⟩
  have hle : Submodule.span K {u, w₁} ≤ LinearMap.range N := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hw₁
  have hfin : finrank K (Submodule.span K {u, w₁}) = 2 := by
    have := finrank_span_eq_card hli
    rwa [show Set.range ![u, w₁] = {u, w₁} by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]] at this
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hW2])
  rw [← heq] at hv
  obtain ⟨α, γ, rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [quad_smul_add_smul, hQu, hpol hu hw₁] at hQv
  have hγ : γ = 0 := by
    have : γ * γ * Q w₁ = 0 := by linear_combination hQv
    rcases mul_eq_zero.mp this with h | h
    · exact mul_self_eq_zero.mp h
    · exact absurd h hQw₁
  exact ⟨α, by rw [hγ, zero_smul, add_zero]⟩

theorem apply_eq_self_of_quad_eq_zero_two (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (s : matrixIsometries Q) (hss : s * s = 1)
    (hW2 : finrank K (LinearMap.range (sNil s.val)) = 2)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), Q w ≠ 0)
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgN : ∀ x, g (sNil s.val x) = sNil s.val (g x))
    {u : Fin d → K} (hu : u ∈ LinearMap.range (sNil s.val)) (hQu : Q u = 0) : g u = u := by
  have hadj := polar_sNil_left s hss
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  obtain ⟨w₁, hw₁, hQw₁⟩ := hW
  have hline := fun {v : Fin d → K} (hv : v ∈ LinearMap.range (sNil s.val)) (hQv : Q v = 0) =>
    exists_eq_smul_of_quad_eq_zero_two (sNil s.val) hadj hNN hW2 hw₁ hQw₁ hu hQu hu0 hv hQv
  obtain ⟨hgu1, hgu2⟩ := quad_sub_eq_zero_of_mem_range (sNil s.val) hadj hNN hg hgN hu
  obtain ⟨α, hα⟩ := hline hgu1 hgu2
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, hb⟩ : ∃ b, QuadraticMap.polar Q (sNil s.val a) b ≠ 0 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    exact hu0 (hB.1 _ fun b => by rw [QuadraticMap.polarBilin_apply_apply]; exact hall b)
  have hNb := quad_sub_eq_zero_of_mem_range (sNil s.val) hadj hNN hg hgN
    (LinearMap.mem_range_self (sNil s.val) b)
  obtain ⟨e, he⟩ := hline hNb.1 hNb.2
  have hgb : QuadraticMap.polar Q (sNil s.val a) (g b) = QuadraticMap.polar Q (sNil s.val a) b := by
    have h1 : QuadraticMap.polar Q (sNil s.val a) (g b - b) = 0 := by
      rw [← QuadraticMap.polarBilin_apply_apply, hadj, map_sub, ← hgN, he,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_comm, polar_sNil_self s a, hQu, smul_zero]
    rw [QuadraticMap.polar_sub_right, sub_eq_zero] at h1
    exact h1
  have hiso := polar_apply_of_mem_orth hg (sNil s.val a) b
  have hgNa : g (sNil s.val a) = (1 + α) • sNil s.val a := by
    rw [add_smul, one_smul, ← hα, add_sub_cancel]
  rw [hgNa, QuadraticMap.polar_smul_left, hgb, smul_eq_mul] at hiso
  have hα0 : α = 0 := by
    have : α * QuadraticMap.polar Q (sNil s.val a) b = 0 := by linear_combination hiso
    exact (mul_eq_zero.mp this).resolve_right hb
  rw [hgNa, hα0, add_zero, one_smul]

theorem apply_comm_of_two (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (s : matrixIsometries Q) (hss : s * s = 1)
    (hW2 : finrank K (LinearMap.range (sNil s.val)) = 2)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), Q w ≠ 0)
    {g g' : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgN : ∀ x, g (sNil s.val x) = sNil s.val (g x))
    (hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg'N : ∀ x, g' (sNil s.val x) = sNil s.val (g' x))
    {w : Fin d → K} (hw : w ∈ LinearMap.range (sNil s.val)) : g (g' w) = g' (g w) := by
  have hadj := polar_sNil_left s hss
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  obtain ⟨h1, h2⟩ := quad_sub_eq_zero_of_mem_range (sNil s.val) hadj hNN hg hgN hw
  obtain ⟨h1', h2'⟩ := quad_sub_eq_zero_of_mem_range (sNil s.val) hadj hNN hg' hg'N hw
  have e1 := apply_eq_self_of_quad_eq_zero_two hB s hss hW2 hW hg hgN h1' h2'
  have e2 := apply_eq_self_of_quad_eq_zero_two hB s hss hW2 hW hg' hg'N h1 h2
  have k1 : g' w = w + (g' w - w) := by abel
  have k2 : g w = w + (g w - w) := by abel
  rw [k1, map_add, e1, k2, map_add, e2]
  abel

end Two

section Core

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] def fixRangeSubgroup (hQ : ∃ v, Q v ≠ 0) (N : (Fin d → K) →ₗ[K] (Fin d → K)) :
    Subgroup (matrixProjectiveDerived Q) where
  carrier := {z | ∀ w ∈ LinearMap.range N, projLift hQ z w = w}
  one_mem' := fun w _ => by rw [projLift_one']; rfl
  mul_mem' := fun {a b} ha hb w hw => by
    rw [projLift_mul, LinearEquiv.mul_apply, hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    rw [projLift_inv]
    conv_lhs => rw [← ha w hw]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl

theorem projLift_mem_orthogonalGroup (hQ : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) :
    projLift hQ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  CFSG.Quasithin.A3.commutator_self_le _ (projLift_mem_orthDerived hQ x)

theorem core_fix_range_of_two (hQ : ∃ v, Q v ≠ 0) (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (s : matrixIsometries Q) (hss : s * s = 1)
    (hW2 : finrank K (LinearMap.range (sNil s.val)) = 2)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), Q w ≠ 0) {x : matrixProjectiveDerived Q}
    (hx : x ∈ perfectCore (autFixSubgroup (isometryConjugationHom Q s)))
    {w : Fin d → K} (hw : w ∈ LinearMap.range (sNil s.val)) : projLift hQ x w = w := by
  have hcomm : ∀ y ∈ autFixSubgroup (isometryConjugationHom Q s),
      ∀ v, projLift hQ y (sNil s.val v) = sNil s.val (projLift hQ y v) :=
    fun y hy v => projLift_sub_one_of_mem_autFixSubgroup hQ s hy v
  have hle : ⁅autFixSubgroup (isometryConjugationHom Q s),
      autFixSubgroup (isometryConjugationHom Q s)⁆ ≤ fixRangeSubgroup hQ (sNil s.val) := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂ v hv
    have hc : ∀ {a b : matrixProjectiveDerived Q}, a ∈ autFixSubgroup (isometryConjugationHom Q s) →
        b ∈ autFixSubgroup (isometryConjugationHom Q s) → ∀ {u}, u ∈ LinearMap.range (sNil s.val) →
        projLift hQ a (projLift hQ b u) = projLift hQ b (projLift hQ a u) :=
      fun ha hb _ hu => apply_comm_of_two hB s hss hW2 hW (projLift_mem_orthogonalGroup hQ _)
        (hcomm _ ha) (projLift_mem_orthogonalGroup hQ _) (hcomm _ hb) hu
    have hmem : ∀ {a : matrixProjectiveDerived Q}, a ∈ autFixSubgroup (isometryConjugationHom Q s) →
        ∀ {u}, u ∈ LinearMap.range (sNil s.val) → projLift hQ a u ∈ LinearMap.range (sNil s.val) :=
      fun ha _ hu => mem_range_of_commute (g := (projLift hQ _ : (Fin d → K) →ₗ[K] (Fin d → K)))
        (hcomm _ ha) _ hu
    have hi₁ := inv_mem hy₁
    have hi₂ := inv_mem hy₂
    have hinv : ∀ (a : matrixProjectiveDerived Q) (u : Fin d → K),
        projLift hQ a (projLift hQ a⁻¹ u) = u := fun a u => by
      rw [← LinearEquiv.mul_apply, ← projLift_mul, mul_inv_cancel, projLift_one']
      rfl
    change projLift hQ (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) v = v
    rw [projLift_mul, projLift_mul, projLift_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hc hy₂ hi₁ (hmem hi₂ hv), hinv, hinv]
  exact hle (perfectCore_le_derivedSeriesOf _ 1 hx) w hw

end Core

section Plus

theorem finrank_kerQuot_add {K : Type} [Field K] {d : ℕ} (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hNN : ∀ v, N (N v) = 0) :
    finrank K (LinearMap.ker N ⧸ rangeInKer N) + 2 * finrank K (LinearMap.range N) = d := by
  have h1 := Submodule.finrank_quotient_add_finrank (rangeInKer N)
  have h2 : finrank K (rangeInKer N) = finrank K (LinearMap.range N) :=
    (Submodule.comapSubtypeEquivOfLe (range_le_ker N hNN)).finrank_eq
  have h3 := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fin_fun] at h3
  omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem spLeviData_typeC_two (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW2 : finrank K (LinearMap.range (sNil s.val)) = 2)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) :
    SpLeviData (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  have hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega)
  have hB := (regular_coordinateQuadPlus n K (by omega)).1
  have hdim := finrank_kerQuot_add (sNil s.val) (sNil_sNil (congrArg Subtype.val hss))
  have hposM : finrank K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) ≠ 0 := by
    omega
  refine spLeviData_typeBC_unequal hf hK hn hq4 s hss hW hposM ⊤ ?_ ?_
    (spLeviSection_top _ _) ?_
  · rw [inf_top_eq]
    refine (isPGroup_ker_inf_ker hQ (perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
      (sNil s.val) (fun x hx v => projLift_sNil_of_mem_core _ s hx v)).to_le fun x hx => ⟨?_, hx⟩
    refine MonoidHom.mem_ker.mpr ?_
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact core_fix_range_of_two hQ hB s hss hW2 hW x.2 w.2
  · intro M _ hle
    exact Or.inr (top_le_iff.mp hle)
  · intro r hr
    exact isEmpty_quotient_top_mulEquiv _ (by omega)

end Plus

end CFSG.SeitzReduction.OmegaPilot
