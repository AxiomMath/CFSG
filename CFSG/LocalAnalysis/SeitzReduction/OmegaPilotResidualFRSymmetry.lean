module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityStd
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Quasithin (perfectCore perfectCore_le map_perfectCore perfectCore_eq_self_of_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem symmetryCore_eq_and_mulEquiv (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {v : Fin (2 * n) → K} (hv : coordinateQuadPlus n K v = 1) :
    perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) =
        autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v) ∧
      Nonempty (↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) ≃*
        StatedProj (StatedSp (n - 1) K)) := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hout : symmetryAut (coordinateQuadPlus n K) v ∉
      inner (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective _ y
    rw [← kappa_derived_eq_conj] at hy
    have h1 := CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.isometryKappa_injective
      hreg.1 hreg.2 hE (a₁ := Subgroup.inclusion (matrixDerived_le_isometries _) g)
      (a₂ := symmetryIsometry _ v) hy
    apply CFSG.ComponentClassification.EvenOrthSelector.symmetryGL_not_mem_matrixDerived
      hreg.1 hreg.2 hE hv
    have h2 : ((Subgroup.inclusion (matrixDerived_le_isometries _) g : matrixIsometries _) :
        GL (Fin (2 * n)) K) = symmetryGL _ v := congrArg Subtype.val h1
    rw [← h2]
    exact g.2
  obtain ⟨ε⟩ := F4Pilot.omega_symmetry_fixed hf hK (by omega) hreg.1 hreg.2 hE hv hout
  obtain ⟨-, hSp⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (r := n - 1)
    (k := K) (by omega) (by omega)
  have e : ↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) ≃*
      StatedProj (StatedSp (n - 1) K) :=
    (MulEquiv.subgroupCongr (autFixSubgroup_eq_fixedSubgroup' _)).trans (ε.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot
          (n - 1))).trans QuotientGroup.quotientBot).symm)
  have hFperf : Group.IsPerfect ↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.mp hFperf), ⟨e⟩⟩

theorem outerCommutative_symmetryCore (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {v : Fin (2 * n) → K} (hv : coordinateQuadPlus n K v = 1) :
    OuterCommutative ↥(perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))) := by
  obtain ⟨heq, ⟨e⟩⟩ := symmetryCore_eq_and_mulEquiv hK hn hv
  exact outerCommutative_of_mulEquiv ((MulEquiv.subgroupCongr heq).trans e)
    (outerCommutative_statedProj_statedSp (by omega : 3 ≤ n - 1))

omit [Finite K] [CharP K 2] in
theorem ne_zero_of_quad_eq_one {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}
    (hv : Q v = 1) : v ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at hv
  exact zero_ne_one hv

omit [CharP K 2] in
theorem exists_symmetryCore_eq_map (hn : 5 ≤ n) {v₀ v : Fin (2 * n) → K}
    (hv₀ : coordinateQuadPlus n K v₀ = 1) (hv : coordinateQuadPlus n K v = 1) :
    ∃ δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) =
        (perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₀))).map
          δ.toMonoidHom := by
  obtain ⟨P₁, P₂, -, h₁₂, -, -⟩ := exists_three_pairs_plus (K := K) (n := n) (by omega)
  have hreg := regular_coordinateQuadPlus n K (by omega)
  obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hreg.1 h₁₂
    (ne_zero_of_quad_eq_one hv₀) (ne_zero_of_quad_eq_one hv) (hv₀.trans hv.symm)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) :=
    elementaryGroup_le_orthogonalGroup _ hg
  set A : GL (Fin (2 * n)) K := matrixLinearIso.symm g with hAdef
  have hA : A ∈ matrixIsometries (coordinateQuadPlus n K) := by
    change matrixLinearIso A ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K)
    rw [hAdef, MulEquiv.apply_symm_apply]
    exact hgO
  have hAv : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ v₀ = v := by
    change matrixLinearIso A v₀ = v
    rw [hAdef, MulEquiv.apply_symm_apply, hgv]
  set a : matrixIsometries (coordinateQuadPlus n K) := ⟨A, hA⟩ with ha
  have hsym : symmetryIsometry (coordinateQuadPlus n K) v =
      a * symmetryIsometry (coordinateQuadPlus n K) v₀ * a⁻¹ := by
    apply Subtype.ext
    change symmetryGL _ v = A * symmetryGL _ v₀ * A⁻¹
    rw [conj_symmetryGL hA, hAv]
  have hα : symmetryAut (coordinateQuadPlus n K) v =
      isometryConjugationHom _ a * symmetryAut (coordinateQuadPlus n K) v₀ *
        (isometryConjugationHom _ a)⁻¹ := by
    change isometryConjugationHom _ (symmetryIsometry _ v) = _
    rw [hsym, map_mul, map_mul, map_inv]
    rfl
  refine ⟨isometryConjugationHom _ a, ?_⟩
  rw [hα, LinearPilot.autFixSubgroup_conj, map_perfectCore]

theorem exists_symmetryCore_fix (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    ∃ v₀ : Fin (2 * n) → K, coordinateQuadPlus n K v₀ = 1 ∧
      ∀ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
        (∀ x ∈ perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₀)),
          β x = x) →
        plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn β = 1 := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_plus (K := K) (n := n) (by omega)
  have hv₀ : coordinateQuadPlus n K (P₁.e + P₁.f) = 1 := by
    rw [QuadraticMap.map_add (coordinateQuadPlus n K), P₁.Q_e, P₁.Q_f, P₁.polar_ef, zero_add,
      zero_add]
  have hv₀u : polar (coordinateQuadPlus n K) (P₁.e + P₁.f) P₂.e = 0 := by
    rw [polar_add_left, h₁₂.ee, h₁₂.fe, add_zero]
  have hv₀w : polar (coordinateQuadPlus n K) (P₁.e + P₁.f) P₃.e = 0 := by
    rw [polar_add_left, h₁₃.ee, h₁₃.fe, add_zero]
  have hind : LinearIndependent K ![P₂.e, P₃.e] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun x => polar (coordinateQuadPlus n K) x P₂.f) hab
    have h2 := congrArg (fun x => polar (coordinateQuadPlus n K) x P₃.f) hab
    have hwf₂ : polar (coordinateQuadPlus n K) P₃.e P₂.f = 0 := by rw [polar_comm]; exact h₂₃.fe
    simp only [polar_add_left, polar_smul_left, P₂.polar_ef, P₃.polar_ef, h₂₃.ef, hwf₂,
      polar_zero_left, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨P₁.e + P₁.f, hv₀, fun β hβ => ?_⟩
  have hcore := (symmetryCore_eq_and_mulEquiv hK hn hv₀).1
  have hs : ∀ x, polar (coordinateQuadPlus n K) (P₁.e + P₁.f) x = 0 →
      coordinateSemilinearMap (matrixIsometryInclusion (coordinateQuadPlus n K)
        (symmetryIsometry (coordinateQuadPlus n K) (P₁.e + P₁.f))).val x = x := by
    intro x hx
    rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl, matrixLinearEquiv_apply]
    change (symmetryGL (coordinateQuadPlus n K) (P₁.e + P₁.f) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ x = x
    rw [symmetryGL_mulVec_of_charTwo hv₀, hx, zero_smul, add_zero]
  refine plusFieldPart_eq_one_of_fix_rootGroup hK hn P₂.Q_e P₃.Q_e h₂₃.ee hind β
    fun c E hE => hβ _ ?_
  rw [hcore, mem_autFixSubgroup]
  have hpol : polar (coordinateQuadPlus n K) (P₁.e + P₁.f) (c • P₃.e) = 0 := by
    rw [polar_smul_right, hv₀w, smul_zero]
  exact kappa_projHom_eichler
    (inclusion_mem_unitMultiplierPairs (symmetryIsometry (coordinateQuadPlus n K) (P₁.e + P₁.f)))
    E E hE (by rw [hE, hs _ hv₀u, hs _ hpol])

theorem symmetryCoresRigid_plus (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    SymmetryCoresRigid n K (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn) := by
  obtain ⟨v₀, hv₀, hcen⟩ := exists_symmetryCore_fix hK hn
  intro v₁ v₂ hv₁ hv₂
  obtain ⟨δ₁, h₁⟩ := exists_symmetryCore_eq_map hn hv₀ hv₁
  obtain ⟨δ₂, h₂⟩ := exists_symmetryCore_eq_map hn hv₀ hv₂
  rw [h₁, h₂]
  exact fieldRigidInOf_map_of_centralizer _ (fun x => orthAutFieldPart_conj _ _ x) hcen
    (outerCommutative_symmetryCore hK hn hv₀) δ₁ δ₂

end CFSG.SeitzReduction.OmegaPilot
