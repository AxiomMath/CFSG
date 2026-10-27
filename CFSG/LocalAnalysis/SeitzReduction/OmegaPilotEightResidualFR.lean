module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualRecentre
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRSymmetry

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
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)

section RigidE

variable {C : Type*} [Group C] {L : Type*} [Field L]

theorem fieldRigidInOfE_of_isEmpty (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L))
    {X₁ X₂ : Subgroup C} (h : IsEmpty (↥X₁ ≃* ↥X₂)) : FieldRigidInOfE E fp X₁ X₂ := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX
  exact (h.false ((X₁.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (X₂.equivMapOfInjective φ₂ hφ₂).symm))).elim

variable [Finite L]

theorem fieldRigidInOfE_map (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L))
    {X₁ X₂ : Subgroup C} (h : FieldRigidInOfE E fp X₁ X₂) {δ₁ δ₂ : MulAut C} (hδ₁ : δ₁ ∈ E)
    (hδ₂ : δ₂ ∈ E) :
    FieldRigidInOfE E fp (X₁.map δ₁.toMonoidHom) (X₂.map δ₂.toMonoidHom) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβ₁E hβ₂E hβ₁ hc₁ hc₂
  have hm : ∀ {δ β : MulAut C}, δ ∈ E → β ∈ E → δ⁻¹ * β * δ ∈ E := fun hδ hβ =>
    mul_mem (mul_mem (inv_mem hδ) hβ) hδ
  have hcls : ∀ {δ β : MulAut C} (hδ : δ ∈ E) (hβ : β ∈ E),
      fp ⟨δ⁻¹ * β * δ, hm hδ hβ⟩ = fp ⟨β, hβ⟩ := fun {δ β} hδ hβ => by
    have e1 : (⟨δ⁻¹ * β * δ, hm hδ hβ⟩ : E) = (⟨δ, hδ⟩ : E)⁻¹ * ⟨β, hβ⟩ * ⟨δ, hδ⟩ :=
      Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, LinearPilot.ringEquiv_mul_comm (fp ⟨δ, hδ⟩)⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]
  have hX' : X₁.map (φ₁.comp δ₁.toMonoidHom) = X₂.map (φ₂.comp δ₂.toMonoidHom) := by
    rw [← Subgroup.map_map, ← Subgroup.map_map, hX]
  have key := h Γ (φ₁.comp δ₁.toMonoidHom) (φ₂.comp δ₂.toMonoidHom)
    (hφ₁.comp δ₁.injective) (hφ₂.comp δ₂.injective) hX' γ (δ₁⁻¹ * β₁ * δ₁) (δ₂⁻¹ * β₂ * δ₂)
    (hm hδ₁ hβ₁E) (hm hδ₂ hβ₂E)
    (fun x hx => by
      have hx' : δ₁ x ∈ X₁.map δ₁.toMonoidHom := ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hβ₁ _ hx'
      have : (δ₁⁻¹ * β₁ * δ₁) x = y := by
        rw [MulAut.mul_apply, MulAut.mul_apply, ← hyx]
        exact δ₁.symm_apply_apply y
      rw [this]
      exact hy)
    (fun x => by
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.mul_apply]
      rw [← hc₁ (δ₁ x)]
      congr 1
      exact δ₁.apply_symm_apply _)
    (fun x => by
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.mul_apply]
      rw [← hc₂ (δ₂ x)]
      congr 1
      exact δ₂.apply_symm_apply _)
  rwa [hcls hδ₁ hβ₁E, hcls hδ₂ hβ₂E] at key

omit [Finite L] in
theorem fieldRigidInOfE_self_of_centralizer [Finite C] (E : Subgroup (MulAut C))
    (fp : E →* (L ≃+* L)) {X : Subgroup C}
    (hinn : ∀ x : C, ∃ h : MulAut.conj x ∈ E, fp ⟨_, h⟩ = 1)
    (hcen : ∀ (β : MulAut C) (hβ : β ∈ E), (∀ x ∈ X, β x = x) → fp ⟨β, hβ⟩ = 1)
    (hout : OuterCommutative X) : FieldRigidInOfE E fp X X := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβ₁E hβ₂E hβ₁ hc₁ hc₂
  set ψ : ↥X ≃* ↥X := (X.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (X.equivMapOfInjective φ₂ hφ₂).symm) with hψ
  have hψφ : ∀ x : X, φ₂ (ψ x : C) = φ₁ x := fun x => by
    have h1 : X.equivMapOfInjective φ₂ hφ₂ (ψ x) =
        MulEquiv.subgroupCongr hX (X.equivMapOfInjective φ₁ hφ₁ x) := by
      rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun y : ↥(X.map φ₂) => (y : Γ)) h1
    simp only [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  have hkey : ∀ x : X, β₂ (ψ x : C) = (ψ ⟨β₁ x, hβ₁ x x.2⟩ : C) := fun x => by
    apply hφ₂
    rw [hc₂, hψφ, hψφ, hc₁]
  have hβ₂ : ∀ y ∈ X, β₂ y ∈ X := fun y hy => by
    obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
    have : y = (ψ x : C) := by rw [hx]
    rw [this, hkey]
    exact (ψ _).2
  set θ₁ := restrictAutOfMapsTo β₁ X hβ₁ with hθ₁
  set θ₂ := restrictAutOfMapsTo β₂ X hβ₂ with hθ₂
  have hconj : θ₂ * ψ = ψ * θ₁ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply, coe_restrictAutOfMapsTo, hkey]
    rfl
  have hθ : θ₂ = ψ * θ₁ * ψ⁻¹ := by rw [← hconj, mul_inv_cancel_right]
  obtain ⟨x₀, hx₀⟩ := hout ψ θ₁
  have hθ' : θ₂ = MulAut.conj x₀ * θ₁ := by
    rw [hx₀, hθ, inv_mul_cancel_right]
  obtain ⟨hcE, hcfp⟩ := hinn (x₀ : C)
  have hfix : ∀ y ∈ X, ((MulAut.conj (x₀ : C) * β₁)⁻¹ * β₂) y = y := fun y hy => by
    have h1 : β₂ y = (MulAut.conj (x₀ : C) * β₁) y := by
      have h2 := congrArg (fun θ : MulAut ↥X => ((θ ⟨y, hy⟩ : ↥X) : C)) hθ'
      simp only [hθ₂, coe_restrictAutOfMapsTo, MulAut.mul_apply, MulAut.conj_apply,
        hθ₁] at h2
      rw [h2, MulAut.mul_apply, MulAut.conj_apply]
      rfl
    rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
  have hmem : (MulAut.conj (x₀ : C) * β₁)⁻¹ * β₂ ∈ E :=
    mul_mem (inv_mem (mul_mem hcE hβ₁E)) hβ₂E
  have h := hcen _ hmem hfix
  have e1 : (⟨_, hmem⟩ : E) = (⟨_, hcE⟩ * ⟨β₁, hβ₁E⟩ : E)⁻¹ * ⟨β₂, hβ₂E⟩ := Subtype.ext rfl
  rw [e1, map_mul, map_inv, inv_mul_eq_one, map_mul, hcfp, one_mul] at h
  exact h

end RigidE

section Symmetry

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem symmetryCore_eq_and_mulEquiv_of_four_le (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
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

theorem outerCommutative_symmetryCore_of_four_le (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {v : Fin (2 * n) → K} (hv : coordinateQuadPlus n K v = 1) :
    OuterCommutative ↥(perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))) := by
  obtain ⟨heq, ⟨e⟩⟩ := symmetryCore_eq_and_mulEquiv_of_four_le hK hn hv
  exact outerCommutative_of_mulEquiv ((MulEquiv.subgroupCongr heq).trans e)
    (outerCommutative_statedProj_statedSp (by omega : 3 ≤ n - 1))

omit [CharP K 2] in
theorem exists_symmetryCore_eq_map_of_four_le (hn : 4 ≤ n) {v₀ v : Fin (2 * n) → K}
    (hv₀ : coordinateQuadPlus n K v₀ = 1) (hv : coordinateQuadPlus n K v = 1) :
    ∃ δ ∈ matrixProjectiveImage (coordinateQuadPlus n K),
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
  refine ⟨isometryConjugationHom _ a, ⟨_, rfl⟩, ?_⟩
  rw [hα, LinearPilot.autFixSubgroup_conj, map_perfectCore]

end Symmetry

section SymmetryFix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem plusImageFieldPart_eq_one_of_fix_rootGroup (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {u w : Fin (2 * n) → K} (hu : coordinateQuadPlus n K u = 0)
    (hw : coordinateQuadPlus n K w = 0) (huw : polar (coordinateQuadPlus n K) u w = 0)
    (hind : LinearIndependent K ![u, w])
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hβE : β ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (hfix : ∀ (c : K) (E : orthDerived (coordinateQuadPlus n K)),
      (E : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
        eichler (coordinateQuadPlus n K) u (c • w) →
        β (projHom _ E) = projHom _ E) :
    plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn ⟨β, hβE⟩ = 1 := by
  have hreg := regular_coordinateQuadPlus n K hn
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep hβE
  have hσ : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn
      ⟨matrixProjectiveConjugationHom _ S, hβE⟩ = S.val.right :=
    plusImageFieldPart_kappa _ hK hn S
  rw [hσ]
  exact right_eq_one_of_fix_rootGroup hreg.1 hreg.2
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_ne_zero_of_polar_nondegenerate
      (by omega) hreg.1) hS hu hw huw hind hfix

theorem exists_symmetryCore_fix_of_four_le (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    ∃ v₀ : Fin (2 * n) → K, coordinateQuadPlus n K v₀ = 1 ∧
      ∀ (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
        (hβE : β ∈ matrixProjectiveImage (coordinateQuadPlus n K)),
        (∀ x ∈ perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₀)),
          β x = x) →
        plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by omega) ⟨β, hβE⟩ = 1 := by
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
  refine ⟨P₁.e + P₁.f, hv₀, fun β hβE hβ => ?_⟩
  have hcore := (symmetryCore_eq_and_mulEquiv_of_four_le hK hn hv₀).1
  have hs : ∀ x, polar (coordinateQuadPlus n K) (P₁.e + P₁.f) x = 0 →
      coordinateSemilinearMap (matrixIsometryInclusion (coordinateQuadPlus n K)
        (symmetryIsometry (coordinateQuadPlus n K) (P₁.e + P₁.f))).val x = x := by
    intro x hx
    rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl, matrixLinearEquiv_apply]
    change (symmetryGL (coordinateQuadPlus n K) (P₁.e + P₁.f) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ x = x
    rw [symmetryGL_mulVec_of_charTwo hv₀, hx, zero_smul, add_zero]
  refine plusImageFieldPart_eq_one_of_fix_rootGroup hK (by omega) P₂.Q_e P₃.Q_e h₂₃.ee hind β hβE
    fun c E hE => hβ _ ?_
  rw [hcore, mem_autFixSubgroup]
  have hpol : polar (coordinateQuadPlus n K) (P₁.e + P₁.f) (c • P₃.e) = 0 := by
    rw [polar_smul_right, hv₀w, smul_zero]
  exact kappa_projHom_eichler
    (inclusion_mem_unitMultiplierPairs (symmetryIsometry (coordinateQuadPlus n K) (P₁.e + P₁.f)))
    E E hE (by rw [hE, hs _ hv₀u, hs _ hpol])

theorem symmetryCoresRigidE_of_four_le (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {v₁ v₂ : Fin (2 * n) → K} (hv₁ : coordinateQuadPlus n K v₁ = 1)
    (hv₂ : coordinateQuadPlus n K v₂ = 1) :
    FieldRigidInOfE (matrixProjectiveImage (coordinateQuadPlus n K))
      (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by omega))
      (perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₁)))
      (perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₂))) := by
  obtain ⟨v₀, hv₀, hcen⟩ := exists_symmetryCore_fix_of_four_le hK hn
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_symmetryCore_eq_map_of_four_le hn hv₀ hv₁
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_symmetryCore_eq_map_of_four_le hn hv₀ hv₂
  rw [h₁, h₂]
  exact fieldRigidInOfE_map _ _ (fieldRigidInOfE_self_of_centralizer _ _
    (fun x => ⟨conj_mem_plusImage x, plusImageFieldPart_conj _ hK _ x⟩) hcen
    (outerCommutative_symmetryCore_of_four_le hK hn hv₀)) hδ₁ hδ₂

end SymmetryFix

@[expose] def PlusFourHigherRankCoresRigidE (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : Prop :=
  ∀ s₁ s₂ : matrixIsometries (coordinateQuadPlus 4 K),
    orderOf (isometryConjugationHom _ s₁) = 2 → orderOf (isometryConjugationHom _ s₂) = 2 →
    2 ≤ (((s₁ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) - 1).rank →
    2 ≤ (((s₂ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) - 1).rank →
    FieldRigidInOfE (matrixProjectiveImage (coordinateQuadPlus 4 K))
      (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num))
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s₁)))
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s₂)))

section Assembly

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem nonFieldCoresRigidE_plusFour_of_higherRank (hK : Nat.card K = 2 ^ f)
    (hhigh : PlusFourHigherRankCoresRigidE K hK) :
    NonFieldCoresRigidE (matrixProjectiveImage (coordinateQuadPlus 4 K))
      (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)) := by
  intro α₁ α₂ h₁ h₂ hα₁ hα₂ hne₁ hne₂ hfp₁ hfp₂
  rcases nonField_cases_four hK h₁ hα₁ hne₁ hfp₁ with ⟨v₁, hv₁, rfl⟩ | ⟨s₁, rfl, hs₁, hr₁⟩ <;>
    rcases nonField_cases_four hK h₂ hα₂ hne₂ hfp₂ with ⟨v₂, hv₂, rfl⟩ | ⟨s₂, rfl, hs₂, hr₂⟩
  · exact symmetryCoresRigidE_of_four_le hK le_rfl hv₁ hv₂
  · exact fieldRigidInOfE_of_isEmpty _ _ ⟨fun ψ =>
      not_isSimpleGroup_core_of_two_le_rank_of_four_le le_rfl s₂ hs₂ hr₂
        (@MulEquiv.isSimpleGroup _ _ _ _ (symmetryCore_spec_of_four_le hK le_rfl hv₁).1 ψ.symm)⟩
  · exact fieldRigidInOfE_of_isEmpty _ _ ⟨fun ψ =>
      not_isSimpleGroup_core_of_two_le_rank_of_four_le le_rfl s₁ hs₁ hr₁
        (@MulEquiv.isSimpleGroup _ _ _ _ (symmetryCore_spec_of_four_le hK le_rfl hv₂).1 ψ)⟩
  · exact hhigh s₁ s₂ hs₁ hs₂ hr₁ hr₂

end Assembly

theorem omegaPlusFourResidualInput_of_higherRankCoresRigidE
    (hhigh : ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f),
      2 ≤ f → Even f → PlusFourHigherRankCoresRigidE K hK) :
    OmegaPlusFourResidualInput :=
  omegaPlusFourResidualInput_of_matrixInput fun f K _ _ _ hK hf2 hfe =>
    ⟨nonFieldCoresRigidE_plusFour_of_higherRank hK (hhigh f K hK hf2 hfe),
      fieldRecentreInE_plusFour hK⟩

end CFSG.SeitzReduction.OmegaPilot
