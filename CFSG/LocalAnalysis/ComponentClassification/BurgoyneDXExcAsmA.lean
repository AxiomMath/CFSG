module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXTwin8
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcComp

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

attribute [local instance] GeneralizedFitting.normal

theorem exists_kappa_of_mem_family {F : Type} [Field F] [Finite F] {p : ℕ} [CharP F p]
    {γ : MulAut (P8 F)} (hγ : γ ∈ projectivePointFamilyAut (Q8 F)) :
    ∃ g : similarityPairs (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F)),
      MulAut.congr (p8Stated F) γ = oκ _ g := by
  obtain ⟨f, hcard, hmod⟩ := exists_model8 F (p := p)
  rw [coordinate_plus_family_eq_matrixImage hmod F hcard (MulEquiv.refl _)] at hγ
  obtain ⟨g, rfl⟩ := hγ
  exact ⟨g, by ext x; rfl⟩

theorem exists_kappa_picR {X : Type} [Group X] {F : Type} [Field F] [Finite F] {p : ℕ}
    [CharP F p] (θ : GeneralizedFitting.subgroup X ≃* P8 F) {R : GL (Fin (2 * 4)) F}
    (hS₁ : ∀ v, oQ R ((1 : GL (Fin (2 * 4)) F).val *ᵥ v) =
      ((1 : Fˣ) : F) * reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F) v)
    {a : MulAut (GeneralizedFitting.subgroup X)}
    (ha : MulAut.congr θ a ∈ projectivePointFamilyAut (Q8 F)) :
    ∃ gs : similarityPairs (oQ R), MulAut.congr (picR θ 1 1 hS₁) a = oκ _ gs := by
  obtain ⟨g₀, hg₀⟩ := exists_kappa_of_mem_family (p := p) ha
  refine ⟨transPair 1 1 hS₁ g₀, ?_⟩
  rw [← oTransport_kappa, ← hg₀]
  exact MulEquiv.ext fun x => rfl

theorem oTransport_one_pi8 {F : Type} [Field F] {R : GL (Fin (2 * 4)) F}
    (hS₁ : ∀ v, oQ R ((1 : GL (Fin (2 * 4)) F).val *ᵥ v) =
      ((1 : Fˣ) : F) * reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F) v)
    (hRQ : matrixDerived (Q8 F) ≤ matrixDerived (oQ R)) (x : Sp8 F) :
    oTransport 1 1 hS₁ (p8Stated F (pi8 F x)) =
      projH _ (⟨spinGL F x, hRQ (spinM F x).2⟩ : matrixDerived (oQ R)) := by
  rw [pi8_eq_proj_spinM]
  refine (oTransport_proj 1 1 hS₁ (spinM F x)).trans ?_
  congr 1
  apply Subtype.ext
  change _ = ((spinM F x : matrixDerived (Q8 F)) : GL (Fin (2 * 4)) F)
  exact (coe_derivedTransport 1 1 hS₁ (spinM F x)).trans (by rw [one_mul, inv_one, mul_one])

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)

include hq in
theorem eq_one_of_socleHom_eq {s : MulAut (K ⧸ pPrimeCore 2 K)}
    (h : ∀ x, socleHom K hq hsimple hnab (s x) = socleHom K hq hsimple hnab x) : s = 1 := by
  have hz : ∀ x, ∃ z ∈ center (K ⧸ pPrimeCore 2 K), s x = x * z := by
    intro x
    refine ⟨x⁻¹ * s x, ?_, by group⟩
    have h1 : s x * x⁻¹ ∈ center (K ⧸ pPrimeCore 2 K) := by
      rw [← ker_socleHom K hq hsimple hnab, MonoidHom.mem_ker, map_mul, map_inv, h x,
        mul_inv_cancel]
    have h2 : x⁻¹ * s x = x⁻¹ * (s x * x⁻¹) * x := by group
    rw [h2, mem_center_iff.1 h1 x⁻¹, inv_mul_cancel_right]
    exact h1
  have hfix : ∀ a b : K ⧸ pPrimeCore 2 K, s ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨za, hza, hsa⟩ := hz a
    obtain ⟨zb, hzb, hsb⟩ := hz b
    rw [map_commutatorElement, hsa, hsb, PSL.commutatorElement_mul_mem_center a b hza hzb]
  have hle : commutator (K ⧸ pPrimeCore 2 K) ≤ autFixed s := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    exact hfix a b
  have htop := Group.isPerfect_def.1 hq.1
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ autFixed s := hle (htop ▸ mem_top x)
  exact hx

theorem congr_socleAut_apply {T : Type} [Group T]
    (Θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* T) (s : MulAut (K ⧸ pPrimeCore 2 K))
    (x : K ⧸ pPrimeCore 2 K) :
    MulAut.congr Θ (socleAut K hq hsimple hnab s) (Θ (socleHom K hq hsimple hnab x)) =
      Θ (socleHom K hq hsimple hnab (s x)) := by
  change Θ (socleAut K hq hsimple hnab s (Θ.symm (Θ (socleHom K hq hsimple hnab x)))) = _
  rw [MulEquiv.symm_apply_apply, ← socleHom_socleAut]

theorem socleAction_apply_socleHom {T : Type} [Group T]
    (Θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* T) (g : J) (x : K ⧸ pPrimeCore 2 K) :
    socleAction Θ ((rhoZ K).rangeRestrict g) (Θ (socleHom K hq hsimple hnab x)) =
      Θ (socleHom K hq hsimple hnab (phiO K g x)) := by
  rw [socleHom_phiO]
  change Θ (MulAut.conjNormal ((rhoZ K).rangeRestrict g)
    (Θ.symm (Θ (socleHom K hq hsimple hnab x)))) = _
  rw [MulEquiv.symm_apply_apply]

include hq in
theorem socle_comp {T : Type} [Group T] [Finite T]
    (Θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* T)
    (hZ : IsPGroup 2 (center (K ⧸ pPrimeCore 2 K))) {s : MulAut (K ⧸ pPrimeCore 2 K)}
    {Q : Subgroup (K ⧸ pPrimeCore 2 K)} (hQs : Q ≤ autFixed s)
    (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s))) :
    Q.map (Θ.toMonoidHom.comp (socleHom K hq hsimple hnab)) ≤
        autFixed (MulAut.congr Θ (socleAut K hq hsimple hnab s)) ∧
      IsPComponent 2 ((Q.map (Θ.toMonoidHom.comp (socleHom K hq hsimple hnab))).subgroupOf
        (autFixed (MulAut.congr Θ (socleAut K hq hsimple hnab s)))) := by
  have hker : (Θ.toMonoidHom.comp (socleHom K hq hsimple hnab)).ker =
      center (K ⧸ pPrimeCore 2 K) := by
    rw [← ker_socleHom K hq hsimple hnab]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact MulEquiv.map_eq_one_iff _
  refine isPComponent_map_autFixed _ ?_ hker.le (hker ▸ hZ) (fun x => ?_) hQs hQc
  · rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact Θ.surjective.comp (socleHom_surjective K hq hsimple hnab)
  · change Θ (socleHom K hq hsimple hnab (s x)) =
      Θ (socleAut K hq hsimple hnab s (Θ.symm (Θ (socleHom K hq hsimple hnab x))))
    rw [MulEquiv.symm_apply_apply, socleHom_socleAut]

include hq in
theorem socle_comp_of_eq {T : Type} [Group T] [Finite T]
    (Θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* T)
    (hZ : IsPGroup 2 (center (K ⧸ pPrimeCore 2 K))) {s : MulAut (K ⧸ pPrimeCore 2 K)}
    {Q : Subgroup (K ⧸ pPrimeCore 2 K)} (hQs : Q ≤ autFixed s)
    (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s))) {Qb : Subgroup T}
    (hQb : Q.map (Θ.toMonoidHom.comp (socleHom K hq hsimple hnab)) = Qb) {σ : MulAut T}
    (hσ : MulAut.congr Θ (socleAut K hq hsimple hnab s) = σ) :
    Qb ≤ autFixed σ ∧ IsPComponent 2 (Qb.subgroupOf (autFixed σ)) := by
  subst hQb hσ
  exact socle_comp K hq hsimple hnab Θ hZ hQs hQc

include hq in
theorem isPGroup_center8 {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F) {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x))
    (hαs : Function.Surjective α) : IsPGroup 2 (center (K ⧸ pPrimeCore 2 K)) := by
  intro z
  obtain ⟨y, hy⟩ := hαs (z : K ⧸ pPrimeCore 2 K)
  have hz : socleHom K hq hsimple hnab z = 1 := by
    rw [← MonoidHom.mem_ker, ker_socleHom]
    exact z.2
  have hy1 : pi8 F y = 1 := by
    have e1 := hα y
    rw [hy, hz] at e1
    exact (MulEquiv.map_eq_one_iff θ.symm).1 e1.symm
  have hyc : y ∈ center (Sp8 F) := by rw [← ker_pi8]; exact hy1
  have hyy := mul_self_eq_one_of_mem_center8 F h2 hyc
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one, ← hy, ← map_mul, hyy, map_one]

theorem map_socle_eq {F : Type} [Field F]
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F) {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x))
    {R : GL (Fin (2 * 4)) F}
    (hS₁ : ∀ v, oQ R ((1 : GL (Fin (2 * 4)) F).val *ᵥ v) =
      ((1 : Fˣ) : F) * reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F) v)
    (hRQ : matrixDerived (Q8 F) ≤ matrixDerived (oQ R)) {Q : Subgroup (K ⧸ pPrimeCore 2 K)}
    (hQ : ⁅Q.comap α, Q.comap α⁆.map α = Q) :
    Q.map ((picR θ 1 1 hS₁).toMonoidHom.comp (socleHom K hq hsimple hnab)) =
      ((⁅Q.comap α, Q.comap α⁆.map (spinGL F)).subgroupOf (matrixDerived (oQ R))).map
        (projH _) := by
  have hνα : ∀ x : Sp8 F, (picR θ 1 1 hS₁).toMonoidHom.comp (socleHom K hq hsimple hnab) (α x) =
      projH _ (⟨spinGL F x, hRQ (spinM F x).2⟩ : matrixDerived (oQ R)) := by
    intro x
    rw [MonoidHom.comp_apply, hα]
    change oTransport 1 1 hS₁ (p8Stated F (θ (θ.symm (pi8 F x)))) = _
    rw [MulEquiv.apply_symm_apply]
    exact oTransport_one_pi8 hS₁ hRQ x
  have hQ' : Q.map ((picR θ 1 1 hS₁).toMonoidHom.comp (socleHom K hq hsimple hnab)) =
      (⁅Q.comap α, Q.comap α⁆.map α).map
        ((picR θ 1 1 hS₁).toMonoidHom.comp (socleHom K hq hsimple hnab)) := by rw [hQ]
  rw [hQ', Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨spinGL F x, hRQ (spinM F x).2⟩, mem_subgroupOf.2 ⟨x, hx, rfl⟩, (hνα x).symm⟩
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨x, hx, hxX⟩ := mem_subgroupOf.1 hX
    refine ⟨x, hx, ?_⟩
    rw [MonoidHom.comp_apply, hνα]
    congr 1
    exact Subtype.ext hxX

end CFSG.ComponentClassification.Burgoyne.DX
