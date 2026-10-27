module

public import CFSG.ClassicalGroups.Orthogonal.BorelSolvableMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBorel
public import CFSG.ClassicalGroups.SpecialLinear.ComponentBorelQuotient
public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
open QuadraticMap Module
open scoped Pointwise commutatorElement

variable {K : Type*} [Field K]
  {A A' : Type*} [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
  {qA : QuadraticForm K A} {qA' : QuadraticForm K A'} {r : ℕ}

@[expose] def tailProdIsometry (ψ : qA.IsometryEquiv qA') (r : ℕ) :
    (quadTail r qA).IsometryEquiv (quadTail r qA') :=
  (QuadraticMap.IsometryEquiv.refl (quadPlus r K)).prod ψ

@[simp]
theorem tailProdIsometry_apply (ψ : qA.IsometryEquiv qA') (r : ℕ)
    (v : (Fin r ⊕ Fin r → K) × A) :
    tailProdIsometry ψ r v = (v.1, ψ v.2) :=
  rfl

@[simp]
theorem tailProdIsometry_toLinearEquiv_apply (ψ : qA.IsometryEquiv qA') (r : ℕ)
    (v : (Fin r ⊕ Fin r → K) × A) :
    (tailProdIsometry ψ r).toLinearEquiv v = (v.1, ψ v.2) :=
  rfl

theorem tailFlag_map_tailProdIsometry (ψ : qA.IsometryEquiv qA') (r i : ℕ) :
    (tailFlag K A r i).map (tailProdIsometry ψ r).toLinearMap = tailFlag K A' r i := by
  rw [tailFlag, tailFlag, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by
      dsimp only
      change hypVec K A' (.inl j) =
        (tailProdIsometry ψ r).toLinearEquiv (hypVec K A (.inl j))
      rw [tailProdIsometry_toLinearEquiv_apply]
      simp [hypVec]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hypVec K A (.inl j), ⟨j, hj, rfl⟩, by
      change (tailProdIsometry ψ r) (hypVec K A (.inl j)) = hypVec K A' (.inl j)
      rw [tailProdIsometry_apply]
      simp [hypVec]⟩

theorem exists_isometry_minusTailForm {A : Type*} [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] {qA : QuadraticForm K A} [Finite K] [CharP K 2]
    (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (h2 : finrank K A = 2) :
    ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (qA.IsometryEquiv (minusTailForm K b c)) := by
  obtain ⟨-, -, hnf, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      qA hreg
  have hdim : finrank K A = 2 * 1 := by rw [h2]
  rcases hnf 1 (by norm_num) hdim with ⟨b, hb⟩ | ⟨β, γ, -, hirr, b, hb⟩
  · exfalso
    have hv : b (Sum.inl (0 : Fin 1)) ≠ 0 := b.linearIndependent.ne_zero _
    have hq0 : qA (b (Sum.inl (0 : Fin 1))) = 0 := by
      have h := hb (Pi.single 0 1) (fun _ => 0)
      simpa using h
    exact hv (hani _ hq0)
  · refine ⟨β, γ, hirr, ?_⟩
    have hcoord : (quadMinus 1 K β γ).IsometryEquiv (minusTailForm K β γ) :=
      (minusTailIsometry 1 K β γ).symm.trans
        (QuadraticMap.IsometryEquiv.uniqueProd (quadPlus 0 K) (minusTailForm K β γ))
    refine ⟨(?_ : qA.IsometryEquiv (quadMinus 1 K β γ)).trans hcoord⟩
    refine ⟨b.equivFun, fun v => ?_⟩
    rw [← Basis.sum_equivFun b v]
    have hsum : (∑ i, b.equivFun v i • b i) =
        ∑ i, b.equivFun v (Sum.inl i) • b (Sum.inl i) +
          ∑ i, b.equivFun v (Sum.inr (Sum.inl i)) • b (Sum.inr (Sum.inl i)) +
          b.equivFun v (Sum.inr (Sum.inr 0)) • b (Sum.inr (Sum.inr 0)) +
          b.equivFun v (Sum.inr (Sum.inr 1)) • b (Sum.inr (Sum.inr 1)) := by
      rw [Fintype.sum_sum_type]
      simp [Fintype.sum_sum_type]
    rw [hsum, hb, quadMinus_apply]
    simp

theorem stdFlag_map_tailProdIsometry (ψ : qA.IsometryEquiv qA') (r : ℕ) :
    (fun i => (OrthogonalTail.stdFlag K A r i).map (tailProdIsometry ψ r).toLinearMap) =
      OrthogonalTail.stdFlag K A' r :=
  funext fun i => tailFlag_map_tailProdIsometry ψ r (i + 1)

theorem isSolvable_minusProjectiveBorel {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hr : 3 ≤ r) {A : Type} [AddCommGroup A] [Module K A]
    {qA : QuadraticForm K A} (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate)
    (hm : finrank K A = 1 ∨ finrank K A = 2) :
    Group.IsSolvable ↥(((tailBorel r qA).subgroupOf
      (orthElementaryGroup (quadTail r qA))).map
      (QuotientGroup.mk' (elemScalars (quadTail r qA)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  haveI : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  haveI : Finite A := Module.finite_of_finite K
  obtain ⟨n, hn⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      qA hreg).1
  have h2 : finrank K A = 2 := by rcases hm with h | h <;> omega
  obtain ⟨b, c, hirr, ⟨e⟩⟩ := exists_isometry_minusTailForm hani hreg h2
  let ψ1 : (quadTail r qA).IsometryEquiv (quadMinus (r + 1) K b c) :=
    (tailProdIsometry e r).trans (minusTailIsometry (r + 1) K b c)
  let ψ2 : (quadTail r (minusTailForm K b c)).IsometryEquiv (quadMinus (r + 1) K b c) :=
    minusTailIsometry (r + 1) K b c
  have hQ : ⇑(quadMinus (r + 1) K b c) = StatedQuadMinus (r + 1) K b c :=
    coe_quadMinus (r + 1) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c)⁆ =
      elementaryGroup (quadMinus (r + 1) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  let Φ1 := tailOmegaEquiv ψ1 hQ hE
  let Φ2 := tailOmegaEquiv ψ2 hQ hE
  let F : Fin r → Submodule K (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2 → K) :=
    tailModelFlag r K (Fin 2)
  have hF2 : ∀ i, F i =
      (OrthogonalTail.stdFlag K (Fin 2 → K) r i).map ψ2.toLinearMap := by
    intro i
    simpa [F, OrthogonalTail.stdFlag] using tailModelFlag_eq_map ψ2 (fun _ => rfl) i
  have hψ1 : ψ1.toLinearMap = ψ2.toLinearMap.comp (tailProdIsometry e r).toLinearMap := rfl
  have hF1 : ∀ i, F i = (OrthogonalTail.stdFlag K A r i).map ψ1.toLinearMap := by
    intro i
    rw [hψ1, Submodule.map_comp]
    rw [congrFun (stdFlag_map_tailProdIsometry e r) i]
    exact hF2 i
  have hflag1 : (fun i => (F i).map ψ1.symm.toLinearMap) = OrthogonalTail.stdFlag K A r := by
    funext i
    rw [hF1 i, ← Submodule.map_comp]
    rw [show (ψ1.symm.toLinearMap.comp ψ1.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => ψ1.symm_apply_apply v, Submodule.map_id]
  have hflag2 : (fun i => (F i).map ψ2.symm.toLinearMap) =
      OrthogonalTail.stdFlag K (Fin 2 → K) r := by
    funext i
    rw [hF2 i, ← Submodule.map_comp]
    rw [show (ψ2.symm.toLinearMap.comp ψ2.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => ψ2.symm_apply_apply v, Submodule.map_id]
  let B0 : Subgroup (orthElementaryGroup (quadTail r qA)) :=
    (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))
  let B0' : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
    (tailBorel r (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail r (minusTailForm K b c)))
  have hB1 : (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
      Φ1.toMonoidHom = B0 := by
    rw [tailOmegaEquiv_flagStabilizer ψ1 hQ hE F, hflag1]
    exact tailBorel_subgroupOf_eq.symm
  have hB2 : (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
      Φ2.toMonoidHom = B0' := by
    rw [tailOmegaEquiv_flagStabilizer ψ2 hQ hE F, hflag2]
    exact tailBorel_subgroupOf_eq.symm
  let Φ : orthElementaryGroup (quadTail r qA) ≃*
      orthElementaryGroup (quadTail r (minusTailForm K b c)) := Φ1.symm.trans Φ2
  have hmap : B0.map Φ.toMonoidHom = B0' := by
    rw [show B0 = (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
        Φ1.toMonoidHom from hB1.symm]
    rw [Subgroup.map_map (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F)
      Φ.toMonoidHom Φ1.toMonoidHom]
    have hcomp : Φ.toMonoidHom.comp Φ1.toMonoidHom = Φ2.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      change Φ (Φ1 x) = Φ2 x
      rw [show Φ = Φ1.symm.trans Φ2 from rfl, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [hcomp, hB2]
  haveI hTB : Group.IsSolvable ↥(tailBorel r (minusTailForm K b c)) :=
    isSolvable_borel_orth_minus hirr r
  haveI hB0' : Group.IsSolvable ↥B0' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe tailBorel_le).toMonoidHom) (MulEquiv.injective _)
  haveI hB0 : Group.IsSolvable ↥B0 := by
    haveI : Group.IsSolvable ↥(B0.map Φ.toMonoidHom) := hmap ▸ hB0'
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective B0 Φ.toMonoidHom Φ.injective).toMonoidHom)
      (MulEquiv.injective _)
  have hq : Function.Injective (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact elemScalars_quadTail_eq_bot (by omega)
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective B0 (QuotientGroup.mk' (elemScalars (quadTail r qA))) hq).toMonoidHom)
    (MulEquiv.surjective _)

theorem isMulCommutative_minusProjectiveBorel_quotient {K : Type} [Field K] [Finite K]
    [CharP K 2] {r : ℕ} (hr : 3 ≤ r) {A : Type} [AddCommGroup A] [Module K A]
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : finrank K A = 1 ∨ finrank K A = 2) :
    IsMulCommutative
      (↥(((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
          (QuotientGroup.mk' (elemScalars (quadTail r qA)))) ⧸
        CFSG.pCore 2 ↥(((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
          (QuotientGroup.mk' (elemScalars (quadTail r qA))))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  haveI : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  haveI : Finite A := Module.finite_of_finite K
  have h2 : finrank K A = 2 := by
    obtain ⟨n, hn⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        qA hreg).1
    rcases hm with h | h <;> omega
  obtain ⟨b, c, hirr, ⟨e⟩⟩ := exists_isometry_minusTailForm hani hreg h2
  let ψ1 : (quadTail r qA).IsometryEquiv (quadMinus (r + 1) K b c) :=
    (tailProdIsometry e r).trans (minusTailIsometry (r + 1) K b c)
  let ψ2 : (quadTail r (minusTailForm K b c)).IsometryEquiv (quadMinus (r + 1) K b c) :=
    minusTailIsometry (r + 1) K b c
  have hQ : ⇑(quadMinus (r + 1) K b c) = StatedQuadMinus (r + 1) K b c :=
    coe_quadMinus (r + 1) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c)⁆ =
      elementaryGroup (quadMinus (r + 1) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  let Φ1 := tailOmegaEquiv ψ1 hQ hE
  let Φ2 := tailOmegaEquiv ψ2 hQ hE
  let F : Fin r → Submodule K (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2 → K) :=
    tailModelFlag r K (Fin 2)
  have hF2 : ∀ i, F i =
      (OrthogonalTail.stdFlag K (Fin 2 → K) r i).map ψ2.toLinearMap := by
    intro i
    simpa [F, OrthogonalTail.stdFlag] using tailModelFlag_eq_map ψ2 (fun _ => rfl) i
  have hψ1 : ψ1.toLinearMap = ψ2.toLinearMap.comp (tailProdIsometry e r).toLinearMap := rfl
  have hF1 : ∀ i, F i = (OrthogonalTail.stdFlag K A r i).map ψ1.toLinearMap := by
    intro i
    rw [hψ1, Submodule.map_comp]
    rw [congrFun (stdFlag_map_tailProdIsometry e r) i]
    exact hF2 i
  have hflag1 : (fun i => (F i).map ψ1.symm.toLinearMap) = OrthogonalTail.stdFlag K A r := by
    funext i
    rw [hF1 i, ← Submodule.map_comp]
    rw [show (ψ1.symm.toLinearMap.comp ψ1.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => ψ1.symm_apply_apply v, Submodule.map_id]
  have hflag2 : (fun i => (F i).map ψ2.symm.toLinearMap) =
      OrthogonalTail.stdFlag K (Fin 2 → K) r := by
    funext i
    rw [hF2 i, ← Submodule.map_comp]
    rw [show (ψ2.symm.toLinearMap.comp ψ2.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => ψ2.symm_apply_apply v, Submodule.map_id]
  let B0 : Subgroup (orthElementaryGroup (quadTail r qA)) :=
    (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))
  let B0' : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
    (tailBorel r (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail r (minusTailForm K b c)))
  have hB1 : (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
      Φ1.toMonoidHom = B0 := by
    rw [tailOmegaEquiv_flagStabilizer ψ1 hQ hE F, hflag1]
    exact tailBorel_subgroupOf_eq.symm
  have hB2 : (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
      Φ2.toMonoidHom = B0' := by
    rw [tailOmegaEquiv_flagStabilizer ψ2 hQ hE F, hflag2]
    exact tailBorel_subgroupOf_eq.symm
  let Φ : orthElementaryGroup (quadTail r qA) ≃*
      orthElementaryGroup (quadTail r (minusTailForm K b c)) := Φ1.symm.trans Φ2
  have hmap : B0.map Φ.toMonoidHom = B0' := by
    rw [show B0 = (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
        Φ1.toMonoidHom from hB1.symm]
    rw [Subgroup.map_map (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F)
      Φ.toMonoidHom Φ1.toMonoidHom]
    have hcomp : Φ.toMonoidHom.comp Φ1.toMonoidHom = Φ2.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      change Φ (Φ1 x) = Φ2 x
      rw [show Φ = Φ1.symm.trans Φ2 from rfl, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [hcomp, hB2]
  let q' : orthElementaryGroup (quadTail r (minusTailForm K b c)) →*
      (orthElementaryGroup (quadTail r (minusTailForm K b c)) ⧸
        elemScalars (quadTail r (minusTailForm K b c))) :=
    QuotientGroup.mk' (elemScalars (quadTail r (minusTailForm K b c)))
  let U0' : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
    (tailUnipotent r (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail r (minusTailForm K b c)))
  have hani' : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  have hUle : U0' ≤ B0' := fun x hx => tailUnipotent_le_tailBorel hani' hx
  have hUn : (U0'.subgroupOf B0').Normal := by
    have hUnB : ((tailUnipotent r (minusTailForm K b c)).subgroupOf
        (tailBorel r (minusTailForm K b c))).Normal := tailUnipotent_normal hani'
    let eB : ↥B0' ≃* ↥(tailBorel r (minusTailForm K b c)) :=
      Subgroup.subgroupOfEquivOfLe tailBorel_le
    have h := hUnB.comap eB.toMonoidHom
    rwa [show ((tailUnipotent r (minusTailForm K b c)).subgroupOf
        (tailBorel r (minusTailForm K b c))).comap eB.toMonoidHom =
        U0'.subgroupOf B0' from rfl] at h
  have hU2 : IsPGroup 2 (U0'.subgroupOf B0') := by
    have h := isPGroup_tailUnipotent (p := 2) hani' (r := r)
      (qA := minusTailForm K b c)
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe hUle).symm
  have hUlePc : U0'.subgroupOf B0' ≤ CFSG.pCore 2 ↥B0' :=
    le_sSup ⟨hUn, hU2⟩
  have hcomm : commutator ↥B0' ≤ CFSG.pCore 2 ↥B0' := by
    change ⁅(⊤ : Subgroup ↥B0'), ⊤⁆ ≤ CFSG.pCore 2 ↥B0'
    rw [Subgroup.commutator_le]
    intro x _ y _
    refine hUlePc (Subgroup.mem_subgroupOf.2 ?_)
    let z : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) :=
      (((⁅x, y⁆ : ↥B0').1 : orthElementaryGroup (quadTail r (minusTailForm K b c))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
    have hxy : z = ⁅(x : ↥B0').1.1, (y : ↥B0').1.1⁆ := by
      change ((Subgroup.subtype (orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) ((Subgroup.subtype B0') ⁅x, y⁆) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) = _
      rw [map_commutatorElement (Subgroup.subtype B0') x y]
      exact map_commutatorElement (Subgroup.subtype (orthElementaryGroup
        (quadTail r (minusTailForm K b c)))) x.1 y.1
    change z ∈ tailUnipotent r (minusTailForm K b c)
    rw [hxy]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus.commutator_mem_tailUnipotent
      hr hirr x.2 y.2
  have hcommPC : IsMulCommutative (↥B0' ⧸ CFSG.pCore 2 ↥B0') :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  haveI : Finite (orthElementaryGroup (quadTail r (minusTailForm K b c))) := Subtype.finite
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := inferInstance
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) => (g : _ → _)) DFunLike.coe_injective
  have hq' : Function.Injective q' := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact elemScalars_quadTail_eq_bot (by omega)
  let f : ↥B0' →* ↥(B0'.map q') :=
    MonoidHom.codRestrict (q'.comp B0'.subtype) (B0'.map q')
      (fun x => Subgroup.mem_map_of_mem q' x.2)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcommBbar : IsMulCommutative
      (↥(B0'.map q') ⧸ CFSG.pCore 2 ↥(B0'.map q')) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective f hf hcommPC
  have hq : Function.Injective (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact elemScalars_quadTail_eq_bot (by omega)
  let q0 : orthElementaryGroup (quadTail r qA) →*
      (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)) :=
    QuotientGroup.mk' (elemScalars (quadTail r qA))
  let eZ : ↥(B0.map q0) ≃* ↥B0 := (Subgroup.equivMapOfInjective B0 q0 hq).symm
  let e0 : ↥B0 ≃* ↥B0' :=
    (Subgroup.equivMapOfInjective B0 Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  let eZ' : ↥B0' ≃* ↥(B0'.map q') := Subgroup.equivMapOfInjective B0' q' hq'
  let eBar : ↥(B0.map q0) ≃* ↥(B0'.map q') := eZ.trans (e0.trans eZ')
  let eQ : (↥(B0.map q0) ⧸ CFSG.pCore 2 ↥(B0.map q0)) ≃*
      (↥(B0'.map q') ⧸ CFSG.pCore 2 ↥(B0'.map q')) :=
    QuotientGroup.congr _ _ eBar (CFSG.pCore_map_iso 2 eBar)
  exact Function.Surjective.isMulCommutative eQ.symm.surjective hcommBbar

theorem three_le_pRank_diagTorus_orthogonal_minus_gen {K : Type} [Field K] [Finite K]
    [CharP K 2] {m : ℕ} (hm : 4 ≤ m) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card K - 1) (b c : K) :
    3 ≤ CFSG.Open.pRank q ((diagTorusMinus m K).subgroupOf
      (StatedOmega (StatedQuadMinus m K b c))) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hqne : q ≠ 2 := by
    rintro rfl
    letI : Fintype K := Fintype.ofFinite K
    have heven : Even (Nat.card K) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr
        (FiniteField.even_card_iff_char_two.mp (ringChar.eq K 2))
    have hodd : Odd (Nat.card K - 1) := by
      obtain ⟨k, hk⟩ := heven
      have hpos : 0 < Nat.card K := Nat.card_pos
      refine ⟨k - 1, ?_⟩
      omega
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hoddq : Odd q := hq.odd_of_ne_two hqne
  have hdvd' : q ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  obtain ⟨T, hTle, -, -, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving (F := K)
      (X := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)
      (G := StatedOmega (StatedQuadMinus m K b c))
      (H := (diagTorusMinus m K).subgroupOf (StatedOmega (StatedQuadMinus m K b c)))
      (ι := Fin 3) (r := q) hq
      (fun i : Fin 3 => diagGenMinus b c t hm i hoddq ht)
      (fun i : Fin 3 => Pi.single (Sum.inl (threeToFinMinus hm i)) 1)
      (omegaActMinus m K b c)
      (fun i => by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨Pi.mulSingle (threeToFinMinus hm i) t, rfl⟩)
      (fun i => orderOf_diagGenMinus _ _ t hm i hoddq ht)
      (fun i j => commute_diagGenMinus _ _ t hm i j hoddq ht)
      (fun i a h => dvd_of_diagGenMinus_zpow_fixes _ _ t hm i hoddq ht h)
      (fun i j hij => omegaAct_diagGenMinus_single_of_ne _ _ t hm hij hoddq ht)
  have hcard : Nat.card (Fin 3) = 3 := by simp
  rw [hcard] at hTrank
  exact hTrank.trans (CFSG.SectionRank.pRank_mono hq.one_lt hTle)

end CFSG.ClassicalGroups.Orthogonal

end
