module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescent

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem F_mem_quadGens
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β) {g : adjointGroup τ k}
    (hg : g ∈ quadGens D) : D.F g ∈ quadGens D ∧ D.F (D.F g) = g := by
  obtain ⟨β, hβ, c, hc, hgc⟩ := hg
  have hker := D.mem_kernelRoots_of_mem_simpleRootsJ hβ
  obtain ⟨h1, h2, -⟩ := D.thetaPowVec_spec hker 1
  rw [pow_one] at h1
  set β' := thetaPowVec D.θ 1 β with hβ'
  have hβ'J : β' ∈ D.simpleRootsJ := D.thetaOrbit_subset_simpleRootsJ hβ h2
  have hc' : c ^ p ^ D.e ∈ frobeniusFixedField k p (D.e * 2) := by
    rw [mem_frobeniusFixedField] at hc ⊢
    rw [← pow_mul, mul_comm, pow_mul, hc]
  have hcc : (c ^ p ^ D.e) ^ p ^ D.e = c := by
    rw [mem_frobeniusFixedField] at hc
    rw [← pow_mul, ← pow_add, ← two_mul, mul_comm, hc]
  have hFr : ∀ z : k, iterateFrobenius k p D.e z = z ^ p ^ D.e := fun z => iterateFrobenius_def ..
  rcases hgc with hgc | hgc
  · have hF := D.map_rootSL2 β hβ.1 β' h1.symm (uSL c) g hgc
    rw [LieType.Chevalley.map_uSL, hFr] at hF
    refine ⟨⟨β', hβ'J, _, hc', Or.inl hF⟩, Subtype.ext ?_⟩
    have hF2 := D.map_rootSL2 β' hβ'J.1 β (by rw [h1, hθ2 β hβ]) (uSL (c ^ p ^ D.e)) _ hF
    rw [hF2, LieType.Chevalley.map_uSL, hFr, hcc, hgc]
  · have hF := D.map_rootSL2 β hβ.1 β' h1.symm (vSL c) g hgc
    rw [LieType.Chevalley.map_vSL, hFr] at hF
    refine ⟨⟨β', hβ'J, _, hc', Or.inr hF⟩, Subtype.ext ?_⟩
    have hF2 := D.map_rootSL2 β' hβ'J.1 β (by rw [h1, hθ2 β hβ]) (vSL (c ^ p ^ D.e)) _ hF
    rw [hF2, LieType.Chevalley.map_vSL, hFr, hcc, hgc]

theorem F_mem_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β) {y : adjointGroup τ k}
    (hy : y ∈ quadGroup D) : D.F y ∈ quadGroup D ∧ D.F (D.F y) = y := by
  have h1 : (quadGroup D).map D.F.toMonoidHom ≤ quadGroup D := by
    rw [quadGroup, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨g, hg, rfl⟩
    exact (F_mem_quadGens D hθ2 hg).1
  have h2 : quadGroup D ≤ (D.F.toMonoidHom.comp D.F.toMonoidHom).eqLocus (MonoidHom.id _) :=
    (Subgroup.closure_le _).2 fun g hg => (F_mem_quadGens D hθ2 hg).2
  exact ⟨h1 ⟨y, hy, rfl⟩, h2 hy⟩

@[expose] def quadAut
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β) : MulAut (quadGroup D) where
  toFun y := ⟨D.F y.1, (F_mem_quadGroup D hθ2 y.2).1⟩
  invFun y := ⟨D.F y.1, (F_mem_quadGroup D hθ2 y.2).1⟩
  left_inv y := Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  right_inv y := Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  map_mul' x y := Subtype.ext (map_mul D.F x.1 y.1)

theorem quadGroup_le_rootSpanJ
    (D : OrthogonalSemilinearFixedRootDatum τ p k) :
    quadGroup D ≤ D.rootSpanJ.subgroupOf (adjointGroup τ k) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨β, hβ, c, -, hg⟩
  have hβr : β ∈ D.roots := hβ.2
  have key : ∀ A : SL2 k, rootSL2 τ k β A ∈ D.rootSpanJ := fun A => by
    have hmem : rootSL2 τ k β A ∈ (rootSL2 τ k β).range := ⟨A, rfl⟩
    rw [range_rootSL2_of_isRoot (D.mem_kernelRoots_of_mem_simpleRootsJ hβ).1] at hmem
    refine (sup_le ?_ ?_ : _ ≤ D.rootSpanJ) hmem
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ unionRoots D.χ D.J) => rootSubgroup τ k α) β
        hβr le_rfl
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ unionRoots D.χ D.J) => rootSubgroup τ k α) (-β)
        (neg_mem_unionRoots hβr) le_rfl
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  rcases hg with hg | hg <;> rw [hg] <;> exact key _

theorem finite_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k) : Finite (quadGroup D) := by
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have : Finite (ModGL τ (frobeniusFixedField k p (D.e * 2))) := finite_modGL
  have h2 : Finite ((pairSpan τ (frobeniusFixedField k p (D.e * 2)) D.simpleRootsJ).map
      (baseChangeGL (frobeniusFixedField k p (D.e * 2)).subtype)) :=
    Finite.of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  rw [← map_subtype_quadGroup] at h2
  exact Finite.of_equiv _ ((quadGroup D).equivMapOfInjective _
    (adjointGroup τ k).subtype_injective).symm.toEquiv

theorem oddLieCentralQuotient_orbitGroup_of_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2)
    (hnc : ∃ y ∈ quadGens D, ∃ x ∈ quadGens D, ¬ Commute (D.F y * y⁻¹) x)
    (hq : IsQuasisimple D.orbitGroup)
    (hfam : ∀ α : MulAut (↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)), orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L) :
    OddLieCentralQuotient p D.orbitGroup := by
  have := finite_quadGroup D
  let Y := quadGroup D
  let σ := quadAut D hθ2
  have hσσ : ∀ y, σ (σ y) = y := fun y => Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  let π := QuotientGroup.mk' (Subgroup.center Y)
  let σ' : MulAut (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ (Subgroup.map_center_eq σ)
  have hcomm : ∀ y, π (σ y) = σ' (π y) := fun y => rfl
  have hσ'2 : σ' ^ 2 = 1 := by
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) z
    rw [sq, MulAut.mul_apply, ← hcomm, ← hcomm, hσσ]
    rfl
  have hσ'1 : σ' ≠ 1 := by
    obtain ⟨y, hy, x, hx, hyx⟩ := hnc
    intro h
    have hyY : y ∈ Y := Subgroup.subset_closure hy
    have hxY : x ∈ Y := Subgroup.subset_closure hx
    have h1 : π (σ ⟨y, hyY⟩) = π ⟨y, hyY⟩ := by rw [hcomm, h]; rfl
    have hz : (σ ⟨y, hyY⟩)⁻¹ * ⟨y, hyY⟩ ∈ Subgroup.center Y := QuotientGroup.eq.1 h1
    have hzc := Subgroup.mem_center_iff.1 (inv_mem hz)
    have he : σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹ = ((σ ⟨y, hyY⟩)⁻¹ * ⟨y, hyY⟩)⁻¹ := by
      have h2 := hzc (σ ⟨y, hyY⟩)
      rw [mul_inv_rev, inv_inv] at h2 ⊢
      calc σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹ =
          σ ⟨y, hyY⟩ * ((⟨y, hyY⟩ : Y)⁻¹ * σ ⟨y, hyY⟩) * (σ ⟨y, hyY⟩)⁻¹ := by group
        _ = (⟨y, hyY⟩ : Y)⁻¹ * σ ⟨y, hyY⟩ := by rw [h2]; group
    apply hyx
    have hc : Commute (σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹) ⟨x, hxY⟩ := by
      rw [he]
      exact (hzc ⟨x, hxY⟩).symm
    exact hc.map Y.subtype
  have hord : orderOf σ' = 2 := orderOf_eq_prime hσ'2 hσ'1
  have hCY : D.orbitGroupC ≤ Y := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := orbitGroup_le_map_quadGroup D hcard (Subgroup.mem_subgroupOf.1 hx)
    rwa [← Subtype.ext hyx]
  let C₁ : Subgroup Y := D.orbitGroupC.subgroupOf Y
  let eC : C₁ ≃* D.orbitGroup := (Subgroup.subgroupOfEquivOfLe hCY).trans
    (Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup)
  have hq₁ : IsQuasisimple C₁ := LocalCores.isQuasisimple_of_mulEquiv eC.symm hq
  have hC₁fix : C₁ ≤ fixedSubgroup σ := fun c hc =>
    Subtype.ext (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup hc)).2
  have hYfix : ∀ g : Y, σ g = g → (g : adjointGroup τ k) ∈ D.fixedGroup := fun g hg =>
    D.mem_fixedGroup.2 ⟨Subgroup.mem_subgroupOf.1 (quadGroup_le_rootSpanJ D g.2),
      congrArg Subtype.val hg⟩
  have hN : (C₁.subgroupOf (fixedSubgroup σ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnor := D.orbitGroupC_normal
    have hn' : (⟨(n : Y), hYfix _ n.2⟩ : D.fixedGroup) ∈ D.orbitGroupC.subgroupOf D.fixedGroup :=
      Subgroup.mem_subgroupOf.2 hn
    have := hnor.conj_mem _ hn' ⟨((g : Y) : adjointGroup τ k), hYfix _ g.2⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hC₁comp : Assembly.IsComponentOf C₁ (fixedSubgroup σ) :=
    ⟨hC₁fix, Assembly.IsSubnormal.step hC₁fix hN (Assembly.IsSubnormal.refl _),
      (AssemblyBPredicates.isQuasisimple_iff_native C₁).2 hq₁⟩
  have hmap := LocalAnalysis.ComponentInitial.isComponentOf_map_fixed (π := π)
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hσσ hcomm hC₁comp
  have hK := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hmap.1).1 hmap
  obtain ⟨τ', n', f', hadm, hlie⟩ := oddLieCentralQuotient_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hmap.1).symm (hfam σ' hord _ hK)
  have hker : (π.subgroupMap C₁).ker ≤ Subgroup.center C₁ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_center_iff.2 fun w =>
      Subtype.ext (Subgroup.mem_center_iff.1 hx1 (w : Y))
  obtain ⟨e₂⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq₁
    (π.subgroupMap C₁) (π.subgroupMap_surjective C₁) hker
  exact oddLieCentralQuotient_of_mulEquiv eC.symm
    ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv e₂.symm hlie⟩

end CFSG.ComponentClassification.CatLeafProof
