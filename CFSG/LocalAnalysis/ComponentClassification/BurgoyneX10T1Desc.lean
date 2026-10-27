module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Forms
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Root
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Kernel
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Pred
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescentMain
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

section Descent

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

@[expose] def quadAutBar
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β) :
    MulAut (↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) :=
  QuotientGroup.congr (Subgroup.center (quadGroup D)) (Subgroup.center (quadGroup D))
    (quadAut D hθ2) (Subgroup.map_center_eq (quadAut D hθ2))

theorem quadAutBar_mk
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β) (y : quadGroup D) :
    quadAutBar D hθ2 (y : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) =
      ((quadAut D hθ2 y : quadGroup D) : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) :=
  rfl

theorem quadAutBar_sq
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β) :
    quadAutBar D hθ2 ^ 2 = 1 := by
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [sq, MulAut.mul_apply, quadAutBar_mk, quadAutBar_mk,
    show quadAut D hθ2 (quadAut D hθ2 y) = y from Subtype.ext (F_mem_quadGroup D hθ2 y.2).2]
  rfl

theorem CompPred.orbitGroup_of_quadGroup_at
    (P : CompPred) (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2)
    (hq : IsQuasisimple D.orbitGroup)
    (hfam : ∀ L : Subgroup (fixedSubgroup (quadAutBar D hθ2)), IsComponent L → P.P p L) :
    P.P p D.orbitGroup := by
  have := finite_quadGroup D
  let Y := quadGroup D
  let σ := quadAut D hθ2
  have hσσ : ∀ y, σ (σ y) = y := fun y => Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  let π := QuotientGroup.mk' (Subgroup.center Y)
  let σ' : MulAut (Y ⧸ Subgroup.center Y) := quadAutBar D hθ2
  have hcomm : ∀ y, π (σ y) = σ' (π y) := fun y => rfl
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
  have hPK : P.P p ↥(C₁.map π) :=
    P.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hmap.1).symm (hfam _ hK)
  have hker : (π.subgroupMap C₁).ker ≤ Subgroup.center C₁ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_center_iff.2 fun w =>
      Subtype.ext (Subgroup.mem_center_iff.1 hx1 (w : Y))
  exact P.of_mulEquiv eC.symm (P.of_central hq₁ (π.subgroupMap C₁) (π.subgroupMap_surjective C₁)
    hker hPK)

end Descent

section Root

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem right_ne_one_of_root_action [Finite K] (hd : 0 < d) {N : Matrix (Fin d) (Fin d) K}
    (hN2 : N * N = 0) (hN : N ≠ 0) (r : K → matrixDerived Q)
    (hr : ∀ c, (((r c : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N)
    (g : similarityPairs Q) (w : K → matrixProjectiveDerived Q) (φ₀ : K → K)
    (hinto : ∀ c, ∃ c', w c = matrixProjectiveProjection Q (r c'))
    (honto : ∀ c', ∃ c, w c = matrixProjectiveProjection Q (r c'))
    (hact : ∀ c, matrixProjectiveConjugationHom Q g (w c) = w (φ₀ c))
    (h1 : Nat.card {c : K // φ₀ c = c} ≠ 1) (hK : Nat.card {c : K // φ₀ c = c} ≠ Nat.card K) :
    g.val.right ≠ 1 := by
  intro hτ
  choose φ hφ using hinto
  have hφs : Function.Surjective φ := fun c' => by
    obtain ⟨c, hc⟩ := honto c'
    exact ⟨c, rootClass_injective hd hN2 hN r hr (by rw [← hφ c, hc])⟩
  have hφi : Function.Injective φ := Finite.injective_iff_surjective.mpr hφs
  have hnorm : ∀ c, ∃ c', matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
      matrixProjectiveProjection Q (r c') := by
    intro c'
    obtain ⟨c, rfl⟩ := hφs c'
    exact ⟨φ (φ₀ c), by rw [← hφ c, hact, hφ]⟩
  have hfix : ∀ c, matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r (φ c))) =
      matrixProjectiveProjection Q (r (φ c)) ↔ φ₀ c = c := by
    intro c
    rw [← hφ c, hact, hφ, hφ]
    constructor
    · exact fun h => hφi (rootClass_injective hd hN2 hN r hr h)
    · intro h
      rw [h]
  have hcard : Nat.card {c : K // matrixProjectiveConjugationHom Q g
      (matrixProjectiveProjection Q (r c)) = matrixProjectiveProjection Q (r c)} =
      Nat.card {c : K // φ₀ c = c} :=
    Nat.card_congr ((Equiv.ofBijective φ ⟨hφi, hφs⟩).subtypeEquiv fun c => (hfix c).symm).symm
  rcases card_fixed_root_of_linear hd hN2 hN r hr g hτ hnorm with h | h
  · exact h1 (hcard ▸ h)
  · exact hK (hcard ▸ h)

end Root

section Frobenius

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem card_pow_fixed_frobeniusFixedField {e : ℕ} (he : 1 ≤ e) :
    Nat.card {c : frobeniusFixedField k p (e * 2) // c ^ p ^ e = c} = p ^ e := by
  refine (Nat.card_congr ?_).trans (card_frobeniusFixedField (k := k) (p := p) (by omega : 0 < e))
  exact
    { toFun := fun c => ⟨(c.1 : k), mem_frobeniusFixedField.2 (by
        have h := congrArg (fun z : frobeniusFixedField k p (e * 2) => (z : k)) c.2
        simpa using h)⟩
      invFun := fun z => ⟨⟨(z : k), mem_frobeniusFixedField.2 (by
        have h := mem_frobeniusFixedField.1 z.2
        rw [mul_two, pow_add, pow_mul, h, h])⟩, Subtype.ext (by
        have h := mem_frobeniusFixedField.1 z.2
        simpa using h)⟩
      left_inv := fun c => rfl
      right_inv := fun z => rfl }

end Frobenius

section Split

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_quadGroup_equiv_pairSpan
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {S : Set (Fin τ.rank → ℤ)}
    (hJS : D.simpleRootsJ = S) :
    ∃ eY : quadGroup D ≃* pairSpan τ (frobeniusFixedField k p (D.e * 2)) S,
      ∀ y, baseChangeGL (frobeniusFixedField k p (D.e * 2)).subtype
        ((eY y : pairSpan τ (frobeniusFixedField k p (D.e * 2)) S) :
          ModGL τ (frobeniusFixedField k p (D.e * 2))) =
        ((y : adjointGroup τ k) : ModGL τ k) := by
  set e₂ := (pairSpan τ (frobeniusFixedField k p (D.e * 2)) D.simpleRootsJ).equivMapOfInjective _
    (baseChangeGL_injective (frobeniusFixedField k p (D.e * 2)).subtype) with he₂
  refine ⟨(((quadGroup D).equivMapOfInjective _ (adjointGroup τ k).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_quadGroup D))).trans
      (e₂.symm.trans (MulEquiv.subgroupCongr (congrArg (pairSpan τ _) hJS))), fun y => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply]
  set z := MulEquiv.subgroupCongr (map_subtype_quadGroup D)
    ((quadGroup D).equivMapOfInjective _ (adjointGroup τ k).subtype_injective y) with hz
  have hz' : (z : ModGL τ k) = ((y : adjointGroup τ k) : ModGL τ k) := by
    rw [hz, MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have h := congrArg Subtype.val (e₂.apply_symm_apply z)
  rw [he₂, Subgroup.coe_equivMapOfInjective_apply] at h
  rw [h, hz']

end Split

theorem thetaMap_e6_alpha4 :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm (Pi.single (e6Node 3) 1) =
      Pi.single (e6Node 3) 1 := by
  rw [thetaMap_e6_nil_apply]
  funext j
  change (Pi.single (e6Node 3) 1 : Fin (Tag.rank .E6) → ℤ) (TwistTag.E6.perm.symm j) =
    (Pi.single (e6Node 3) 1 : Fin (Tag.rank .E6) → ℤ) j
  have h : ∀ i : Fin 6, (Pi.single 3 1 : Fin 6 → ℤ)
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i) = (Pi.single 3 1 : Fin 6 → ℤ) i := by
    decide
  exact h j

theorem excCompModel_of_root_fixed {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 5 K))) (hα2 : α ^ 2 = 1)
    {N : Matrix (Fin (2 * 5)) (Fin (2 * 5)) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    (r : K → matrixDerived (coordinateQuadPlus 5 K))
    (hr : ∀ c, (((r c : matrixDerived (coordinateQuadPlus 5 K)) : GL (Fin (2 * 5)) K) :
      Matrix (Fin (2 * 5)) (Fin (2 * 5)) K) = 1 + c • N)
    (w : K → matrixProjectiveDerived (coordinateQuadPlus 5 K)) (φ₀ : K → K)
    (hinto : ∀ c, ∃ c', w c = matrixProjectiveProjection _ (r c'))
    (honto : ∀ c', ∃ c, w c = matrixProjectiveProjection _ (r c'))
    (hact : ∀ c, α (w c) = w (φ₀ c))
    (h1 : Nat.card {c : K // φ₀ c = c} ≠ 1) (hKc : Nat.card {c : K // φ₀ c = c} ≠ Nat.card K)
    (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) : ExcCompModel p L := by
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 5 K))) .POmegaPlus
      5 p f := ⟨⟨hp, hf, by norm_num⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  have hmem : α ∈ matrixProjectiveImage (coordinateQuadPlus 5 K) := by
    rw [RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K 5 le_rfl]
    exact Subgroup.mem_top α
  obtain ⟨g, rfl⟩ := hmem
  have hgg : matrixProjectiveConjugationHom _ (g * g) = 1 := by rw [map_mul, ← sq, hα2]
  obtain ⟨hσ2', c, hc⟩ :=
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP
      (g * g)).mp hgg
  have hσ2 : g.val.right ^ 2 = 1 := by
    rw [← (CatalogueBOrthogonalInvolutionRepresentation.sq_val _ g).2]
    exact hσ2'
  have hc' : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin (2 * 5)) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin (2 * 5)) c := by
    rw [← (CatalogueBOrthogonalInvolutionRepresentation.sq_val _ g).1, hc]
  have hσ : g.val.right ≠ 1 :=
    right_ne_one_of_root_action (by norm_num) hN2 hN r hr g w φ₀ hinto honto hact h1 hKc
  exact excCompModel_omega_field_ten hp hp2 hf hK rfl hnd g hσ2 hσ c hc' hL

end CFSG.ComponentClassification.Burgoyne.X10
