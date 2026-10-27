module

public import CFSG.Mathlib.LinearAlgebra.PositiveWeightTwist
public import CFSG.LieType.AlgebraicGroups.QuotientConjugation
public import CFSG.LieType.AlgebraicGroups.TwistedBorelDifferential
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv

universe u v
variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]

theorem pointConjugation_mem_hopfIdeal
    (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k))
    {a : H} (ha : a ∈ I) : TauCeti.HopfAlgebra.pointConjugationAlgHom g a ∈ I := by
  let A := H ⧸ I.toIdeal
  let π : H →ₐ[k] A := Ideal.Quotient.mkₐ k I.toIdeal
  let P := CommHopfAlgCat.quotientPointsSubgroup
    (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k A)
  let q := toConv π
  let cg := AlgHom.mapValue (H := H) (Algebra.ofId k A) g
  have hcg : cg ∈ P := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    change (AlgHom.mapValue (H := H) (Algebra.ofId k A) g).ofConv x = 0
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    rw [(CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hg x hx, map_zero]
  have hq : q ∈ P := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    change Ideal.Quotient.mk I.toIdeal x = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hc : toConv (π.comp (TauCeti.HopfAlgebra.pointConjugationAlgHom g)) ∈ P := by
    rw [TauCeti.HopfAlgebra.comp_pointConjugationAlgHom]
    exact P.mul_mem (P.mul_mem hcg hq) (P.inv_mem hcg)
  have hz := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hc a ha
  change Ideal.Quotient.mk I.toIdeal (TauCeti.HopfAlgebra.pointConjugationAlgHom g a) = 0 at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

theorem pointConjugation_preserves_lieSubalgebra
    (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k)) :
    (I.lieSubalgebra (B := k)).toSubmodule ≤
      (I.lieSubalgebra (B := k)).toSubmodule.comap
        (derivationCompLieHom (B := k)
          (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom).toLinearMap := by
  intro d hd
  change (derivationCompLieHom (B := k)
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom).toLinearMap d ∈
      I.lieSubalgebra (B := k)
  rw [LieHom.coe_toLinearMap, derivationCompLieHom_apply]
  exact derivationComp_mem_lieSubalgebra_of_stable
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom I
    (by
      intro a ha
      have hp := pointConjugation_mem_hopfIdeal I g hg ha
      rwa [← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom] at hp) d hd

@[expose] def quotientCocharacterPoints (I : HopfIdeal k H)
    (γ : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k) :
    kˣ →* WithConv (H →ₐ[k] k) :=
  (AlgHom.mapDomain (A := k) (_root_.Bialgebra.Quotient.mkBialgHom I.toIdeal)).comp
    ((AlgHom.mapDomain (A := k) γ).comp
      (TauCeti.MultiplicativeGroup.pointsMulEquiv (R := k) (A := k)).symm.toMonoidHom)

theorem quotientCocharacterPoints_mem (I : HopfIdeal k H)
    (γ : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k)
    (s : kˣ) : quotientCocharacterPoints I γ s ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro a ha
  simp only [quotientCocharacterPoints, MonoidHom.comp_apply,
    AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
  rw [_root_.Bialgebra.Quotient.mkBialgHom_toAlgHom]
  have hzero : (Ideal.Quotient.mkₐ k I.toIdeal) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hzero, map_zero, map_zero]

@[expose] def quotientCocharacterLieEnd (I : HopfIdeal k H)
    (γ : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k)
    (s : kˣ) : Module.End k
      (Derivation k H (Bialgebra.CounitAlgebra k H k) ⧸ (I.lieSubalgebra (B := k)).toSubmodule) :=
  (I.lieSubalgebra (B := k)).toSubmodule.mapQ (I.lieSubalgebra (B := k)).toSubmodule
    (derivationCompLieHom (B := k) (TauCeti.HopfAlgebra.pointConjugationBialgEquiv
      (quotientCocharacterPoints I γ s)).toBialgHom).toLinearMap
    (pointConjugation_preserves_lieSubalgebra I _ (quotientCocharacterPoints_mem I γ s))

structure PositiveLieQuotientCocharacter {k : Type u} [Field k]
    {H : Type v} [CommRing H] [HopfAlgebra k H] (I : HopfIdeal k H) where
  cocharacter : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k
  rank : ℕ
  basis : Module.Basis (Fin rank) k
    (Derivation k H (Bialgebra.CounitAlgebra k H k) ⧸ (I.lieSubalgebra (B := k)).toSubmodule)
  weight : Fin rank → ℕ
  weight_pos : ∀ i, 0 < weight i
  acts_on_basis : ∀ (s : kˣ) (i : Fin rank),
    quotientCocharacterLieEnd I cocharacter s (basis i) = ((s : k) ^ weight i) • basis i

theorem exists_quotientPoint_range_twistDifferential_eq_top_of_positiveCocharacter
    {k : Type u} [Field k] [Infinite k]
    {H : Type v} [CommRing H] [HopfAlgebra k H]
    (I : HopfIdeal k H) (τ : H →ₐc[k] H) (hτ : ∀ a ∈ I, τ a ∈ I)
    (P : PositiveLieQuotientCocharacter I) :
    ∃ b : WithConv (H →ₐ[k] k),
      b ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k k) ∧
      LinearMap.range (LinearMap.id - (derivationCompLieHom (B := k)
        (τ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv b).toBialgHom)).toLinearMap) ⊔
          (I.lieSubalgebra (B := k)).toSubmodule = ⊤ := by
  let N := (I.lieSubalgebra (B := k)).toSubmodule
  let F := (derivationCompLieHom (B := k) τ).toLinearMap
  let D (s : kˣ) := (derivationCompLieHom (B := k)
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv
      (quotientCocharacterPoints I P.cocharacter s)).toBialgHom).toLinearMap
  have hD (s : kˣ) : N ≤ N.comap (D s) :=
    pointConjugation_preserves_lieSubalgebra I _
      (quotientCocharacterPoints_mem I P.cocharacter s)
  have hF : N ≤ N.comap F := by
    intro d hd
    change (derivationCompLieHom (B := k) τ).toLinearMap d ∈ I.lieSubalgebra (B := k)
    rw [LieHom.coe_toLinearMap, derivationCompLieHom_apply]
    exact derivationComp_mem_lieSubalgebra_of_stable τ I hτ d hd
  have hweights : ∀ (s : kˣ) (i : Fin P.rank),
      N.mapQ N (D s) (hD s) (P.basis i) = ((s : k) ^ P.weight i) • P.basis i :=
    P.acts_on_basis
  obtain ⟨s, hs⟩ := CFSG.LinearAlgebra.exists_range_one_sub_comp_sup_eq_top_of_positive_quotient_weights
    N P.basis P.weight P.weight_pos D hD hweights F hF
  refine ⟨quotientCocharacterPoints I P.cocharacter s,
    quotientCocharacterPoints_mem I P.cocharacter s, ?_⟩
  have heq : (derivationCompLieHom (B := k)
      (τ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv
        (quotientCocharacterPoints I P.cocharacter s)).toBialgHom)).toLinearMap = (D s).comp F := by
    apply LinearMap.ext
    intro d
    simpa only [D, F, LieHom.coe_toLinearMap, derivationCompLieHom_apply,
      LinearMap.comp_apply] using DFunLike.congr_fun (derivationComp_comp (B := k) τ
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv
        (quotientCocharacterPoints I P.cocharacter s)).toBialgHom) d
  rw [heq]
  exact hs

end CFSG.LieType.AlgebraicGroups

namespace CFSG.LieType.AlgebraicGroups.QuotientConjugation

open TauCeti WithConv

universe u v
variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]

theorem quotientCocharacterPoints_comp_coordinateEquiv (I : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) (γ : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k)
    (s : kˣ) :
    quotientCocharacterPoints (I.conjugate g)
        (γ.comp (coordinateEquiv I g).toBialgHom) s =
      AlgHom.mapDomain (A := k)
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
        (quotientCocharacterPoints I γ s) := by
  apply WithConv.ext
  ext a
  simp only [quotientCocharacterPoints, MonoidHom.comp_apply, AlgHom.mapDomain_apply,
    ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom, BialgHom.comp_apply]
  congr 2
  exact DFunLike.congr_fun (coordinateEquiv_comp_mk I g) a

theorem quotientCocharacterPoints_conjugate (I : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) (γ : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k)
    (s : kˣ) :
    quotientCocharacterPoints (I.conjugate g)
        (γ.comp (coordinateEquiv I g).toBialgHom) s =
      g * quotientCocharacterPoints I γ s * g⁻¹ := by
  rw [quotientCocharacterPoints_comp_coordinateEquiv,
    TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv]
  have hself (x : WithConv (H →ₐ[k] k)) :
      AlgHom.mapValue (H := H) (Algebra.ofId k k) x = x := by
    apply WithConv.ext
    ext a
    simp
  rw [hself]

theorem quotientCocharacterLieEnd_conjugate (I : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) (γ : (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k)
    (s : kˣ)
    (x : Derivation k H (Bialgebra.CounitAlgebra k H k) ⧸
      (I.lieSubalgebra (B := k)).toSubmodule) :
    quotientCocharacterLieEnd (I.conjugate g)
        (γ.comp (coordinateEquiv I g).toBialgHom) s (lieQuotientEquiv I g x) =
      lieQuotientEquiv I g (quotientCocharacterLieEnd I γ s x) := by
  refine Submodule.Quotient.induction_on _ x fun d => ?_
  rw [lieQuotientEquiv_mk]
  simp only [quotientCocharacterLieEnd, Submodule.mapQ_apply,
    lieQuotientEquiv_mk, LieHom.coe_toLinearMap, derivationCompLieHom_apply,
    quotientCocharacterPoints_conjugate]
  exact congrArg Submodule.Quotient.mk
    (lieLinearEquiv_derivationComp_pointConjugation g (quotientCocharacterPoints I γ s) d).symm

end CFSG.LieType.AlgebraicGroups.QuotientConjugation

namespace CFSG.LieType.AlgebraicGroups.PositiveLieQuotientCocharacter

open TauCeti WithConv

universe u v
variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {I : HopfIdeal k H}

@[expose] def conjugate (P : PositiveLieQuotientCocharacter I)
    (g : WithConv (H →ₐ[k] k)) : PositiveLieQuotientCocharacter (I.conjugate g) where
  cocharacter := P.cocharacter.comp (QuotientConjugation.coordinateEquiv I g).toBialgHom
  rank := P.rank
  basis := P.basis.map (QuotientConjugation.lieQuotientEquiv I g)
  weight := P.weight
  weight_pos := P.weight_pos
  acts_on_basis s i := by
    simp only [Module.Basis.map_apply, QuotientConjugation.quotientCocharacterLieEnd_conjugate,
      P.acts_on_basis, map_smul]

@[simp] theorem conjugate_cocharacter_apply (P : PositiveLieQuotientCocharacter I)
    (g : WithConv (H →ₐ[k] k)) (a : H ⧸ (I.conjugate g).toIdeal) :
    (P.conjugate g).cocharacter a = P.cocharacter (QuotientConjugation.coordinateEquiv I g a) := rfl

@[simp] theorem conjugate_rank (P : PositiveLieQuotientCocharacter I)
    (g : WithConv (H →ₐ[k] k)) : (P.conjugate g).rank = P.rank := rfl

@[simp] theorem conjugate_weight (P : PositiveLieQuotientCocharacter I)
    (g : WithConv (H →ₐ[k] k)) : (P.conjugate g).weight = P.weight := rfl

@[simp] theorem conjugate_basis (P : PositiveLieQuotientCocharacter I)
    (g : WithConv (H →ₐ[k] k)) :
    (P.conjugate g).basis = P.basis.map (QuotientConjugation.lieQuotientEquiv I g) := rfl

end CFSG.LieType.AlgebraicGroups.PositiveLieQuotientCocharacter
