module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.RegularLemmaR
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.Spectrum

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.SignalizerFunctorTheorem.NonLocalExc

section Central


variable {K : Type} [Field K]

theorem coe_twistedEntrywiseAut_one_D4 (σ : K ≃+* K) (u : adjointGroup Tag.D4 K) :
    (Subtype.val (twistedEntrywiseAut TwistTag.D4 1 σ u) : ModGL Tag.D4 K) =
      d4P K * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) * (d4P K)⁻¹ := by
  have h := coe_twistedEntrywiseAut TwistTag.D4 (1 : ℤ) σ u
  rw [zpow_one] at h
  exact h

theorem twistedEntrywiseAut_one_adjX (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    twistedEntrywiseAut TwistTag.D4 1 σ (adjX Tag.D4 K i c) = adjX Tag.D4 K (d4Rho i) (σ c) := by
  refine Subtype.ext ?_
  have h1 := coe_twistedEntrywiseAut_one_D4 σ (adjX Tag.D4 K i c)
  have h2 := diagramMap_pow_mul_xUnit_mul_inv TwistTag.D4 K 1 i (σ c)
  simp only [pow_one] at h2
  have h3 : Units.map (entrywiseHom σ.toRingHom) (xUnit Tag.D4 K i c) =
      xUnit Tag.D4 K i (σ c) := units_map_entrywiseHom_xUnit σ.toRingHom i c
  refine h1.trans ?_
  show d4P K * Units.map (entrywiseHom σ.toRingHom) (xUnit Tag.D4 K i c) * (d4P K)⁻¹ =
    xUnit Tag.D4 K (d4Rho i) (σ c)
  rw [h3]
  exact h2

@[expose] noncomputable def d4Twist (j : ℤ) (σ : K ≃+* K) : MulAut (adjointGroup Tag.D4 K) :=
  twistedEntrywiseAut TwistTag.D4 j σ

theorem d4Twist_one_adjX (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    d4Twist 1 σ (adjX Tag.D4 K i c) = adjX Tag.D4 K (d4Rho i) (σ c) :=
  twistedEntrywiseAut_one_adjX σ i c

@[expose] noncomputable def d4Regular (K : Type) [Field K] : adjointGroup Tag.D4 K :=
  adjX Tag.D4 K ⟨2, by decide⟩ 1 * adjX Tag.D4 K ⟨0, by decide⟩ 1 *
    adjX Tag.D4 K ⟨1, by decide⟩ 1 * adjX Tag.D4 K ⟨3, by decide⟩ 1

@[expose] def d4RegularIdx : List (Fin Tag.D4.rank) :=
  [⟨2, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩]

theorem commute_adjX_D4 {i j : Fin Tag.D4.rank} (hij : i ≠ j) (hc : Tag.D4.cartan i j ≠ -1)
    (a b : K) : Commute (adjX Tag.D4 K i a) (adjX Tag.D4 K j b) :=
  (simplePos_commute_iff_D4 hij).2 hc _ ⟨a, rfl⟩ _ ⟨b, rfl⟩

theorem d4Twist_one_d4Regular (σ : K ≃+* K) : d4Twist 1 σ (d4Regular K) = d4Regular K := by
  have h0 : (⟨0, by decide⟩ : Fin Tag.D4.rank) ≠ ⟨1, by decide⟩ := by decide
  have h03 : (⟨0, by decide⟩ : Fin Tag.D4.rank) ≠ ⟨3, by decide⟩ := by decide
  have h13 : (⟨1, by decide⟩ : Fin Tag.D4.rank) ≠ ⟨3, by decide⟩ := by decide
  have c01 := commute_adjX_D4 (K := K) h0 (by decide) 1 1
  have c03 := commute_adjX_D4 (K := K) h03 (by decide) 1 1
  have c13 := commute_adjX_D4 (K := K) h13 (by decide) 1 1
  have r2 : d4Rho (⟨2, by decide⟩ : Fin Tag.D4.rank) = ⟨2, by decide⟩ := by decide
  have r0 : d4Rho (⟨0, by decide⟩ : Fin Tag.D4.rank) = ⟨1, by decide⟩ := by decide
  have r1 : d4Rho (⟨1, by decide⟩ : Fin Tag.D4.rank) = ⟨3, by decide⟩ := by decide
  have r3 : d4Rho (⟨3, by decide⟩ : Fin Tag.D4.rank) = ⟨0, by decide⟩ := by decide
  unfold d4Regular
  simp only [map_mul, d4Twist_one_adjX, map_one, r2, r0, r1, r3]
  have e : adjX Tag.D4 K ⟨1, by decide⟩ 1 * adjX Tag.D4 K ⟨3, by decide⟩ 1 *
      adjX Tag.D4 K ⟨0, by decide⟩ 1 =
      adjX Tag.D4 K ⟨0, by decide⟩ 1 * adjX Tag.D4 K ⟨1, by decide⟩ 1 *
        adjX Tag.D4 K ⟨3, by decide⟩ 1 := by
    rw [mul_assoc, ← c03.eq, ← mul_assoc, ← c01.eq]
  simp only [mul_assoc] at e ⊢
  rw [e]

theorem eq_one_of_commute_fixed_twisted_D4 [Finite K] (σ : K ≃+* K) {z : adjointGroup Tag.D4 K}
    (hz : ∀ u ∈ fixedSubgroup (d4Twist 1 σ), z * u = u * z) : z = 1 := by
  classical
  set r : adjointGroup Tag.D4 K := d4Regular K with hr
  have hrΓ : r ∈ fixedSubgroup (d4Twist 1 σ) := d4Twist_one_d4Regular σ
  have hs1 : (z : ModGL Tag.D4 K) * (r : ModGL Tag.D4 K) = (r : ModGL Tag.D4 K) * z :=
    congrArg Subtype.val (hz r hrΓ)
  have hyU : (r : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K := by
    show xUnit Tag.D4 K _ 1 * xUnit Tag.D4 K _ 1 * xUnit Tag.D4 K _ 1 * xUnit Tag.D4 K _ 1 ∈ _
    exact mul_mem (mul_mem (mul_mem (CFSG.LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
      (CFSG.LieType.Chevalley.xUnit_mem_posUnipotent _ 1))
      (CFSG.LieType.Chevalley.xUnit_mem_posUnipotent _ 1))
      (CFSG.LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
  have hlist : (r : ModGL Tag.D4 K) = (d4RegularIdx.map fun j => xUnit Tag.D4 K j 1).prod := by
    simp [hr, d4Regular, d4RegularIdx, adjX, mul_assoc]
  have hco : ∀ i, HasCoord i (r : ModGL Tag.D4 K) (1 : K) := by
    intro i
    have h := hasCoord_list_prod_xUnit_one (τ := Tag.D4) (K := K) d4RegularIdx i
    have hcount : d4RegularIdx.count i = 1 := by fin_cases i <;> rfl
    rw [hcount, Nat.cast_one, ← hlist] at h
    exact h
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  have hw₀rel : w₀ ∈ relWeylTwist TwistTag.D4 := by
    obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.D4
    rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
    exact hw₁
  have hmem : canonicalRep (coxeterSystem TwistTag.D4.tag) K w₀ ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := canonicalRep_mem_graphFixedRootGroup hw₀rel
  have hΓ := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hmem
  have hadj : canonicalRep (coxeterSystem Tag.D4) K w₀ ∈ adjointGroup Tag.D4 K :=
    canonicalRep_mem_adjointGroup _ K w₀
  have hfix : (⟨_, hadj⟩ : adjointGroup Tag.D4 K) ∈ fixedSubgroup (d4Twist 1 σ) := by
    have h1 : (⟨_, hadj⟩ : adjointGroup TwistTag.D4.tag K) ∈
        (twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf
          (adjointGroup TwistTag.D4.tag K) := hΓ
    rw [← fixedSubgroup_twistedEntrywiseAut_one] at h1
    exact h1
  have hn : (z : ModGL Tag.D4 K) * canonicalRep (coxeterSystem Tag.D4) K w₀ =
      canonicalRep (coxeterSystem Tag.D4) K w₀ * z :=
    congrArg Subtype.val (hz _ hfix)
  exact Subtype.ext (eq_one_of_commute_regular z.2 (y := fun _ => (r : ModGL Tag.D4 K))
    (fun _ => hyU) (c := fun _ => (1 : K)) (fun _ => one_ne_zero) hco hw₀ (fun _ => hs1) hn)

end Central

end CFSG.LieType.SeitzGeneration.ExcWideThree
