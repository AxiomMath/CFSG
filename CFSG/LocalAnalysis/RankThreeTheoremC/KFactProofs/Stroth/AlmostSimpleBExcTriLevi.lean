module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Toral
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res417Seven
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section Levi


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem levi_threeGroup_comm (hσ : σ ^ 3 = 1) (a : Fin TwistTag.D4.foldedTag.rank)
    {S : Subgroup (ModGL TwistTag.D4.tag K)}
    (hSL : S ≤ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a}) (hS : IsPGroup 3 S) :
    ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
  classical
  have hTcomm := (triangular_borel_structure.{0, 0} TwistTag.D4.tag K).1
  set R := orbitRankOneHom TwistTag.D4 K σ.toRingHom a
  have hinj : Function.Injective R := orbitRankOneHom_injective_D4 hσ a
  set M := R.range
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom
  set Z := H ⊓ Subgroup.centralizer (M : Set (ModGL TwistTag.D4.tag K))
  have hHM : H ≤ Subgroup.normalizer (M : Set (ModGL TwistTag.D4.tag K)) :=
    graphFixedRootTorus_le_normalizer _ a
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy => hTcomm _ hx.1.1 _ hy.1.1
  have hdec : ∀ e ∈ S, ∃ z ∈ Z, ∃ m ∈ M, e = z * m := by
    intro e he
    have he' : e ∈ ((H ⊔ M : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := graphFixedParabolicLevi_singleton_le_sup σ a (hSL he)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H M hHM] at he'
    obtain ⟨h, hh, m, hm, rfl⟩ := he'
    have hh' : h ∈ H := hh
    obtain ⟨l, hl⟩ := exists_mul_orbitH_inv_mem_centralizer σ.toRingHom a hh'
    refine ⟨h * (orbitH TwistTag.D4 K σ.toRingHom a l : ModGL TwistTag.D4.tag K)⁻¹,
      ⟨H.mul_mem hh' (H.inv_mem (orbitH_mem_graphFixedRootTorus _ a l)), hl⟩,
      (orbitH TwistTag.D4 K σ.toRingHom a l : ModGL TwistTag.D4.tag K) * m,
      mul_mem (orbitH_mem_range _ a l) hm, by group⟩
  have hZE : ∀ z ∈ Z, ∀ e ∈ S, e * z = z * e := by
    intro z hz e he
    obtain ⟨z', hz', m, hm, rfl⟩ := hdec e he
    have h1 : m * z = z * m := (Subgroup.mem_centralizer_iff.1 hz.2) m hm
    rw [mul_assoc, h1, ← mul_assoc, hHcomm z' hz'.1 z hz.1, mul_assoc]
  have hZSn : Z ≤ Subgroup.normalizer (S : Set (ModGL TwistTag.D4.tag K)) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      rw [← hZE z hz e he, mul_inv_cancel_right]
      exact he
    · intro he
      have h1 := hZE z hz _ he
      have h2 : z * e = z * (z * e * z⁻¹) := by
        calc z * e = z * e * z⁻¹ * z := by group
          _ = z * (z * e * z⁻¹) := h1
      have h3 : e = z * e * z⁻¹ := mul_left_cancel h2
      rw [h3]
      exact he
  set S' := (S ⊔ Z) ⊓ M with hS'
  have hS'3 : ∀ m ∈ S', ∃ k : ℕ, m ^ 3 ^ k = 1 := by
    rintro m ⟨hmEZ, hmM⟩
    have hmEZ' : m ∈ ((S ⊔ Z : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := hmEZ
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S Z hZSn] at hmEZ'
    obtain ⟨e, he, z, hz, rfl⟩ := hmEZ'
    obtain ⟨k, hk⟩ := hS ⟨e, he⟩
    have hk' : e ^ 3 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hcomm : Commute e z := hZE z hz e he
    have hpow : (e * z) ^ 3 ^ k = z ^ 3 ^ k := by
      rw [hcomm.mul_pow, hk', one_mul]
    rw [hpow]
    refine eq_one_of_mem_range_of_mem_centralizer σ hσ a ?_ (pow_mem hz.2 _)
    rw [← hpow]
    exact pow_mem hmM _
  set S'' := S'.comap R with hS''
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (orbitField TwistTag.D4 K σ.toRingHom a) := Subtype.finite
  have hS''p : IsPGroup 3 S'' := fun A => by
    obtain ⟨k, hk⟩ := hS'3 (R A) A.2
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    rw [Subgroup.coe_pow, map_pow, hk, Subgroup.coe_one, map_one]
  have hcyc := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic (by norm_num) S'' hS''p
  letI : CommGroup S'' := IsCyclic.commGroup
  have hmS' : ∀ e ∈ S, ∀ z ∈ Z, ∀ m ∈ M, e = z * m → m ∈ S' := by
    intro e he z hz m hm hem
    have e1 : m = z⁻¹ * e := by rw [hem]; group
    have hmem : z⁻¹ * e ∈ S ⊔ Z := (S ⊔ Z).mul_mem
      ((S ⊔ Z).inv_mem (Subgroup.mem_sup_right hz)) (Subgroup.mem_sup_left he)
    have hm' : m ∈ S ⊔ Z := by rw [e1]; exact hmem
    exact ⟨hm', hm⟩
  intro s hs t ht
  obtain ⟨z₁, hz₁, m₁, hm₁, hsm⟩ := hdec s hs
  obtain ⟨z₂, hz₂, m₂, hm₂, htm⟩ := hdec t ht
  obtain ⟨A₁, rfl⟩ := hm₁
  obtain ⟨A₂, rfl⟩ := hm₂
  have hA₁ : A₁ ∈ S'' := hmS' s hs z₁ hz₁ _ ⟨A₁, rfl⟩ hsm
  have hA₂ : A₂ ∈ S'' := hmS' t ht z₂ hz₂ _ ⟨A₂, rfl⟩ htm
  have hAc : A₁ * A₂ = A₂ * A₁ := by
    have := mul_comm (⟨A₁, hA₁⟩ : S'') ⟨A₂, hA₂⟩
    exact congrArg Subtype.val this
  have hmc : R A₁ * R A₂ = R A₂ * R A₁ := by rw [← map_mul, ← map_mul, hAc]
  have hz₂m : R A₁ * z₂ = z₂ * R A₁ := (Subgroup.mem_centralizer_iff.1 hz₂.2) _ ⟨A₁, rfl⟩
  have hz₁m : R A₂ * z₁ = z₁ * R A₂ := (Subgroup.mem_centralizer_iff.1 hz₁.2) _ ⟨A₂, rfl⟩
  have hzz : z₁ * z₂ = z₂ * z₁ := hHcomm _ hz₁.1 _ hz₂.1
  rw [hsm, htm]
  calc z₁ * R A₁ * (z₂ * R A₂) = z₁ * (R A₁ * z₂) * R A₂ := by group
    _ = z₁ * (z₂ * R A₁) * R A₂ := by rw [hz₂m]
    _ = (z₁ * z₂) * (R A₁ * R A₂) := by group
    _ = (z₂ * z₁) * (R A₂ * R A₁) := by rw [hzz, hmc]
    _ = z₂ * (z₁ * R A₂) * R A₁ := by group
    _ = z₂ * (R A₂ * z₁) * R A₁ := by rw [hz₁m]
    _ = z₂ * R A₂ * (z₁ * R A₁) := by group

end Levi

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
