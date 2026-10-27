module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3Actor
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Layer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_adjointE6_four_R3 (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card K ^ 2 + 1) :
    InnerPlaneBalance p (adjointGroup Tag.E6 K) := by
  classical
  have hp3 : 3 < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by exact_mod_cast hpd
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  set n : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L e6F4U with hn
  have hcm : n ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L e6F4U
  have hπ : weylQuotientHom Tag.E6 L ⟨n, hcm⟩ = e6F4U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6F4U)
  have hnW : ∀ u, weylQuotientHom Tag.E6 L ⟨n, hcm⟩ • u = (weylMatrix e6F4U) *ᵥ u := fun u => by
    rw [hπ, weylMatrix_mulVec]
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_four_frame K hf hK hp hp3 hpq L n hcm hnW
  intro E hEin hE hcard H hH
  have hC : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup Tag.E6 K) := E.comap
    (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)) = E := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hEin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hq
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨g, a, σ, ε, hzE⟩ := exists_conj_mul_exactNormalAut (τ := Tag.E6) (K := K) (Or.inl rfl) z
  have hexpr : ∀ y : adjointGroup Tag.E6 K, (z y : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) *
      rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε * Units.map (entrywiseHom σ.toRingHom)
        (y : ModGL Tag.E6 K) * (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ *
          (g : ModGL Tag.E6 K)⁻¹ := by
    intro y
    rw [hzE, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hex : ∀ i : Fin Tag.E6.rank, ∃ (q : adjointGroup Tag.E6 K), q ∈ A₀ ∧ q ≠ 1 ∧
      σ = 1 ∧ (ε : ℕ) = 0 ∧ ∃ a' : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit Tag.E6 a' = g0⁻¹ * adjEmb Tag.E6 K L c *
          baseChangeGL (algebraMap K L) ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) *
            (adjEmb Tag.E6 K L c)⁻¹ * g0 ∧ a' i = 1 := by
    intro i
    obtain ⟨q, hqA, hq1, b, hb, hbi⟩ :=
      e6_four_exists_nonregular_at K hp L n g0 A₀ hA₀card hA₀exp c hc i
    have hqp : orderOf q = p := orderOf_eq_prime (hA₀exp q hqA) hq1
    obtain ⟨hquasi, hpR, hact⟩ := e6_four_actor K hf hK hp hp3 hordq hΦ L n hcm hnW g0 hg0C hg0
      hperf hT hqp c (hc q hqA) hb ⟨_, hbi⟩
    obtain ⟨hzq, hzD⟩ := fixes_of_mem_localDeltaIn hp hinj hH hz hqA hq1 hquasi hpR
    obtain ⟨hσ, hε, a', ha', hker⟩ := hact z g a σ ε hzq hzD hexpr
    refine ⟨q, hqA, hq1, hσ, hε, a', ha', ?_⟩
    have := hker _ hbi
    rwa [CTTorus.rootChar_single] at this
  choose q hqA hq1 hσ hε a' ha' hai using hex
  have i0 : Fin Tag.E6.rank := ⟨0, by decide⟩
  have hσ1 : σ = 1 := hσ i0
  have hε0 : (ε : ℕ) = 0 := hε i0
  have hcommon : ∀ i, a' i = a' i0 := fun i =>
    rootDiagUnit_injective ((ha' i).trans (ha' i0).symm)
  have hone : a' i0 = 1 := funext fun j => by
    have := hai j
    rwa [hcommon j] at this
  have hM : g0⁻¹ * adjEmb Tag.E6 K L c *
      baseChangeGL (algebraMap K L) ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) *
        (adjEmb Tag.E6 K L c)⁻¹ * g0 = 1 := by
    rw [← ha' i0, hone, rootDiagUnit_one]
  have hm1 : (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a = 1 := by
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K L)
    rw [map_one]
    have h1 : baseChangeGL (algebraMap K L) ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) =
        (adjEmb Tag.E6 K L c)⁻¹ * g0 * (g0⁻¹ * adjEmb Tag.E6 K L c *
          baseChangeGL (algebraMap K L) ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) *
            (adjEmb Tag.E6 K L c)⁻¹ * g0) * g0⁻¹ * adjEmb Tag.E6 K L c := by group
    rw [h1, hM]
    group
  have hid : ∀ y : ModGL Tag.E6 K, Units.map (entrywiseHom σ.toRingHom) y = y := fun y => by
    subst hσ1
    exact Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K ε = 1 := by
    rw [hε0]
    exact exactQ_zero Tag.E6 K
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  rw [hexpr y, hid, hQ0]
  have h2 : (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * 1 * (y : ModGL Tag.E6 K) * (1 : ModGL Tag.E6 K)⁻¹ *
      (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹ =
      ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) * (y : ModGL Tag.E6 K) *
        ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a)⁻¹ := by group
  rw [h2, hm1]
  simp

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
