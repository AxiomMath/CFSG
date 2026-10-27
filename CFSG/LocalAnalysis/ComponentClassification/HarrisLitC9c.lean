module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC9b
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def OddLieA6ComponentCentreInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Blueprint.OddLieType S → ∀ α : MulAut S, orderOf α = 2 →
    ∀ K : Subgroup (FixedCommutingProduct.fixedSubgroup α), IsComponent K →
      Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 6)) → IsPGroup 2 ↥(center ↥K)

namespace C9

open C311

theorem pPrimeCore_le_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : pPrimeCore 2 A ≤ center A) : pPrimeCore 2 B ≤ center B := by
  rw [← pPrimeCore_map_iso 2 e, ← Subgroup.map_center_eq e]
  exact map_mono h

theorem lieModel_quotient_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {p f : ℕ}
    (h : Blueprint.LieModel (A ⧸ pPrimeCore 2 A) .PSL 2 p f) :
    Blueprint.LieModel (B ⧸ pPrimeCore 2 B) .PSL 2 p f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) h

theorem eq_bot_of_isPGroup_two {A : Type*} [Group A] [Finite A] {H : Subgroup A}
    (hH : IsPGroup 2 H) (hodd : Nat.Coprime 2 (Nat.card H)) : H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rw [hn] at hodd
  have hn0 : n = 0 := by
    by_contra h0
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 h0
    exact absurd (Nat.Coprime.eq_one_of_dvd hodd h2) (by norm_num)
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq H hn

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_component {S : Subgroup G} [S.Normal] {a : G} {J : Subgroup G}
    (hJS : J ≤ S) (hJ : IsTwoComponentIn J (centralizer {a})) :
    ∃ K : Subgroup (FixedCommutingProduct.fixedSubgroup (MulAut.conjNormal (H := S) a)),
      IsPComponent 2 K ∧ Nonempty (↥J ≃* ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := (isTwoComponentIn_iff hJ.1).mp hJ
  have hJSC : J ≤ S ⊓ centralizer {a} := le_inf hJS hJ.1
  have hP2 : IsPComponent 2 (J.subgroupOf (S ⊓ centralizer {a})) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJSC inf_le_right hP
  let e := (infEquivSubgroupOf S (centralizer {a})).trans (FixedNormalCentralizer.equivalence S a)
  exact ⟨_, isPComponent_map_mulEquiv e hP2, ⟨(subgroupOfEquivOfLe hJSC).symm.trans
    ((J.subgroupOf (S ⊓ centralizer {a})).equivMapOfInjective _ e.injective)⟩⟩

theorem pPrimeCore_eq_bot_of_oddLie (hA6 : OddLieA6ComponentCentreInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hodd : Blueprint.OddLieType S)
    {α : MulAut S} (hα : orderOf α = 2) {K : Subgroup (FixedCommutingProduct.fixedSubgroup α)}
    (hK : IsPComponent 2 K) {J : Type} [Group J] [Finite J] (eJK : J ≃* ↥K)
    (hJ : IsTwoQuasisimple J) {p f : ℕ} (hm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (h9 : p ^ f = 9) (hle : pPrimeCore 2 J ≤ center J) : pPrimeCore 2 J = ⊥ := by
  have : IsSimpleGroup (J ⧸ pPrimeCore 2 J) := isSimpleGroup_of_lieModel_psl2 hm
  have hna := nonabelian_of_lieModel_psl2 hm
  have hZO := center_eq_pPrimeCore hle hna
  let eQ : J ⧸ center J ≃* J ⧸ pPrimeCore 2 J := QuotientGroup.quotientMulEquivOfEq hZO
  have : IsSimpleGroup (J ⧸ center J) := eQ.isSimpleGroup
  have hJq : IsQuasisimple J := by
    refine ⟨hJ.1, inferInstance, ?_⟩
    obtain ⟨u, v, huv⟩ := hna
    exact ⟨eQ.symm u, eQ.symm v, fun h => huv (by simpa using congrArg eQ h)⟩
  obtain ⟨hsub, -⟩ := (isTwoComponent_iff_isPComponent K).mpr hK
  have hKc : IsComponent K := ⟨LocalCores.isQuasisimple_of_mulEquiv eJK hJq, hsub⟩
  obtain ⟨eA⟩ := (card_eq_and_equiv_of_lieModel_nine hm h9).2
  let eKA : ↥K ⧸ center ↥K ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.congr _ _ eJK (Subgroup.map_center_eq eJK)).symm.trans eQ).trans eA
  have hZK := hA6 S hnab hodd α hα K hKc ⟨eKA⟩
  have hZJ : IsPGroup 2 ↥(center J) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZK
    exact IsPGroup.iff_card.mpr ⟨n, by rw [Nat.card_congr (Subgroup.centerCongr eJK).toEquiv, hn]⟩
  exact eq_bot_of_isPGroup_two (hZJ.to_le hle) pPrimeCore_coprime_card

section Main


theorem harris34Nine_of (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hA6 : OddLieA6ComponentCentreInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
      IsSimpleGroup ↥(Open.genFittingFStar G) → HarrisF p ↥(Open.genFittingFStar G) →
      ∀ J : Subgroup G, IsInvolutionTwoComponent J → ∀ p' f' : ℕ,
        Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p' f' → p' ^ f' = 9 →
          pPrimeCore 2 ↥J ≤ center ↥J → pPrimeCore 2 ↥J = ⊥ := by
  intro G _ _ p _ _ hS hF J hJ p' f' hm h9 hle
  classical
  obtain ⟨a, ha, hJa⟩ := hJ
  set S := Open.genFittingFStar G with hSdef
  have : S.Normal := ClassicalInvolution.genFittingFStar_normal G
  have : IsSimpleGroup ↥S := hS
  have hnab := nonabelian_of_harrisF hF
  have hcat := catalog_of_harrisF hF
  have hC : centralizer (S : Set G) = ⊥ :=
    CatalogueRelativeB.simple_self_centralizing_centralizer_eq_bot S hnab
      (Adapters.generalized_fitting_self_centralizing G)
  by_cases hO : CFSG.oddCore ↥(centralizer ({a} : Set G)) = ⊥
  · have hO' : pPrimeCore 2 ↥(centralizer ({a} : Set G)) = ⊥ := by
      rw [← oddCore_eq_pPrimeCore_two]
      exact hO
    have h1 := pPrimeCore_eq_bot_of_isSubnormal hO' hJa.2.1
    exact pPrimeCore_eq_bot_of_mulEquiv (subgroupOfEquivOfLe hJa.1).symm h1
  have hUG := hU G hS hnab hcat ⟨a, ha, hO⟩
  have hout : Group.IsSolvable (OuterAutomorphisms.Outer ↥S) := hSch ↥S hnab hcat
  have : Group.IsPerfect ↥J := hJa.2.2.1
  have hJS : J ≤ S := le_of_isPerfect hC
  have hα1 : MulAut.conjNormal (H := S) a ≠ 1 := by
    intro h1
    have haC : a ∈ centralizer (S : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h3 := congrArg (fun φ : MulAut S => ((φ ⟨x, hx⟩ : S) : G)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc x * a = a * x * a⁻¹ * a := by rw [h3]
        _ = a * x := by group
    rw [hC, mem_bot] at haC
    rw [haC, orderOf_one] at ha
    omega
  have hαo : orderOf (MulAut.conjNormal (H := S) a) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, ← pow_two, ← ha, pow_orderOf_eq_one, map_one])
      hα1
  obtain ⟨K, hK, ⟨eJK⟩⟩ := exists_fixed_component hJS hJa
  rcases hUG with hodd | ⟨n, -, hn7, ⟨θ⟩, -⟩ | ⟨hm34 | hHe, -⟩
  ·
    exact pPrimeCore_eq_bot_of_oddLie hA6 hnab hodd hαo hK eJK hJa.2.2 hm h9 hle
  ·
    have : IsSimpleGroup ↥(GeneralizedFitting.subgroup G) := hS
    exact pPrimeCore_eq_bot_of_alternating hnab (Or.inr hn7) θ ha hJa
  ·
    refine pPrimeCore_eq_bot_of_card_dvd hJa.2.2 hm h9 hle ?_
    rw [← CatLeaf.card_of_isL34Type hm34]
    exact Subgroup.card_dvd_of_le hJS
  ·
    have h := pPrimeCore_eq_bot_of_held hnab hHe.some _ hαo K hK
      (lieModel_quotient_of_mulEquiv eJK hm) h9 (pPrimeCore_le_center_of_mulEquiv eJK hle)
    exact pPrimeCore_eq_bot_of_mulEquiv eJK h

end Main

end C9

end CFSG.ComponentClassification.HarrisLit
