module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicNoA6
public import CFSG.Sporadic.Recognition.J3MultiplierCert
public import CFSG.GH74.E2.ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_dvd_j3_fixed {q c : ℕ} (h11 : 11 ≤ q) (hc : c = 1920 ∨ c = 2448) :
    ¬ q * (q ^ 2 - 1) ∣ c := by
  intro hd
  have hle : q * (q ^ 2 - 1) ≤ 2448 := by
    rcases hc with rfl | rfl
    · exact (Nat.le_of_dvd (by norm_num) hd).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) hd
  have hq : q ≤ 13 := by
    by_contra h
    have h1 : 14 ≤ q := by omega
    have h2 : 14 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : 14 * (14 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    omega
  interval_cases q <;> rcases hc with rfl | rfl <;> norm_num at hd

theorem chev_of_mulEquiv {A Z : Type} [Group A] [Group Z] {r : ℕ}
    (hA : HarrisLit.IsSimpleChevalleyOver r A) (hA2 : ¬ GH74.GLS.InChev2 A) (e : A ≃* Z) :
    HarrisLit.IsSimpleChevalleyOver r Z ∧ ¬ GH74.GLS.InChev2 Z := by
  obtain ⟨τ, n, f, h⟩ := hA
  exact ⟨⟨τ, n, f, Blueprint.LieModel.of_mulEquiv e h⟩,
    fun h => hA2 (GH74.E2.inChev2_of_mulEquiv e.symm h)⟩

theorem chevOddPump_aut (hleaf : ChevOddPumpLeaf)
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y))
    (hcat : Blueprint.Catalog ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)))
    (β : MulAut Y) (hβ : ∀ y, β (β y) = y) {T : Subgroup Y} (hTF : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) {r q : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h11 : 11 ≤ q)
    (hTY : HarrisLit.IsSimpleChevalleyOver r (↥T ⧸ Open.fusionZStar ↥T))
    (hTY2 : ¬ GH74.GLS.InChev2 (↥T ⧸ Open.fusionZStar ↥T))
    (hk : q * (q ^ 2 - 1) ∣ Nat.card (↥T ⧸ pPrimeCore 2 ↥T)) :
    HarrisLit.IsSimpleChevalleyOver r (Y ⧸ Open.fusionZStar Y) ∧
      ¬ GH74.GLS.InChev2 (Y ⧸ Open.fusionZStar Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hT
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTF).toMonoidHom)
      (subgroupOfEquivOfLe hTF).surjective
  have hTq : IsQuasisimple (T ⧸ pPrimeCore 2 T) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTF)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hT)
  let eTop : (⊤ : Subgroup Y) ≃* Y := Subgroup.topEquiv
  have : Group.IsPerfect (⊤ : Subgroup Y) :=
    Group.IsPerfect.ofSurjective (f := eTop.symm.toMonoidHom) eTop.symm.surjective
  have hTop : IsPComponent 2 (⊤ : Subgroup Y) := by
    rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple]
    exact ⟨Subgroup.IsSubnormal.top, HarrisLit.primeResidual_eq_top_of_isPerfect,
      LocalCores.isQuasisimple_of_mulEquiv
        (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eTop).symm hYq⟩
  obtain ⟨eYS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar Y
  obtain ⟨hle, heq⟩ := UnbalancedGS.OrbitFixedComponent.stable_case (⊤ : Subgroup Y)
    (fixedSubgroup β) le_top T hTF hT
  rcases hle.lt_or_eq with hlt | hidx
  swap
  ·
    obtain ⟨e⟩ := stable_case_type hTop le_top hTq (heq hidx).2
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' eTop
    exact chev_of_mulEquiv hTY hTY2 (e.trans eZ)
  have hlt' : (pPrimeCore 2 T).index < (pPrimeCore 2 Y).index := by
    rw [index_eq_card (pPrimeCore 2 Y),
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eTop, ← index_eq_card]
    exact hlt
  obtain ⟨σ, -, hσ, hPF, hP, hPne, ⟨eP⟩⟩ :=
    GrSLit.exists_simple_fixed_component_image hYq β hβ hTF hT hlt'
  have : IsSimpleGroup ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) := hYq.2.1
  have hna := hYq.2.2
  obtain ⟨hP1, hP2⟩ := chev_of_mulEquiv hTY hTY2 eP
  rcases hleaf _ inferInstance hna hcat σ _ ⟨hσ, hPF, hP, hPne⟩ r hr hr2 hP1 hP2 with
      ⟨hS1, hS2⟩ | ⟨⟨eJ⟩, -⟩
  · obtain ⟨τ, n, f, h⟩ := hS1
    exact ⟨⟨τ, n, f, Blueprint.LieModel.of_mulEquiv eYS h⟩,
      fun h => hS2 (GH74.E2.inChev2_of_mulEquiv eYS.symm h)⟩
  ·
    exfalso
    set π₁ := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ₁
    set π₂ := QuotientGroup.mk' (center (Y ⧸ pPrimeCore 2 Y)) with hπ₂
    have hodd := RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
      Sporadic.Recognition.J3Multiplier.noPerfectDoubleCover_nativeJ3_of_certificate
      (Y ⧸ pPrimeCore 2 Y) hYq.1.commutator_eq_top ⟨eJ⟩
    have hZ : center (Y ⧸ pPrimeCore 2 Y) = ⊥ := by
      have hle : center (Y ⧸ pPrimeCore 2 Y) ≤ pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) :=
        le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
      rw [GH74.pPrimeCore_quotient_pPrimeCore_eq_bot Y 2] at hle
      exact le_bot_iff.mp hle
    let φ : T →* (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y) :=
      (π₂.comp π₁).comp T.subtype
    have hrange : φ.range = (T.map π₁).map π₂ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_map]
    have hker : φ.ker ≤ pPrimeCore 2 T := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : π₁ (x : Y) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
        rw [← QuotientGroup.eq_one_iff (N := center (Y ⧸ pPrimeCore 2 Y))]
        exact hx
      rw [hZ, mem_bot, hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      have hcomap : (pPrimeCore 2 Y).comap T.subtype ≤ pPrimeCore 2 T :=
        le_sSup ⟨inferInstance, Nat.Coprime.coprime_dvd_right
          (card_comap_dvd_of_injective _ _ T.subtype_injective) pPrimeCore_coprime_card⟩
      exact hcomap (by rw [mem_comap]; exact hx1)
    have hdvdP : Nat.card (T ⧸ pPrimeCore 2 T) ∣ Nat.card ↥((T.map π₁).map π₂) := by
      rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
        ← index_eq_card, ← index_eq_card]
      exact Subgroup.index_dvd_of_le hker
    have hσ1 := ProperFixedComponent.ne_one ⟨hσ, hPF, hP, hPne⟩
    have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
      rw [sq]; exact MulEquiv.ext fun y => hσ y) hσ1
    have hfix := CatFC.card_fixedSubgroup_j3 eJ hσ2
    have hdvd : q * (q ^ 2 - 1) ∣ Nat.card (fixedSubgroup σ) :=
      hk.trans (hdvdP.trans (Subgroup.card_dvd_of_le hPF))
    exact not_dvd_j3_fixed h11 hfix hdvd

end CFSG.ComponentClassification.GS82PumpInputs
