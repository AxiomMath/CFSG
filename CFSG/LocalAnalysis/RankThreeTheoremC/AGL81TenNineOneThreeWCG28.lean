module

import CFSG.RankThree.Chevalley.SteinbergBMG2NoninnerLocalCore
import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeG28Rank
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeListOf
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.Open TauCeti

@[expose] def KFactG28SylowCenter : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsCaseIThreeG28 Y →
    ∀ (T : Sylow 3 Y) (a b : Y), a ∈ (T : Subgroup Y) → b ∈ (T : Subgroup Y) →
      orderOf a = 3 → orderOf b = 3 → (∀ t ∈ (T : Subgroup Y), t * a * t⁻¹ = a) →
      (∀ t ∈ (T : Subgroup Y), t * b * t⁻¹ = b) → b ∈ Subgroup.zpowers a

theorem g28_inner_of_fix
    {F : Type} [Field F] (hF : Nat.card F = 2 ^ 3) (φ : MulAut (adjointGroup .G2 F))
    (hφ : φ ^ 3 = 1) (T : Subgroup (adjointGroup .G2 F)) (hT : Nat.card T = 243)
    (hfix : ∀ t ∈ T, φ t = t) :
    φ ∈ (MulAut.conj : adjointGroup .G2 F →* MulAut (adjointGroup .G2 F)).range := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  by_contra hin
  have hφ1 : φ ≠ 1 := fun h => hin ⟨1, by rw [h, map_one]⟩
  have hNF := conj_normalForm_of_pointwise
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (by norm_num : 2 ≤ 3) F hF).1
  obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF φ
  have hαp : orderOf (⟨φ, Subgroup.mem_top φ⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup .G2 F)))) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hφ hφ1
  obtain ⟨hσp, -, ⟨h, hh⟩, -⟩ := even_G2_noninner_prime_local_core_trivial
    (by norm_num : 2 ≤ 3) hF Nat.prime_three ⊤ le_top ⟨φ, Subgroup.mem_top φ⟩ hin hαp y σ hyσ
  have hh' : MulAut.conj h * φ * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ := hh
  obtain ⟨-, hk, -, hloc, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders (by norm_num : 2 ≤ 3) hF σ
  rw [hσp] at hk
  haveI : Finite (fixSubfield σ) := Subtype.finite
  set E := (entrywiseAdjointAut .G2 σ).toMonoidHom.eqLocus (MonoidHom.id _) with hEdef
  have hE : Nat.card E = ordG2 2 := by
    rw [← Subgroup.card_map_of_injective (adjointGroup .G2 F).subtype_injective, hloc,
      ← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
    norm_num
  have hle : T.map (MulAut.conj h).toMonoidHom ≤ E := by
    rintro _ ⟨t, ht, rfl⟩
    show (entrywiseAdjointAut .G2 σ).toMonoidHom ((MulAut.conj h).toMonoidHom t) =
      MonoidHom.id _ ((MulAut.conj h).toMonoidHom t)
    rw [MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, ← hh']
    simp [MulAut.mul_apply, hfix t ht]
    group
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hT, hE] at hdvd
  revert hdvd
  unfold ordG2
  norm_num

theorem factorization_ordG2_eight : (ordG2 8).factorization 3 = 5 := by
  rw [G28Rank.ordG2_eq, show (4329310519296 : ℕ) = 3 ^ 5 * 17816092672 by norm_num,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem g28_hZ_hinnT
    {K : Type} [Group K] [Finite K] (d : ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsGTwoEightIndex d) (e : K ≃* (CFSGIndex.lie d).Group) :
    (∀ k : K, (∀ x : K, k * x = x * k) → k = 1) ∧
    (∀ (T : Sylow 3 K) (φ : MulAut K), φ ^ 3 = 1 →
      (∀ t ∈ (T : Subgroup K), φ t = t) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK8 : Nat.card K = ordG2 8 := G28Rank.card_of_isGTwoEightIndex d hd e
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  subst hd1
  obtain ⟨F, _, _, -, hF⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card q.p
    q.exponent q.prime_p q.exponent_pos
  rw [hqp, hqe] at hF
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv F
    (by rw [hF, PrimePower.card_def, hqp, hqe])
  have hZX : Subgroup.center (adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  set e' : K ≃* adjointGroup .G2 F := e.trans (b.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot))
  refine ⟨fun k hk => ?_, fun T φ hφ hfix => ?_⟩
  · have hc : e' k ∈ Subgroup.center (adjointGroup .G2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e' (hk (e'.symm y))
      simpa using this.symm
    rw [hZX, Subgroup.mem_bot] at hc
    exact e'.injective (by rw [hc, map_one])
  · set ψ : MulAut (adjointGroup .G2 F) := MulAut.congr e' φ
    have hψ : ψ ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
    have hT : Nat.card ((T : Subgroup K).map e'.toMonoidHom) = 243 := by
      rw [Subgroup.card_map_of_injective e'.injective, T.card_eq_multiplicity, hK8,
        factorization_ordG2_eight]
      norm_num
    have hfixψ : ∀ t ∈ (T : Subgroup K).map e'.toMonoidHom, ψ t = t := by
      rintro _ ⟨t, ht, rfl⟩
      simp [ψ, MulAut.congr_apply, hfix t ht]
    obtain ⟨g, hg⟩ := g28_inner_of_fix hF ψ hψ _ hT hfixψ
    refine ⟨e'.symm g, fun x => e'.injective ?_⟩
    have h1 : ψ (e' x) = e' (φ x) := by simp [ψ, MulAut.congr_apply]
    rw [← h1, ← hg, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
