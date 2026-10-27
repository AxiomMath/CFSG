module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTw
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwDefs
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)

section


open CFSG.HardMathSupport.Lang.Coordinator in
theorem two_le_pRank_fixed_twistedE6_cross {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hne : ℓ ≠ p) (hf : 1 ≤ f) {S : Type} [Group S] [Finite S]
    (hchev : ChevalleyExceptionalModel S .twistedE6 ℓ f)
    (hpg : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1)) (hstep : TwE6CrossRankStep)
    (β : MulAut S) (hβ : β ^ p = 1) (hβin : β ∉ inner S)
    (hrk : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup β) := by
  have hp1 : 1 < p := hp.one_lt
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  have hp2 : p ≠ 2 := by omega
  have hβp : (MulAut.congr e' β) ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr e' β ∉ twistedE6Inn K σ := fun hin =>
    hβin ((congr_mem_inner_iff e' β).mp hin)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hcard σ hσ
  have hη1 : Θ (MulAut.congr e' β) ≠ 1 := by
    intro h1
    have hmem : MulAut.congr e' β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout' (mem_inner_of_mem_inn_sup_diag hp hcard hσ hpg hcube hβp hmem)
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order hℓ hf K hK2f σ hσ Θ hΘ hp hp2
      (MulAut.congr e' β) hβp hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hℓ (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK2f, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ c, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hkcard, hJC, -, hder, -, -, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 hpodd K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
  set J := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
    (fixSubfieldRestrict T κ) with hJdef
  have hder' : ⁅fixedSubgroup δ, fixedSubgroup δ⁆ = J.subgroupOf (twistedE6RootGroup K σ) := hder
  have hJΓ : J.subgroupOf (twistedE6RootGroup K σ) ≤ fixedSubgroup δ := by
    rw [← hder']
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixedSubgroup δ).mul_mem ((fixedSubgroup δ).mul_mem ((fixedSubgroup δ).mul_mem ha hb)
        ((fixedSubgroup δ).inv_mem ha)) ((fixedSubgroup δ).inv_mem hb)
  have hσ₀' : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ) c = c ^ (ℓ ^ d) := fun c =>
    Subtype.ext (by rw [hσ₀]; rfl)
  have hkcard' : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ 2 := by
    rw [hkcard, ← pow_mul, mul_comm]
  have hrkC : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e'.symm]
    exact hrk
  have h4 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom)) :=
    hstep hℓ hd1 hp hp5 hne K (fixSubfield κ) σ (fixSubfieldRestrict T κ)
      (by rw [hcard, hd]) hkcard' (fun c => by rw [hσ c, hd]) hσ₀' hrkC
  let eJ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom) ≃*
      ↥J := Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.E6.tag)
        (fixSubfield κ).subtype) (baseChangeGL_injective _)
  let eJC : ↥(J.subgroupOf (twistedE6RootGroup K σ)) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  have h5 : CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(J.subgroupOf (twistedE6RootGroup K σ))) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJ).trans
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJC.symm)
  have h6 : CFSG.Open.pRank p (J.subgroupOf (twistedE6RootGroup K σ)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(J.subgroupOf (twistedE6RootGroup K σ))) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top _
  have h7 := CFSG.SectionRank.pRank_mono (p := p) hp1 hJΓ
  have h8 : CFSG.Open.pRank p (fixedSubgroup δ) ≤
      CFSG.Open.pRank p (fixedSubgroup (MulAut.congr e' β ^ r)) :=
    pRank_fixed_le_of_intertwine hp1 ψ (MulAut.congr e' β ^ r) δ (intertwine_of_conj' hψ)
  have h9 : fixedSubgroup (MulAut.congr e' β ^ r) ≤ fixedSubgroup (MulAut.congr e' β) := by
    have := fixedSubgroup_le_pow' (MulAut.congr e' β ^ r) s
    rwa [hrs] at this
  have h10 := CFSG.SectionRank.pRank_mono (p := p) hp1 h9
  have h11 : CFSG.Open.pRank p (fixedSubgroup (MulAut.congr e' β)) ≤
      CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 e' β (MulAut.congr e' β) fun x => by
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  omega

theorem outerFixedRankCrossAt_twistedE6_of_step (hstep : TwE6CrossRankStep) :
    OuterFixedRankCrossAt .twistedE6 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hne hdiv α hαp hαin hrk
  obtain ⟨hℓ, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  exact two_le_pRank_fixed_twistedE6_cross hℓ hp hp5 hne hf hch hdiv hstep α hαp hαin hrk

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
