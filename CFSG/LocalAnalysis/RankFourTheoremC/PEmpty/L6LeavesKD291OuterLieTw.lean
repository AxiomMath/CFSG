module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)

theorem intertwine_of_conj' {G : Type*} [Group G] {α β δ : MulAut G} (h : δ * α * δ⁻¹ = β)
    (x : G) : β (δ x) = δ (α x) := by
  rw [← h]
  simp [MulAut.mul_apply]

theorem fixedSubgroup_le_pow' {G : Type*} [Group G] (β : MulAut G) (n : ℕ) :
    fixedSubgroup β ≤ fixedSubgroup (β ^ n) := by
  intro x hx
  have hx' : β x = x := hx
  change (β ^ n) x = x
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx']; exact ih

section


theorem twistedModel_graphFixedRootGroup {t : TwistTag} {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = (p ^ d) ^ t.order) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c, σ₀ c = c ^ (p ^ d)) :
    TwistedChevalleyModel (graphFixedRootGroup t k σ₀.toRingHom) t (p ^ d) := by
  have hperf := (finite_fixed_root_group_perfect t hp hd k hk σ₀.toRingHom hσ₀).2.2.1
  have hZ := center_graphFixedRootGroup_eq_bot (t := t) (K := k) (σ := σ₀.toRingHom)
    σ₀.surjective
  obtain ⟨E⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_mulEquiv_of_eq hperf hZ
  exact ⟨k, inferInstance, inferInstance, hk, σ₀.toRingHom, hσ₀, ⟨E.symm⟩⟩

open CFSG.HardMathSupport.Lang.Coordinator in
theorem two_le_pRank_fixed_twistedE6 {ℓ f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p = ℓ)
    (hf : 1 ≤ f) {S : Type} [Group S] [Finite S]
    (hchev : ChevalleyExceptionalModel S .twistedE6 ℓ f)
    (β : MulAut S) (hβ : β ^ p = 1) (hβin : β ∉ inner S) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup β) := by
  subst hpℓ
  have hp1 : 1 < p := hp.one_lt
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have hK2f : Nat.card K = p ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  have hp2 : p ≠ 2 := by omega
  have hβp : (MulAut.congr e' β) ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr e' β ∉ twistedE6Inn K σ := fun hin =>
    hβin ((congr_mem_inner_iff e' β).mp hin)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hcard σ hσ
  have hpg : ¬ p ∣ Nat.gcd 3 (p ^ f + 1) := fun h => by
    have h1 : p ∣ p ^ f + 1 := h.trans (Nat.gcd_dvd_right 3 _)
    have h2 : p ∣ p ^ f := dvd_pow_self _ (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  have hη1 : Θ (MulAut.congr e' β) ≠ 1 := by
    intro h1
    have hmem : MulAut.congr e' β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout' (mem_inner_of_mem_inn_sup_diag hp hcard hσ hpg hcube hβp hmem)
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order hp hf K hK2f σ hσ Θ hΘ hp hp2
      (MulAut.congr e' β) hβp hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hp (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ p ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = p ^ (2 * d * p) := by rw [hK2f, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ p ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ p ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hkcard, hJC, -, hder, -, -, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hp hd1 hm3 hpodd K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
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
  have hσ₀' : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ) c = c ^ (p ^ d) := fun c =>
    Subtype.ext (by rw [hσ₀]; rfl)
  have hkcard' : Nat.card (fixSubfield κ) = (p ^ d) ^ TwistTag.E6.order := by
    rw [hkcard, ← pow_mul, mul_comm]
    rfl
  have hmodel := twistedModel_graphFixedRootGroup (t := TwistTag.E6) hp hd1 (fixSubfield κ)
    hkcard' (fixSubfieldRestrict T κ) hσ₀'
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom)) :=
    CFSG.SectionRank.four_le_pRank_of_twistedE6Model hd1 hmodel
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

theorem outerFixedRankDefAt_twistedE6 : OuterFixedRankDefAt .twistedE6 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  exact Or.inl (two_le_pRank_fixed_twistedE6 hp hp5 rfl hf hch α hαp hαin)

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
