module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPFamilies
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer subfieldRootGroupImage)


theorem s2019OuterComp_twistedE6 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group)
    (β : MulAut K) (hβ : β ^ p = 1) (hout : ∀ a : K, MulAut.conj a ≠ β)
    (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.twistedE6 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q', hv'⟩).Group) := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K₂, _, σ, hK, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  set ℓ := q.p with hℓdef
  set f := q.exponent with hfdef
  have hℓ : ℓ.Prime := q.prime_p
  have hf : 1 ≤ f := q.exponent_pos
  let e' : K ≃* ↥(twistedE6RootGroup K₂ σ) := eK.trans eC
  set φ := MulAut.congr e' β with hφdef
  have hφp : φ ^ p = 1 := by rw [hφdef, ← map_pow, hβ, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K₂ hK σ hσ
  have hΘφ : Θ φ ≠ 1 := by
    intro hΘ1
    have hmem : φ ∈ twistedE6Inn K₂ σ ⊔ twistedE6Diag K₂ σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact hΘ1
    have hpg : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1) := fun h => by
      have h3 := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))
      omega
    obtain ⟨g, hg⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag hp hK hσ hpg hcube hφp
        hmem
    exact hout _ (conj_symm_eq_of_congr_eq_conj e' hg.symm)
  have hK' : Nat.card K₂ = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K₂ hK'
      σ hσ Θ hΘ hp hp2 φ hφp hΘφ
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK'
  obtain ⟨κ, hκ⟩ : ∃ κ : K₂ ≃+* K₂, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K₂ = ℓ ^ (2 * d * p) := by rw [hK', mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K₂) = (c : K₂) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by omega
  obtain ⟨-, hcardk, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K₂ hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K₂ σ.toRingHom with hC
  set N := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ) with hNdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  haveI : Finite (fixSubfield κ) := Subtype.finite
  have eNC : N.subgroupOf C ≃* N := Subgroup.subgroupOfEquivOfLe hJC
  haveI := hsimpleJ
  have hNs : IsSimpleGroup (N.subgroupOf C) := eNC.isSimpleGroup
  have hNn : ∃ x y : N.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eNC.symm a) (eNC.symm b)
    apply eNC.symm.injective
    rw [map_mul, map_mul]
    exact h
  let q' : TauCeti.PrimePower := ⟨ℓ, d, hℓ, hd1⟩
  have hv' : (TauCeti.LieTypeIndex.twistedE6 q').Valid := TauCeti.LieTypeIndex.valid_twistedE6 q'
  have hq'card : q'.card = ℓ ^ d := TauCeti.PrimePower.card_def q'
  have hcardk' : Nat.card (fixSubfield κ) = q'.card ^ 2 := by
    rw [hcardk, hq'card, ← pow_mul, mul_comm]
  have hσ₀k : ∀ c, (fixSubfieldRestrict T κ) c = c ^ q'.card := fun c =>
    Subtype.ext (by rw [hσ₀ c, hq'card]; rfl)
  obtain ⟨eCat⟩ := catEquiv_twistedE6_of_field q' hv' (fixSubfield κ) hcardk'
    (fixSubfieldRestrict T κ) hσ₀k
  let eXN : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom) ≃* ↥N :=
    (graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom).equivMapOfInjective
      (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)
  let eN : ↥(N.subgroupOf C) ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q', hv'⟩).Group :=
    (eNC.trans eXN.symm).trans eCat.symm
  have hδc : FixCompsEquiv δ (TauCeti.CFSGIndex.lie ⟨.twistedE6 q', hv'⟩).Group :=
    fixCompsEquiv_of_derived_eq_simple hder hNs hNn eN
  have hβc : FixCompsEquiv β (TauCeti.CFSGIndex.lie ⟨.twistedE6 q', hv'⟩).Group := by
    refine FixCompsEquiv.of_congr e' (FixCompsEquiv.of_pow_pow hrs
      (FixCompsEquiv.of_conj ψ ?_))
    rw [← hφdef, hψ]
    exact hδc
  have hZT : Subgroup.center (TauCeti.CFSGIndex.lie ⟨.twistedE6 q', hv'⟩).Group = ⊥ := by
    have h1 := Subgroup.map_center_eq eN
    rw [b3Lie_center_eq_bot hNn, Subgroup.map_bot] at h1
    exact h1.symm
  refine ⟨hβc.center_eq_bot hZT hJ, q', hv', ?_, hβc J hJ⟩
  rw [hq'card, ← pow_mul, TauCeti.PrimePower.card_def, ← hfdef, hdp]

end CFSG.LocalAnalysis.GLTheoremA.S2019
