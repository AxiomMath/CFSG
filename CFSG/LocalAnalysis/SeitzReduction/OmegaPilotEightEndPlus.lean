module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

section Abstract

variable {G : Type*} [Group G] [Finite G] {X Q : Type*} [Group X] [Group Q] [Finite Q]
  [IsCyclic Q]

theorem exists_normal_index_two_of_graphField_six {M : Subgroup G} (ρ : M →* MulAut X)
    (hker : Odd (Nat.card ρ.ker)) (hInn : ∀ g : X, ∃ m : M, ρ m = MulAut.conj g)
    (Φ : MulAut X →* Q) (hΦInn : ∀ g : X, Φ (MulAut.conj g) = 1)
    (s : Q →* MulAut X) (hs : ∀ c, Φ (s c) = c) (Γ : Subgroup (MulAut X))
    (hΓ : ∀ π ∈ Γ, Φ π = 1 ∧ π ^ 6 = 1 ∧ ∀ c, π * s c = s c * π)
    (hNF : ∀ α : MulAut X, ∃ g : X, ∃ π ∈ Γ, ∃ c : Q, α = MulAut.conj g * π * s c)
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2) (hts : ρ ⟨t, htM⟩ ∈ s.range)
    (hΦt : Φ (ρ ⟨t, htM⟩) ≠ 1) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup Q := IsCyclic.commGroup
  set α := ρ ⟨t, htM⟩ with hαdef
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hα2 : α ^ 2 = 1 := EPilot.action_sq_eq_one ρ htM ht2
  obtain ⟨ι, hι⟩ := hts
  have hΦα : Φ α = ι := by rw [← hι, hs]
  have hι1 : ι ≠ 1 := by rw [← hΦα]; exact hΦt
  have hι2 : ι ^ 2 = 1 := by rw [← hΦα, ← map_pow, hα2, map_one]
  set R := (Φ.comp ρ).range with hR
  have hιR : ι ∈ R := ⟨⟨t, htM⟩, by rw [MonoidHom.comp_apply, ← hαdef, hΦα]⟩
  have hιp : IsPGroup 2 (zpowers (⟨ι, hιR⟩ : R)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, pow_one]
    exact orderOf_eq_prime hι2 hι1
  obtain ⟨P', hP'⟩ := hιp.exists_le_sylow
  have hιP' : (⟨ι, hιR⟩ : R) ∈ (P' : Subgroup R) := hP' (mem_zpowers _)
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := (P' : Subgroup R))
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 P'.isPGroup'
  have hc₀o : orderOf c₀ = 2 ^ a := (orderOf_eq_card_of_forall_mem_zpowers hc₀).trans ha
  set c : Q := ((c₀ : R) : Q) with hcdef
  have hco : orderOf c = 2 ^ a := by
    rw [hcdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc₀o]
  have hRidx : ¬ 2 ^ (a + 1) ∣ Nat.card R := by
    intro hdvd
    rw [← (P' : Subgroup R).card_mul_index, ha, pow_succ] at hdvd
    exact P'.not_dvd_index (Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd)
  have ha1 : 1 ≤ a := by
    by_contra h0
    obtain rfl : a = 0 := by omega
    have hcard1 : Nat.card (P' : Subgroup R) = 1 := by rw [ha, pow_zero]
    have hsub : Subsingleton (P' : Subgroup R) := (Nat.card_eq_one_iff_unique.1 hcard1).1
    have h1 : (⟨_, hιP'⟩ : (P' : Subgroup R)) = 1 := Subsingleton.elim _ _
    exact hι1 (congrArg (fun z : (P' : Subgroup R) => ((z : R) : Q)) h1)
  set H : Subgroup M := (Φ.comp ρ).ker with hH
  have hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ H) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (Φ.comp ρ)).toEquiv]
    exact hRidx
  have hordQ : ∀ m : M, orderOf (QuotientGroup.mk' H m) = orderOf (Φ (ρ m)) := by
    intro m
    rw [← orderOf_injective _ (QuotientGroup.kerLift_injective (Φ.comp ρ))]
    change orderOf (QuotientGroup.kerLift (Φ.comp ρ) (m : M ⧸ (Φ.comp ρ).ker)) = _
    rw [QuotientGroup.kerLift_mk, MonoidHom.comp_apply]
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    obtain rfl : a = 1 := by omega
    have hxQ : orderOf (QuotientGroup.mk' H ⟨t, htM⟩) = 2 ^ 1 := by
      rw [hordQ, ← hαdef, hΦα, pow_one]
      exact orderOf_eq_prime hι2 hι1
    exact EPilot.exists_normal_index_two_of_unique_of_quotientSub H huniq htM le_rfl
      (by rw [ht, pow_one]) hxQ hQ (n := 1) (by rw [pow_one])
  obtain ⟨m, hm⟩ : c ∈ R := (c₀ : R).2
  set d : Q := c ^ 3 with hd
  have hdo : orderOf d = 2 ^ a := by
    rw [hd, Nat.Coprime.orderOf_pow, hco]
    rw [hco]
    exact Nat.Coprime.pow_left _ (by norm_num)
  have hzA : ∃ z ∈ ρ.range, Φ z = d ∧ z ^ 2 ^ (a - 1) = s (d ^ 2 ^ (a - 1)) ∧
      z ^ 2 ^ a = 1 := by
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by rw [← pow_succ]; congr 1; omega
    have hsda : s d ^ 2 ^ a = 1 := by rw [← map_pow, ← hdo, pow_orderOf_eq_one, map_one]
    obtain ⟨g, π, hπ, c', hgc⟩ := hNF (ρ m)
    obtain ⟨hΦπ, hπ6, hπs⟩ := hΓ π hπ
    have hc' : c' = c := by
      have h1 := congrArg Φ hgc
      rw [map_mul, map_mul, hΦInn, hΦπ, one_mul, one_mul, hs] at h1
      rw [← h1]
      exact hm
    rw [hc'] at hgc
    obtain ⟨m', hm'⟩ := hInn g
    have hz₀ : π * s c ∈ ρ.range :=
      ⟨m'⁻¹ * m, by rw [map_mul, map_inv, hm', hgc, mul_assoc, inv_mul_cancel_left]⟩
    have hcomm : Commute π (s c) := hπs c
    have hcomm' : Commute (π ^ 3) (s d) := by
      rw [hd, map_pow]
      exact hcomm.pow_pow 3 3
    have hπ3 : (π ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hπ6
    have hπpow : (π ^ 3) ^ 2 ^ (a - 1) = 1 := by
      obtain ⟨b, hb⟩ : ∃ b, a - 1 = b + 1 := ⟨a - 2, by omega⟩
      have h2b : 2 ^ (a - 1) = 2 * 2 ^ b := by rw [hb, pow_succ']
      rw [h2b, pow_mul, hπ3, one_pow]
    have hz : (π * s c) ^ 3 = π ^ 3 * s d := by rw [hcomm.mul_pow, hd, map_pow]
    refine ⟨π ^ 3 * s d, ?_, ?_, ?_, ?_⟩
    · rw [← hz]
      exact pow_mem hz₀ 3
    · rw [map_mul, map_pow, hΦπ, one_pow, one_mul, hs]
    · rw [hcomm'.mul_pow, hπpow, one_mul]
      exact (map_pow s d _).symm
    · rw [hcomm'.mul_pow, ← h2a, pow_mul, hπpow, one_pow, one_mul, h2a, hsda]
  obtain ⟨z, hzA, hΦz, hzpow, hz1⟩ := hzA
  have hdpow : d ^ 2 ^ (a - 1) = ι := by
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by rw [← pow_succ]; congr 1; omega
    refine EPilot.eq_of_sq_eq_one_of_ne_one_of_isCyclic ?_ hι2 ?_ hι1
    · rw [← pow_mul, h2a, ← hdo, pow_orderOf_eq_one]
    · intro h1
      have := orderOf_le_of_pow_eq_one (by positivity) h1
      rw [hdo] at this
      have : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  have hzo : orderOf z = 2 ^ a := by
    have hΦo : orderOf (Φ z) ∣ orderOf z := orderOf_map_dvd Φ z
    rw [hΦz, hdo] at hΦo
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hz1) hΦo
  obtain ⟨x, hxρ, hxo⟩ := LinearPilot.exists_orderOf_eq_of_odd_ker ρ hker hzA hzo
  have hxQ : orderOf (QuotientGroup.mk' H ⟨(x : G), x.2⟩) = 2 ^ a := by
    rw [hordQ, Subtype.coe_eta, hxρ, hΦz, hdo]
  have hxpowM : (x : G) ^ 2 ^ (a - 1) ∈ M := pow_mem x.2 _
  have hρx : ρ ⟨(x : G) ^ 2 ^ (a - 1), hxpowM⟩ = α := by
    have h1 : (⟨(x : G) ^ 2 ^ (a - 1), hxpowM⟩ : M) = x ^ 2 ^ (a - 1) := Subtype.ext (by simp)
    rw [h1, map_pow, hxρ, hzpow, hdpow, hι]
  have hxsq : ((x : G) ^ 2 ^ (a - 1)) ^ 2 = 1 := by
    rw [← pow_mul, show 2 ^ (a - 1) * 2 = 2 ^ a by rw [← pow_succ]; congr 1; omega,
      ← hxo, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  have hconj : IsConj t ((x : G) ^ 2 ^ (a - 1)) :=
    EPilot.isConj_of_action_eq ρ hker htM hxpowM ht2 hxsq hρx.symm
  exact EPilot.exists_normal_index_two_of_unique_of_quotientSub H huniq x.2 ha1
    (by rw [Subgroup.orderOf_coe, hxo]) hxQ hQ hconj

end Abstract

@[expose] def OmegaPlusFourAutNormalFormInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
    ∃ (Φ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) →* (F ≃+* F))
      (Γ : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))),
      (∀ g, Φ (MulAut.conj g) = 1) ∧ (∀ σ : F ≃+* F, Φ (fieldAutHom F 4 σ) = σ) ∧
      (∀ π ∈ Γ, Φ π = 1 ∧ π ^ 6 = 1 ∧
        ∀ σ : F ≃+* F, π * fieldAutHom F 4 σ = fieldAutHom F 4 σ * π) ∧
      ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)),
        ∃ g, ∃ π ∈ Γ, ∃ σ : F ≃+* F, α = MulAut.conj g * π * fieldAutHom F 4 σ

theorem omegaPlusFourEndInput_of_normalForm (hNF : OmegaPlusFourAutNormalFormInput) :
    OmegaPlusFourEndInput := by
  intro G _ _ L hset t ht hKt G₀ hLG htN F _ _ _ σ hσ ψ hψ huniq
  have : IsSimpleGroup G := hset.1
  obtain ⟨Φ, Γ, hΦInn, hΦs, hΓ, hform⟩ := hNF F
  obtain ⟨g, hg, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨σ₀, -, -, hzp, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hg hFc
  have : IsCyclic (F ≃+* F) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, hzp⟩
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  set ρ := normalizerMulAut ψ with hρ
  have hρt : ρ ⟨t, htN⟩ = fieldAutHom F 4 σ := hψ
  have hout : ρ ⟨t, htN⟩ ∉ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))).range := by
    rintro ⟨x, hx⟩
    apply hσ1
    rw [← hΦs σ, ← hρt, ← hx, hΦInn]
  have htZ : t ∉ centralizer (G₀ : Set G) := by
    intro htZ
    apply hout
    refine ⟨1, ?_⟩
    rw [map_one]
    refine MulEquiv.ext fun x => ?_
    apply ψ.symm.injective
    apply Subtype.ext
    rw [F4Pilot.coe_symm_normalizerMulAut_apply, MulAut.one_apply]
    have hc := mem_centralizer_iff.1 htZ ((ψ.symm x : G₀) : G) (ψ.symm x).2
    change ((ψ.symm x : G₀) : G) = t * ((ψ.symm x : G₀) : G) * t⁻¹
    rw [← hc, mul_inv_cancel_right]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG ht htN htZ
  have hker : Odd (Nat.card ρ.ker) := by
    rw [hρ, EPilot.card_ker_normalizerMulAut]
    exact hZ
  have htG : t ∉ G₀ := EPilot.not_mem_of_normalizerMulAut_not_mem_range ψ htN hout
  apply CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG)
  refine exists_normal_index_two_of_graphField_six ρ hker
    (EPilot.exists_normalizerMulAut_eq_conj ψ) Φ hΦInn (fieldAutHom F 4) hΦs Γ hΓ
    (fun α => ?_) htN ht ⟨σ, hρt.symm⟩ (by rw [hρt, hΦs]; exact hσ1) huniq
  obtain ⟨x, π, hπ, τ, h⟩ := hform α
  exact ⟨x, π, hπ, τ, h⟩

end CFSG.SeitzReduction.OmegaPilot
