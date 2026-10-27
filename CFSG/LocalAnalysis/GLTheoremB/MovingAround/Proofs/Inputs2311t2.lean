module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311t
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311r

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311t

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

set_option linter.unusedSectionVars false

section Residual

@[expose] def TriXNoGCentUniPlanes :
    Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (E : Subgroup (MulAut (C0 σ))) (x : C0 σ), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (C0 σ) → ¬ TriOddHasGLine σ E →
      (∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E, α * γ = γ * α) →
      x ^ 3 = 1 → x ≠ 1 → MulAut.conj x ∈ E → TriOddIsClassX σ x →
      (∀ ψ : MulAut (C0 σ), ¬ ∀ φ ∈ E.map (MulAut.congr ψ).toMonoidHom,
        ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
          (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
        ((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
          (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →
      uniPlaneClosure ℓ E = ⊤

end Residual

section Reduction

variable {X : Type} [Field X] [Finite X]

theorem exists_tau_model_of_hasGLine_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) (hgl : TriOddHasGLine σ E) :
    ∃ ψ : MulAut (C0 σ), tauAut σ ∈ E.map (MulAut.congr ψ).toMonoidHom ∧
      ((∃ b ∈ Bsub σ, b ≠ 1 ∧ MulAut.conj b ∈ E.map (MulAut.congr ψ).toMonoidHom) ∨
        ∃ a ∈ Asub σ, a ≠ 1 ∧ a ^ 3 = 1 ∧ tauAut σ a = a ∧
          MulAut.conj a ∈ E.map (MulAut.congr ψ).toMonoidHom) := by
  classical
  obtain ⟨β, hβE, φ, hφ⟩ := hgl
  obtain ⟨hE₂, hcard₂, hout₂⟩ := triOdd_map_congr_plane σ φ E hE hcard hout
  obtain ⟨β₀, hβ₀E, hβ₀⟩ : ∃ β₀ ∈ E, (MulAut.congr φ) β₀ = tauAut σ := by
    rcases hφ with h | h
    · exact ⟨β, hβE, by rw [congr_apply_eq, h]⟩
    · refine ⟨β⁻¹, inv_mem hβE, ?_⟩
      rw [map_inv, congr_apply_eq, h, inv_inv]
  have hτ₂ : tauAut σ ∈ E.map (MulAut.congr φ).toMonoidHom := ⟨β₀, hβ₀E, hβ₀⟩
  obtain ⟨x, hx3, hx1, hτx, hE₂eq⟩ :=
    triOdd_exists_plane_with_tau σ hℓ hℓ2 hf hX hσ _ hE₂ hcard₂ hout₂ hτ₂
  have hcx₂ : MulAut.conj x ∈ E.map (MulAut.congr φ).toMonoidHom := by
    rw [hE₂eq]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨α₁, hα₁E, hα₁⟩ := hcx₂
  have hα₁' : (MulAut.congr φ) α₁ = MulAut.conj x := hα₁
  obtain ⟨y, hyG, hy⟩ :=
    exists_gsub_conj_mem_Bsub_or_Asub_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ hτx hx3 hx1
  have hτy : tauAut σ y = y := hyG
  set ψ : MulAut (C0 σ) := MulAut.conj y * φ with hψ
  have hmap : ∀ α, (MulAut.congr ψ) α =
      MulAut.conj y * (MulAut.congr φ) α * (MulAut.conj y)⁻¹ := by
    intro α
    rw [congr_apply_eq, congr_apply_eq, hψ]
    group
  have hyτ : MulAut.conj y * tauAut σ * (MulAut.conj y)⁻¹ = tauAut σ := by
    refine MulEquiv.ext fun z => ?_
    have h3 : (MulAut.conj y)⁻¹ z = y⁻¹ * z * y := by rw [← map_inv, MulAut.conj_apply, inv_inv]
    rw [MulAut.mul_apply, MulAut.mul_apply, h3, MulAut.conj_apply, map_mul, map_mul, map_inv, hτy]
    group
  have hτψ : tauAut σ ∈ E.map (MulAut.congr ψ).toMonoidHom :=
    ⟨β₀, hβ₀E, by show (MulAut.congr ψ) β₀ = _; rw [hmap, hβ₀, hyτ]⟩
  have hxψ : MulAut.conj (y * x * y⁻¹) ∈ E.map (MulAut.congr ψ).toMonoidHom :=
    ⟨α₁, hα₁E, by
      show (MulAut.congr ψ) α₁ = _
      rw [hmap, hα₁', aut_conj_conj, MulAut.conj_apply]⟩
  have hx'1 : y * x * y⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [e, h]
    group
  refine ⟨ψ, hτψ, ?_⟩
  rcases hy with hB | hA
  · exact Or.inl ⟨_, hB, hx'1, hxψ⟩
  · refine Or.inr ⟨_, hA, hx'1, by rw [conj_pow, hx3]; group, ?_, hxψ⟩
    rw [map_mul, map_mul, map_inv, hτy, hτx]

theorem not_hasGLine_of_not_tauModel_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) {G : Type*} [Group G] (e : G ≃* C0 σ)
    (E : Subgroup (MulAut G))
    (hE : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom))
    (hcard : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2)
    (hout : ¬ E.map (MulAut.congr e).toMonoidHom ≤ innerAut (C0 σ))
    (hnτ : ¬ ∃ e' : G ≃* C0 σ, tauAut σ ∈ E.map (MulAut.congr e').toMonoidHom ∧
      ((∃ b ∈ Bsub σ, b ≠ 1 ∧ MulAut.conj b ∈ E.map (MulAut.congr e').toMonoidHom) ∨
        ∃ a ∈ Asub σ, a ≠ 1 ∧ a ^ 3 = 1 ∧ tauAut σ a = a ∧
          MulAut.conj a ∈ E.map (MulAut.congr e').toMonoidHom)) :
    ¬ TriOddHasGLine σ (E.map (MulAut.congr e).toMonoidHom) := by
  intro hgl
  obtain ⟨ψ, hτ, hba⟩ :=
    exists_tau_model_of_hasGLine_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ _ hE hcard hout hgl
  apply hnτ
  have hsub : (E.map (MulAut.congr e).toMonoidHom).map (MulAut.congr ψ).toMonoidHom ≤
      E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
    rintro _ ⟨_, ⟨φ₀, hφ₀, rfl⟩, rfl⟩
    exact ⟨φ₀, hφ₀, Inputs2311k.mulAut_congr_trans_excD4 e ψ φ₀⟩
  refine ⟨e.trans ψ, hsub hτ, ?_⟩
  rcases hba with ⟨b, hb, hb1, hbE⟩ | ⟨a, ha, ha1, ha3, hτa, haE⟩
  · exact Or.inl ⟨b, hb, hb1, hsub hbE⟩
  · exact Or.inr ⟨a, ha, ha1, ha3, hτa, hsub haE⟩

theorem d4PlanesRest3Tri_of_triXNoGCentUni (h : TriXNoGCentUniPlanes) : Inputs2311r.D4PlanesRest3Tri := by
  classical
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨⟨hR, hcase⟩, hin, -, -, hbp, q, hq⟩
  obtain rfl : d = .trialityD4 q := hq
  rcases hcase with ⟨-, -, ⟨q', hq'⟩, -⟩ | ⟨hin', -⟩ | ⟨-, hp3, -, hnτ⟩
  · cases hq'
  · exact absurd hin' hin
  subst hp3
  have hchar : (TauCeti.LieTypeIndex.trialityD4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_trialityD4]
  have hch2 : (TauCeti.LieTypeIndex.trialityD4 q).characteristic ≠ 2 := hR.1.1
  have hq2 : q.p ≠ 2 := fun h2 => hch2 (by rw [hchar, h2])
  have hq3 : q.p ≠ 3 := fun h3 => hpd (by rw [hchar, h3])
  have hℓ := q.prime_p
  have hf := q.exponent_pos
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  have hE'ea : CFSG.IsElementaryAbelian 3 E' :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card E' = 3 ^ 2 := by rw [hE', card_map_congr, hc]
  have hout' : ¬ E' ≤ innerAut (C0 σ) := by
    intro hle
    apply hin
    intro φ hφ
    obtain ⟨g, hg⟩ := hle (Subgroup.mem_map_of_mem _ hφ)
    refine ⟨e.symm g, ?_⟩
    have h1 : (MulAut.congr e).toMonoidHom (MulAut.conj (e.symm g)) =
        (MulAut.congr e).toMonoidHom φ := by
      rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hg]
    exact (MulAut.congr e).injective h1
  have hnG : ¬ TriOddHasGLine σ E' := by
    refine not_hasGLine_of_not_tauModel_inputs2311t hℓ hq2 hq3 hf hK σ hσ e E hE'ea hc' hout' ?_
    rintro ⟨e', hτ, hba⟩
    exact hnτ ⟨q, rfl, K, inferInstance, inferInstance, σ, hK, hσ, e', hτ, hba⟩
  rw [hchar]
  refine (uniPlaneGen_map_congr e q.p E).1 ?_
  show uniPlaneClosure q.p E' = ⊤
  by_cases hcent : ∃ γ : MulAut (C0 σ), TriOddIsGLine σ γ ∧ ∀ α ∈ E', α * γ = γ * α
  · obtain ⟨γ, hγ, hγc⟩ := hcent
    exact uniPlaneClosure_eq_top_of_central_gline_inputs2311t hℓ hq2 hq3 hf hK σ hσ E' hE'ea hc'
      hout' hγ hγc (fun hγE => hnG ⟨γ, hγE, hγ⟩)
  push Not at hcent
  have hncent : ∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E', α * γ = γ * α := by
    intro γ hγ hall
    obtain ⟨α, hα, hne⟩ := hcent γ hγ
    exact hne (hall α hα)
  obtain ⟨x, hx3, hx1, _g, _e, -, -, -, hEeq⟩ :=
    triOdd_plane_shape σ hℓ hq2 hf hK hσ E' hE'ea hc' hout'
  have hcx : MulAut.conj x ∈ E' := by
    rw [hEeq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have h3q : ¬ 3 ∣ q.p ^ q.exponent := fun h3 => hq3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three
    hℓ).1 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)).symm)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds K (q.p ^ q.exponent) σ
    hK hσ h3q x hx3 hx1
  have hX : TriOddIsClassX σ x := by
    rcases hg with hA | hB
    · exact ⟨g, hA⟩
    · exact absurd (triOddYGLine q.p q.exponent hℓ hq2 hq3 hf K hK σ hσ E' x hE'ea hc' hout' hx3
        hx1 hcx ⟨g, hB⟩) hnG
  have hbp' : ∀ ψ : MulAut (C0 σ), ¬ ∀ φ ∈ E'.map (MulAut.congr ψ).toMonoidHom,
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
        (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    intro ψ hall
    apply hbp
    refine ⟨q, rfl, K, inferInstance, inferInstance, σ, hK, e.trans ψ, ?_⟩
    rintro _ ⟨φ₀, hφ₀, rfl⟩
    refine hall _ ⟨(MulAut.congr e).toMonoidHom φ₀, Subgroup.mem_map_of_mem _ hφ₀, ?_⟩
    exact (Inputs2311k.mulAut_congr_trans_excD4 e ψ φ₀).symm
  exact h q.p q.exponent hℓ hq2 hq3 hf K hK σ hσ E' x hE'ea hc' hout' hnG hncent hx3 hx1 hcx hX hbp'

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311t
