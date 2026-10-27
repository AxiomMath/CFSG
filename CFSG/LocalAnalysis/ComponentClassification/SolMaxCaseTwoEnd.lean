module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCaseTwoLift
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma21
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36O

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerCaseTwoWInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ (M : Subgroup X) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 4)))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 4))), IsPermAction θ ρ →
      M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      (∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
        g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) →
      (∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)), x * x = 1 →
        (ρ ⟨x, hHN hx⟩).support.card = 4 →
          centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ g : X, g * t * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X) →
        g ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∃ P : Sylow 2 X, (P : Subgroup X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      ∀ g : X, g * t * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X) →
        g * t * g⁻¹ ≠ t → t * (g * t * g⁻¹) = g * t * g⁻¹ * t →
        (∀ c : X, c * t * c⁻¹ ≠ t * (g * t * g⁻¹)) →
          centralizer ({t * (g * t * g⁻¹)} : Set X) ≤
            normalizer (Sol78.signalizerCompletion E E : Set X)

theorem signalizerCaseTwoFinishInput_of_w (h33 : Sol78.BalanceLemmaInput)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hW : SignalizerCaseTwoWInput) :
    SignalizerCaseTwoFinishInput := by
  intro X _ _ _ t J n e E D S hWne M θ ρ hρ hMH hMpc hJM hHN hk hA4 hfus hSyl
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have htord : orderOf t = 2 := S.pair.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← htord, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    omega
  have htH : t ∈ H := CaseTwo.mem_of_conj_mem_of_sylow htord hfus hSyl
  have ht4 : (ρ ⟨t, hHN htH⟩).support.card = 4 :=
    S.card_support_t_of_add_four hT13 hML hSch hMH hMpc (hHN htH) hJM hρ
  have hHtop : H ≠ ⊤ := S.normalizer_completion_ne_top h33 hWne
  have hCt : ∀ c ∈ centralizer ({t} : Set X), c ∈ H := fun c hc => hfus c (by
    rw [show c * t * c⁻¹ = t by rw [mem_centralizer_singleton_iff.mp hc]; group]
    exact htH)
  have hfixt : ∃! ω : X ⧸ H, t • ω = ω := by
    refine CaseTwo.existsUnique_fixed htH fun g hg => ?_
    have h1 := hfus g⁻¹ (by rwa [inv_inv])
    simpa using H.inv_mem h1
  have hprod : ∀ z₁ z₂ : X, IsConj t z₁ → IsConj t z₂ → z₁ ≠ z₂ → Commute z₁ z₂ →
      ∃! ω : X ⧸ H, (z₁ * z₂) • ω = ω := by
    intro z₁ z₂ h1 h2 hne hcomm
    obtain ⟨a, ha⟩ := isConj_iff.mp h1
    obtain ⟨b, hb⟩ := isConj_iff.mp h2
    set g := a⁻¹ * b with hgdef
    have ht' : g * t * g⁻¹ = a⁻¹ * z₂ * a := by rw [← hb, hgdef]; group
    have hzz : z₁ * z₂ = a * (t * (g * t * g⁻¹)) * a⁻¹ := by rw [ht', ← ha]; group
    have hcomm' : t * (g * t * g⁻¹) = g * t * g⁻¹ * t := by
      have h := hcomm.eq
      rw [ht']
      calc t * (a⁻¹ * z₂ * a) = a⁻¹ * (a * t * a⁻¹) * z₂ * a := by group
        _ = a⁻¹ * (z₁ * z₂) * a := by rw [ha]; group
        _ = a⁻¹ * (z₂ * z₁) * a := by rw [h]
        _ = a⁻¹ * z₂ * a * (a⁻¹ * z₁ * a) := by group
        _ = a⁻¹ * z₂ * a * t := by rw [← ha]; group
    have hne' : g * t * g⁻¹ ≠ t := by
      intro h
      apply hne
      rw [← ha, ← hb]
      calc a * t * a⁻¹ = a * (g * t * g⁻¹) * a⁻¹ := by rw [h]
        _ = b * t * b⁻¹ := by rw [hgdef]; group
    have ht'H : g * t * g⁻¹ ∈ H :=
      hCt _ (mem_centralizer_singleton_iff.mpr hcomm'.symm)
    have hwH : t * (g * t * g⁻¹) ∈ H := H.mul_mem htH ht'H
    have hw2 : t * (g * t * g⁻¹) * (t * (g * t * g⁻¹)) = 1 := by
      calc t * (g * t * g⁻¹) * (t * (g * t * g⁻¹)) =
          t * (g * t * g⁻¹ * t) * (g * t * g⁻¹) := by group
        _ = t * (t * (g * t * g⁻¹)) * (g * t * g⁻¹) := by rw [hcomm']
        _ = (t * t) * (g * (t * t) * g⁻¹) := by group
        _ = 1 := by rw [ht2]; group
    have hw : ∀ c : X, c⁻¹ * (t * (g * t * g⁻¹)) * c ∈ H → c ∈ H := by
      by_cases hconj : ∃ d : X, d * t * d⁻¹ = t * (g * t * g⁻¹)
      · obtain ⟨d, hd⟩ := hconj
        have hdH : d ∈ H := hfus d (by rw [hd]; exact hwH)
        intro c hc
        have h3 : c⁻¹ * d ∈ H := by
          refine hfus _ ?_
          rw [show c⁻¹ * d * t * (c⁻¹ * d)⁻¹ = c⁻¹ * (d * t * d⁻¹) * c by group, hd]
          exact hc
        have h4 := H.mul_mem hdH (H.inv_mem h3)
        rwa [show d * (c⁻¹ * d)⁻¹ = c by group] at h4
      · push Not at hconj
        have hCw := hW X t J n e E D S hWne M θ ρ hρ hMH hMpc hJM hHN hk hA4 hfus hSyl g ht'H
          hne' hcomm' hconj
        intro c hc
        exact hρ.mem_of_conj_mem_of_centralizer_le (by omega) hMH hHN hk htH ht2 ht4 hfus hw2
          hCw hc
    rw [hzz]
    exact CaseTwo.existsUnique_fixed_conj a (CaseTwo.existsUnique_fixed hwH hw)
  have hO : Open.standardComponentOddCore X = ⊥ := by
    unfold Open.standardComponentOddCore
    refine sSup_eq_bot.mpr fun N hN => ?_
    obtain ⟨hNn, hNodd⟩ := hN
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hNodd
      have h2 := orderOf_dvd_natCard t
      rw [htord] at h2
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
  have h21 := Asc76X.asc76Lemma21 X H t hO hHtop htH htord hfixt hprod
  obtain ⟨-, -, -, -, -, -, hse, -⟩ := h21
  have hL : normalClosure ({t} : Set X) = ⊤ := by
    rw [← Asc76X.involutionPointHull_eq_normalClosure]
    exact ProperTwoGeneratedCore.Assembly.involutionPointHull_eq_top ht1
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ with
      h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := S.nonab
      have ha := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) (mem_top a)
      exact hab (mem_centralizer_iff.mp ha b (mem_top b)).symm
    · exact h
  rw [hL, hcomm] at hse
  have hSE : CFSG.IsStronglyEmbedded H :=
    ProperTwoGeneratedCore.Assembly.fusionStronglyEmbedded_of_subgroupOf_top hse
  obtain ⟨y, hyM, hy2, hy8⟩ := hρ.exists_eight_involution (by omega)
  obtain ⟨c, hc⟩ := isConj_iff.mp (Sol78.isConj_of_isStronglyEmbedded hSE htord hy2)
  have hcH : c ∈ H := hfus c (by rw [hc]; exact hMH hyM)
  have hρy : ρ ⟨y, le_normalizer hyM⟩ =
      ρ ⟨c, hHN hcH⟩ * ρ ⟨t, hHN htH⟩ * (ρ ⟨c, hHN hcH⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc.symm
  rw [hρy, Perm.card_support_conj, ht4] at hy8
  omega

end CFSG.ComponentClassification.SolMax
