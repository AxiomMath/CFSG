module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78MaxAlt
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps

public section

namespace CFSG.ComponentClassification.Sol78H

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X]

theorem isKBalanced_of_two_alt {N K₁ K₂ : Subgroup X} {n₁ n₂ : ℕ} (hn₁ : 8 ≤ n₁) (hn₂ : 8 ≤ n₂)
    (h₁ : FooteLit.IsTwoComponentIn K₁ N) (h₂ : FooteLit.IsTwoComponentIn K₂ N)
    (hs₁ : K₁ ∈ FooteLit.solomonKStar X) (hs₂ : K₂ ∈ FooteLit.solomonKStar X) (hne : K₁ ≠ K₂)
    (e₁ : K₁ ⧸ pPrimeCore 2 K₁ ≃* alternatingGroup (Fin n₁))
    (e₂ : K₂ ⧸ pPrimeCore 2 K₂ ≃* alternatingGroup (Fin n₂)) : FooteLit.IsKBalanced N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr₁ : 3 ≤ CFSG.pRank 2 K₁ := Sol78.three_le_pRank_of_coreQuotient hn₁ e₁
  have hr₂ : 3 ≤ CFSG.pRank 2 K₂ := Sol78.three_le_pRank_of_coreQuotient hn₂ e₂
  set S : Set (Subgroup X) := {K | FooteLit.IsTwoComponentIn K N ∧ K ∈ FooteLit.solomonKStar X}
    with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hK₁s : K₁ ∈ s := hSfin.mem_toFinset.mpr ⟨h₁, hs₁⟩
  have hK₂s : K₂ ∈ s := hSfin.mem_toFinset.mpr ⟨h₂, hs₂⟩
  have hr : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨K₁, hK₁s, K₂, hK₂s, hne⟩
  set ee := s.equivFin.symm with hee
  set Kf : Fin s.card → Subgroup X := fun i => ((ee i : s) : Subgroup X) with hKf
  have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (ee i).2
  refine ⟨s.card, Kf, fun i j hij => ee.injective (Subtype.ext hij), fun K => ⟨fun hK => ?_, ?_⟩,
    hr, fun i j hij => ?_, ?_, ?_⟩
  · refine ⟨ee.symm ⟨K, hSfin.mem_toFinset.mpr hK⟩, ?_⟩
    simp only [hKf, Equiv.apply_symm_apply]
  · rintro ⟨i, rfl⟩
    exact hKfS i
  · exact FooteLit.commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
      (fun h => hij (ee.injective (Subtype.ext h)))
  ·
    refine ⟨ee.symm ⟨K₁, hK₁s⟩, ?_⟩
    have hKi : Kf (ee.symm ⟨K₁, hK₁s⟩) = K₁ := by simp only [hKf, Equiv.apply_symm_apply]
    rw [hKi]
    have hle : K₂ ≤ (FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N) ⊓ coreActionKernel K₁ :=
      le_inf ((FooteLit.le_twoLayerIn_of_isTwoComponentIn h₂).trans le_sup_right)
        (GSThmB.B5a.le_coreActionKernel_of_ne h₁.1 h₂.1 h₁.2 h₂.2 hne)
    exact hr₂.trans (Sol78.pRank_le_of_le hle)
  ·
    by_cases h3 : 3 ≤ s.card
    · exact Or.inl h3
    · right; right
      have hsub : ({K₁, K₂} : Finset (Subgroup X)) ⊆ s := by
        intro K hK
        rw [Finset.mem_insert, Finset.mem_singleton] at hK
        rcases hK with rfl | rfl
        · exact hK₁s
        · exact hK₂s
      have hseq : ({K₁, K₂} : Finset (Subgroup X)) = s :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)
      have hgood : ∀ i, 3 ≤ CFSG.pRank 2 ↥(Kf i) ∧ ¬ FooteLit.HasStronglyEmbedded ↥(Kf i) := by
        intro i
        have hi : Kf i ∈ ({K₁, K₂} : Finset (Subgroup X)) := by rw [hseq]; exact (ee i).2
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with hi | hi
        · rw [hi]
          exact ⟨hr₁, Sol78.not_hasStronglyEmbedded_of_coreQuotient hn₁ e₁⟩
        · rw [hi]
          exact ⟨hr₂, Sol78.not_hasStronglyEmbedded_of_coreQuotient hn₂ e₂⟩
      exact ⟨(hgood _).1, (hgood _).1, fun h => (h.elim (hgood _).2 (hgood _).2).elim⟩

theorem false_of_two_alt (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    {N K₁ K₂ : Subgroup X} {n₁ n₂ : ℕ} (hn₁ : 8 ≤ n₁) (hn₂ : 8 ≤ n₂)
    (h₁ : FooteLit.IsTwoComponentIn K₁ N) (h₂ : FooteLit.IsTwoComponentIn K₂ N)
    (hs₁ : K₁ ∈ FooteLit.solomonKStar X) (hs₂ : K₂ ∈ FooteLit.solomonKStar X) (hne : K₁ ≠ K₂)
    (e₁ : K₁ ⧸ pPrimeCore 2 K₁ ≃* alternatingGroup (Fin n₁))
    (e₂ : K₂ ⧸ pPrimeCore 2 K₂ ≃* alternatingGroup (Fin n₂)) : False :=
  h13 X inferInstance hna hK N (isKBalanced_of_two_alt hn₁ hn₂ h₁ h₂ hs₁ hs₂ hne e₁ e₂)

theorem mem_solomonKStar_of_member (hmax : Sol78.MaximalityLemmaInput)
    (hS : SolAltLit.SchurAlternatingMultiplierInput) [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : Odd n) (hn9 : 9 ≤ n)
    (hex : ∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) {L : Subgroup X} (hL : FooteLit.IsSolomonMember L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n)) : L ∈ FooteLit.solomonKStar X := by
  refine ⟨hmax X hna hK hz hU n hn hn9 hex hmaxdeg L hL ⟨e⟩, ?_⟩
  obtain ⟨e'⟩ := Sol78.nonempty_fusionZStar_equiv_of_coreQuotient (by omega) e
  exact Sol76.isSolomonWide_of_fusionZStar hS hL (by omega) e'

theorem eq_of_isTwoComponentIn_alt_of_member (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : Odd n) (hn9 : 9 ≤ n)
    (hex : ∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) {Y L₁ L₂ : Subgroup X} (h₁ : FooteLit.IsTwoComponentIn L₁ Y)
    (h₂ : FooteLit.IsTwoComponentIn L₂ Y) (hm₁ : FooteLit.IsSolomonMember L₁)
    (hm₂ : FooteLit.IsSolomonMember L₂)
    (e₁ : Nonempty (L₁ ⧸ pPrimeCore 2 L₁ ≃* alternatingGroup (Fin n)))
    (e₂ : Nonempty (L₂ ⧸ pPrimeCore 2 L₂ ≃* alternatingGroup (Fin n))) : L₁ = L₂ := by
  by_contra hne
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  exact false_of_two_alt h13 hna hK (by omega) (by omega) h₁ h₂
    (mem_solomonKStar_of_member hmax hS hna hK hz hU hn hn9 hex hmaxdeg hm₁ e₁)
    (mem_solomonKStar_of_member hmax hS hna hK hz hU hn hn9 hex hmaxdeg hm₂ e₂) hne e₁ e₂

theorem eq_of_isTwoComponentIn_centralizer_alt (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : Odd n) (hn9 : 9 ≤ n)
    (hex : ∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) {T L₁ L₂ : Subgroup X} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (h₁ : FooteLit.IsTwoComponentIn L₁ (centralizer (T : Set X)))
    (h₂ : FooteLit.IsTwoComponentIn L₂ (centralizer (T : Set X)))
    (e₁ : Nonempty (L₁ ⧸ pPrimeCore 2 L₁ ≃* alternatingGroup (Fin n)))
    (e₂ : Nonempty (L₂ ⧸ pPrimeCore 2 L₂ ≃* alternatingGroup (Fin n))) : L₁ = L₂ :=
  eq_of_isTwoComponentIn_alt_of_member h13 hmax hS hna hK hz hU hn hn9 hex hmaxdeg h₁ h₂
    (Sol76.isSolomonMember_of_isTwoComponentIn hT hT2 h₁)
    (Sol76.isSolomonMember_of_isTwoComponentIn hT hT2 h₂) e₁ e₂

omit [Finite X] in
theorem mem_normalizer_centralizer {S : Subgroup X} {h : X}
    (hh : h ∈ normalizer (S : Set X)) : h ∈ normalizer (centralizer (S : Set X) : Set X) := by
  have key : ∀ g ∈ normalizer (S : Set X), ∀ x ∈ centralizer (S : Set X),
      g * x * g⁻¹ ∈ centralizer (S : Set X) := by
    intro g hg x hx
    rw [mem_centralizer_iff] at hx ⊢
    intro s hs
    have h1 : g⁻¹ * s * g⁻¹⁻¹ ∈ S := (mem_normalizer_iff.mp (inv_mem hg) s).mp hs
    have h2 := hx _ h1
    calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g⁻¹⁻¹)) * g⁻¹ := by rw [h2]
      _ = g * x * g⁻¹ * s := by group
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key h hh x
  · intro hx
    have h1 := key h⁻¹ (inv_mem hh) _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h1

theorem normalizer_le_normalizer_of_isTwoComponentIn_centralizer_alt
    (h13 : Sol76T13.SolomonThm13Simple) (hmax : Sol78.MaximalityLemmaInput)
    (hS : SolAltLit.SchurAlternatingMultiplierInput) [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : Odd n) (hn9 : 9 ≤ n)
    (hex : ∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) {T L : Subgroup X} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hL : FooteLit.IsTwoComponentIn L (centralizer (T : Set X)))
    (eL : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))) :
    normalizer (T : Set X) ≤ normalizer (L : Set X) := by
  intro g hg
  have hgC : g ∈ normalizer (centralizer (T : Set X) : Set X) := mem_normalizer_centralizer hg
  have hLg : FooteLit.IsTwoComponentIn (L.map (MulAut.conj g).toMonoidHom)
      (centralizer (T : Set X)) := Sol76.isTwoComponentIn_map_conj hL hgC
  obtain ⟨φ⟩ := eL
  have eLg : Nonempty ((L.map (MulAut.conj g).toMonoidHom) ⧸
      pPrimeCore 2 (L.map (MulAut.conj g).toMonoidHom) ≃* alternatingGroup (Fin n)) :=
    ⟨(Sol78.coreQuotCongr (L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).symm.trans φ⟩
  have h := eq_of_isTwoComponentIn_centralizer_alt h13 hmax hS hna hK hz hU hn hn9 hex hmaxdeg
    hT hT2 hLg hL eLg ⟨φ⟩
  exact mem_normalizer_iff_map_conj_eq.mpr h

end CFSG.ComponentClassification.Sol78H
