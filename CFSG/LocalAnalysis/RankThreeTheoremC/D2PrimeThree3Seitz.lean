module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SeitzRest3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3
import CFSG.RankThree.PartTwo.KFacts.K71L28Cent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open scoped MatrixGroups
open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore primeComplementCore_coprime
  rank_two_has_coordinate_embedding embedded_rank_two_signalizer_le_of_line_centralizers
  coordinatePairLineHom)

variable {G : Type} [Group G] [Finite G]

theorem psl28_eq_bot_of_commute_aut {ε : MulAut PSL(2, GaloisField 2 3)} (hε3 : ε ^ 3 = 1)
    (hε1 : ε ≠ 1) {N : Subgroup (MulAut PSL(2, GaloisField 2 3))}
    (hNc : ∀ ν ∈ N, ν * ε = ε * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, ε ℓ = ℓ → ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) : N = ⊥ := by
  by_cases hD : ε ∈ (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction
    (GaloisField 2 3)).range
  · obtain ⟨g, rfl⟩ := hD
    obtain ⟨s, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.toPGL_surjective_psl28 g
    rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL] at hε3 hε1 hNc
    have hs3 : s ^ 3 = 1 := by
      rw [← map_pow] at hε3
      exact CFSG.RankThree.PartTwo.KFacts.eq_one_of_conj_eq_one_psl28 hε3
    have hs1 : s ≠ 1 := fun h => hε1 (by rw [h, map_one])
    exact CFSG.RankThree.PartTwo.KFacts.psl28_eq_bot_of_commute_conj hs3 hs1 hNc hN3
  · have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hε1
    obtain ⟨σ, hσ, g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent
      Nat.prime_three ε hεo hD
    exact CFSG.RankThree.PartTwo.KFacts.eq_bot_of_conj hg
      (fun N₁ hc₁ h₁ hn₁ =>
        CFSG.RankThree.PartTwo.KFacts.psl28_eq_bot_of_commute_field hσ hc₁ h₁ hn₁) hNc hN3 hNn

section Core

variable {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}

theorem inf_centralizer_eq_bot_of_psl28 (h : D2AlmostSimple 3 X R A X₀ K)
    (e : K ≃* PSL(2, GaloisField 2 3)) {W : Subgroup X}
    (hWn : X₀ ≤ Subgroup.normalizer (W : Set X)) (hW3 : ¬ 3 ∣ Nat.card W) {a : X} (haA : a ∈ A)
    (ha1 : a ≠ 1) : W ⊓ Subgroup.centralizer ({a} : Set X) = ⊥ := by
  have hKn := h.normal
  let ψ : X →* MulAut PSL(2, GaloisField 2 3) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψapp : ∀ (x : X) (y : PSL(2, GaloisField 2 3)),
      ((e.symm (ψ x y) : K) : X) = x * (e.symm y : X) * x⁻¹ := by
    intro x y
    simp [ψ, MulAut.congr_apply, MulAut.conjNormal_apply]
  have hψinj : Function.Injective ψ := by
    refine (MulAut.congr e).injective.comp ?_
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer K, h.centralizer_eq_bot]
  have hψconj : ∀ ℓ : PSL(2, GaloisField 2 3), ψ (e.symm ℓ : X) = MulAut.conj ℓ := by
    intro ℓ
    ext y
    apply e.symm.injective
    apply Subtype.ext
    rw [hψapp]
    simp
  have ha3 : a ^ 3 = 1 := h.elem.2 a haA
  have haX₀ : ∀ k : X, k * a = a * k → k ∈ X₀ := by
    intro k hk
    refine h.normalizer_le_of_le_A (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA) ?_
      (CFSG.AGLEmbeddingD2.centralizer_singleton_le_normalizer_zpowers a
        (Subgroup.mem_centralizer_singleton_iff.mpr hk))
    rwa [Ne, Subgroup.zpowers_eq_bot]
  have hN := psl28_eq_bot_of_commute_aut (ε := ψ a)
    (N := (W ⊓ Subgroup.centralizer ({a} : Set X)).map ψ)
    (by rw [← map_pow, ha3, map_one]) (fun h1 => ha1 (hψinj (by rw [h1, map_one]))) ?_ ?_ ?_
  · exact (Subgroup.map_eq_bot_iff_of_injective _ hψinj).mp hN
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
  · rw [Subgroup.card_map_of_injective hψinj]
    exact fun hd => hW3 (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  · intro ℓ hℓ ν hν
    obtain ⟨w, hw, rfl⟩ := hν
    set k : X := (e.symm ℓ : X) with hk
    have hka : k * a = a * k := by
      have h1 := congrArg (fun z : PSL(2, GaloisField 2 3) => ((e.symm z : K) : X)) hℓ
      simp only [hψapp] at h1
      calc k * a = a * k * a⁻¹ * a := by rw [h1]
        _ = a * k := by group
    have hkX₀ : k ∈ X₀ := haX₀ k hka
    refine ⟨k * w * k⁻¹, ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hWn hkX₀) w).mp hw.1
    · have hwa : Commute w a := Subgroup.mem_centralizer_singleton_iff.mp hw.2
      have hka' : Commute k a := hka
      exact ((hka'.mul_left hwa).mul_left hka'.inv_left).eq
    · rw [← hψconj ℓ, map_mul, map_mul, map_inv]

theorem primeComplementCore_eq_bot_of_psl28 (h : D2AlmostSimple 3 X R A X₀ K)
    (e : K ≃* PSL(2, GaloisField 2 3)) : primeComplementCore (G := X₀) 3 = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set W := (primeComplementCore (G := X₀) 3).map X₀.subtype with hWdef
  have hWsub : W.subgroupOf X₀ = primeComplementCore (G := X₀) 3 :=
    Subgroup.comap_map_eq_self_of_injective X₀.subtype_injective _
  have hWX₀ : W ≤ X₀ := Subgroup.map_subtype_le _
  have hWn : X₀ ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX₀).mp (by rw [hWsub]; infer_instance)
  have hcop : Nat.Coprime 3 (Nat.card W) := by
    rw [Subgroup.card_map_of_injective X₀.subtype_injective]
    exact primeComplementCore_coprime 3
  have hW3 : ¬ 3 ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hAX₀ : A ≤ X₀ := h.A_le.trans h.sylow_le
  have hW : W = ⊥ := by
    obtain ⟨emb, hinj, hrange⟩ := rank_two_has_coordinate_embedding 3 hp A
      (le_pRank_of_isElemAbelian hp h.elem h.card_A)
    refine le_bot_iff.mp
      (embedded_rank_two_signalizer_le_of_line_centralizers 3 hp emb W ⊥
        (fun x hx => hWn (hAX₀ (hrange hx))) hcop ?_)
    intro v hv
    set a := emb (coordinatePairLineHom v (Multiplicative.ofAdd (1 : ZMod 3))) with ha
    have haR : a ∈ (emb.comp (coordinatePairLineHom v)).range := ⟨Multiplicative.ofAdd 1, rfl⟩
    have haA : a ∈ A := hrange ⟨_, rfl⟩
    have ha1 : a ≠ 1 := by
      intro h1
      have h2 := hinj (h1.trans (map_one emb).symm)
      have h3 : (Multiplicative.toAdd (coordinatePairLineHom v
          (Multiplicative.ofAdd (1 : ZMod 3)))) = 0 := by rw [h2]; rfl
      apply hv
      simpa [coordinatePairLineHom] using h3
    calc W ⊓ Subgroup.centralizer
          (((emb.comp (coordinatePairLineHom v)).range : Subgroup X) : Set X)
        ≤ W ⊓ Subgroup.centralizer ({a} : Set X) :=
          inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haR))
      _ = ⊥ := inf_centralizer_eq_bot_of_psl28 h e hWn hW3 haA ha1
  exact (Subgroup.map_eq_bot_iff_of_injective _ X₀.subtype_injective).mp hW

end Core

@[expose] def IsD2SeitzLTwoEight (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d = .A 1 q

theorem IsD2SeitzLTwoEight.isD2SeitzRest {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : IsD2SeitzLTwoEight p d) : IsD2SeitzRest p d :=
  Or.inl ⟨h.1, Or.inl h.2⟩

theorem d2PairAt_l28 (d : TauCeti.ValidLieTypeIndex) :
    D2PairAt (.lie d) fun p => IsD2SeitzLTwoEight p d.1 := by
  rintro X _ _ p ⟨rfl, q, hq2, hq3, hdq⟩ R A X₀ K hK ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := d)
    ⟨q, hdq, hq2, hq3⟩
  exact primeComplementCore_eq_bot_of_psl28 hK (e.trans e')

@[expose] def D2SeitzExcRestStrong3 (G : Type) [Group G] [Finite G] : Prop :=
  (∀ d : TauCeti.ValidLieTypeIndex, D2IndexCaseAt3 G (.lie d) fun p =>
    IsD2SeitzRest p d.1 ∧ ¬ IsD2SeitzLTwoEight p d.1) ∧
  ∀ d : TauCeti.ValidLieTypeIndex,
    D2IndexCaseStrongAt3 G (.lie d) fun p => IsD2SeitzLTwoEight p d.1

theorem d2SeitzExcRest3_of_strong (h84 : Asc81bEightFour) (hX : D1NoXBlock3 G)
    (h : D2SeitzExcRestStrong3 G) : D2SeitzExcRest3 G := by
  intro d hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  by_cases hl : IsD2SeitzLTwoEight p d.1
  · exact d2IndexCaseAt3_of_pair (fun _ hp => hp.1) (d2PairAt_l28 d) h84 hX (h.2 d) hSet hD1 M hM
      ha hb p hp hl P A H R hMP hesc hmax Rbar K hRbar hK he
  · exact h.1 d hSet hD1 M hM ha hb p hp ⟨hpp, hl⟩ P A H R hMP hesc hmax Rbar K hRbar hK he

theorem d2SeitzExcRestStrong3_of_seitzExcRest3 (h : D2SeitzExcRest3 G) :
    D2SeitzExcRestStrong3 G :=
  ⟨fun d hSet hD1 M hM ha hb p hp hpp => h d hSet hD1 M hM ha hb p hp hpp.1,
    fun d => d2IndexCaseStrongAt3_of_indexCaseAt3 fun hSet hD1 M hM ha hb p hp hpp =>
      h d hSet hD1 M hM ha hb p hp hpp.isD2SeitzRest⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
