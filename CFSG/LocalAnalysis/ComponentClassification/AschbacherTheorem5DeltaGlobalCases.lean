module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSwap
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEnd
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTwelve

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

@[expose] noncomputable def sylowExp (D : Subgroup G)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (a : Fin r) (x : G) : ℕ :=
  (Nat.card (aschbacherThm5Preimage D (Abar a) ⊓
    Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) x : Set G) :
      Subgroup G)).factorization 2

theorem exists_max (D : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (a : Fin r) (hΔ : (deltaConjugates (Subgroup.normalizer (D : Set G))).Nonempty) :
    ∃ g : G, rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
        deltaConjugates (Subgroup.normalizer (D : Set G)) ∧
      ∀ x : G, rightConjugate (Subgroup.normalizer (D : Set G)) x ∈
        deltaConjugates (Subgroup.normalizer (D : Set G)) →
        sylowExp D Abar a x ≤ sylowExp D Abar a g := by
  obtain ⟨K, hK⟩ := hΔ
  obtain ⟨g₀, rfl, -, -⟩ := id hK
  set X : Set G := {x | rightConjugate (Subgroup.normalizer (D : Set G)) x ∈
    deltaConjugates (Subgroup.normalizer (D : Set G))}
  have hX : X.Finite := Set.toFinite X
  obtain ⟨g, hg, hmax⟩ := Set.exists_max_image X (sylowExp D Abar a) hX ⟨g₀, hK⟩
  exact ⟨g, hg, fun x hx => hmax x hx⟩

theorem omegaOne_eq_of_le (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hSH : d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    AschbacherTheorem3.omegaOne d.S = AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) := by
  apply le_antisymm
  · rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
    rintro x ⟨hxS, hx2⟩
    exact mem_omegaOne ⟨hxS, mem_normalizer_of_involution hloc hC hr d (d.sylowS.le hxS)
      (hSH hxS) hx2⟩ hx2
  · exact AschbacherTheorem3.omegaOne_mono inf_le_left

theorem exists_U_inf_zStar (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hsize : 2 ^ (Nat.card (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) :
        Subgroup G)).factorization 2 ≤ Nat.card d.T) :
    ∃ t ∈ AschbacherTheorem3.omegaOne d.T, t ∈ rightConjugate (factorZStar D Abar a) d.g ∧
      t ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  obtain ⟨x, hxA, hxN, heven, -⟩ := hloc.lemma_6_8 hC d hsize
  obtain ⟨⟨t, ht⟩, htord⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have htord' : orderOf t = 2 := by rw [← Subgroup.orderOf_coe] at htord; exact htord
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at htord'
    exact absurd htord' (by norm_num)
  have ht2 : t ^ 2 = 1 := by rw [← htord']; exact pow_orderOf_eq_one t
  have htL : t ∈ rightConjugate A d.g := d.sylowT.le ht.1 |>.1
  have htLx : t ∈ rightConjugate A (d.g * x) := by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate
      (d.sylowT.le.trans inf_le_left) x ht.2
    rwa [rightConjugate_mul] at h1
  have htwo : ∃ k : ℕ, t ^ (2 ^ k) = 1 := ⟨1, by simpa using ht2⟩
  have hs1 : d.g * t * d.g⁻¹ ∈ A := (mem_rightConjugate_iff _ _ _).mp htL
  have hxH : d.g * x * d.g⁻¹ ∈ H := by
    by_contra hx
    have hs2 : d.g * t * d.g⁻¹ ∈ rightConjugate A (d.g * x * d.g⁻¹) := by
      rw [mem_rightConjugate_iff]
      have h1 := (mem_rightConjugate_iff _ _ _).mp htLx
      have heq : d.g * x * d.g⁻¹ * (d.g * t * d.g⁻¹) * (d.g * x * d.g⁻¹)⁻¹ =
          d.g * x * t * (d.g * x)⁻¹ := by group
      rw [heq]
      exact h1
    have h1 := eq_one_of_mem_inf_conj hC hx (twoElt_conj htwo d.g) hs1 hs2
    apply ht1
    calc t = d.g⁻¹ * (d.g * t * d.g⁻¹) * d.g := by group
      _ = 1 := by rw [h1]; group
  have hxN' : d.g * x * d.g⁻¹ ∉ Subgroup.normalizer (A : Set G) := by
    intro h
    apply hxN
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
    exact h
  obtain ⟨b, hba⟩ := exists_other hC a
  have hAx := rightConjugate_eq_other hC hr hxH hba hxN'
  have htb : d.g * t * d.g⁻¹ ∈ aschbacherThm5Preimage D (Abar b) := by
    rw [← hAx, mem_rightConjugate_iff]
    have h1 := (mem_rightConjugate_iff _ _ _).mp htLx
    have heq : d.g * x * d.g⁻¹ * (d.g * t * d.g⁻¹) * (d.g * x * d.g⁻¹)⁻¹ =
        d.g * x * t * (d.g * x)⁻¹ := by group
    rw [heq]
    exact h1
  refine ⟨t, mem_omegaOne ht.1 ht2, ?_, ht1⟩
  rw [mem_rightConjugate_iff]
  exact mem_factorZStar_of_mem_other hC hba hs1 htb

theorem card_S_le_of_le (hC : Counterexample G D r Abar) (hr : r = 2) {a : Fin r}
    (d d' : DeltaDatum D Abar a) (hg : d'.g = d.g⁻¹)
    (hS' : d'.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d'.g) :
    Nat.card d.S ≤ 2 * Nat.card d.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  have hle : rightConjugate d'.S d.g ≤ L ⊓ H := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    refine ⟨(mem_rightConjugate_iff _ _ _).mpr (d'.sylowS.le hy), ?_⟩
    have h1 := hS' hy
    rw [hg, mem_rightConjugate_iff] at h1
    simpa [mul_assoc] using h1
  obtain ⟨P, hP, hPle⟩ := AschbacherTheorem3.exists_isSylowOf_le
    (AschbacherTheorem3.isPGroup_rightConjugate d'.sylowS.isPGroup d.g) hle
  have hQ : IsSylowOf 2 d.T ((L ⊓ H) ⊓ Subgroup.normalizer (A : Set G)) := by
    have heq : (L ⊓ H) ⊓ Subgroup.normalizer (A : Set G) = L ⊓ Subgroup.normalizer (A : Set G) := by
      rw [inf_assoc, inf_eq_right.mpr (factor_normalizer_le D r Abar hC.hyp.hii a)]
    rw [heq]
    exact d.sylowT
  have h1 := sylow_card_le_two_mul hC hr a inf_le_right hP hQ
  have h2 : Nat.card d.S = Nat.card d'.S := by
    rw [d.sylowS.card_eq, d'.sylowS.card_eq]
  have h3 : Nat.card (rightConjugate d'.S d.g) ≤ Nat.card P := Subgroup.card_le_of_le hPle
  rw [rightConjugate_card] at h3
  omega

@[expose] def Lemma613MainCase : Prop :=
  SectionSixGlobalInputs → SectionSixLocalResults →
  ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {a : Fin r} (d d' : DeltaDatum D Abar a), d'.g = d.g⁻¹ →
    IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) →
    IsSylowOf 2 (d'.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G)) →
    (∀ x : G, rightConjugate (Subgroup.normalizer (D : Set G)) x ∈
        deltaConjugates (Subgroup.normalizer (D : Set G)) →
        sylowExp D Abar a x ≤ sylowExp D Abar a d.g) →
    IsMulCommutative d.T →
    IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G) →
    ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g →
    ¬ d'.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d'.g →
    Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) →
    AschbacherTheorem3.omegaOne d.S ≤ d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ∧
      ∀ c ∈ aschbacherThm5Preimage D (Abar a),
        rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
          d.S ⊔ AschbacherTheorem3.omegaOne d.T →
        rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
          AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S

theorem false_of_max (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hmain : Lemma613MainCase) (hC : Counterexample G D r Abar) {a : Fin r} {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)))
    (hmax : ∀ x : G, rightConjugate (Subgroup.normalizer (D : Set G)) x ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) →
      sylowExp D Abar a x ≤ sylowExp D Abar a g) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : r = 2 := hloc.lemma_6_9 hC ⟨_, hΔ⟩
  obtain ⟨d, hdg, hW⟩ := exists_sylow_datum hC hΔ a
  have hΔ' := inv_mem_deltaConjugates hloc hC hΔ
  obtain ⟨d', hd'g, hW'⟩ := exists_sylow_datum hC hΔ' a
  have hgg : d'.g = d.g⁻¹ := by rw [hd'g, hdg]
  rw [← hdg] at hW hmax
  rw [← hd'g] at hW'
  have hΔd' : rightConjugate (Subgroup.normalizer (D : Set G)) d'.g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) := hd'g ▸ hΔ'
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set W' := d'.S ⊓ Subgroup.normalizer (rightConjugate A d'.g : Set G) with hW'def
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  set Z := factorZStar D Abar a with hZdef
  obtain ⟨c₂, hc₂A, hc₂⟩ := swap_W d d' hgg hW'
  obtain ⟨c₁, hc₁⟩ := swap_T d d' hgg hW
  replace hc₂ : W' = rightConjugate d.T (d.g⁻¹ * c₂) := hc₂
  replace hc₁ : d'.T = rightConjugate W c₁ := hc₁
  have hTW : Nat.card d.T ≤ Nat.card W := by
    have h1 : Nat.card d.T = Nat.card W' := by rw [hc₂, rightConjugate_card]
    rw [h1, hW'.card_eq, hW.card_eq]
    exact Nat.pow_le_pow_right (by norm_num) (hmax d'.g hΔd')
  obtain ⟨y, hy, hyN⟩ := exists_not_normalizer_of_card_le hloc hC (datum_mem_delta d) a
    d.sylowT hW hTW
  have hLH : ¬ L ⊓ H ≤ Subgroup.normalizer (A : Set G) := fun h => hyN (h hy)
  have hWab : IsMulCommutative W := by
    by_cases hWZ : W ≤ Z
    · exact isMulCommutative_of_le_conj_factorZStar (i := a) (g := 1) hW.isPGroup
        (by rw [rightConjugate_one]; exact hWZ)
    · exact sylow_normalizer_abelian hloc hC (datum_mem_delta d) a hW hLH hWZ
  have hTab := datum_T_abelian hloc hC d hWab
  have hT'ab : IsMulCommutative d'.T := by
    rw [hc₁]
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hWab c₁
  have hW'ab : IsMulCommutative W' := by
    rw [hc₂]
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hTab _
  have hcT' : Nat.card (AschbacherTheorem3.omegaOne d'.T) = Nat.card V := by
    rw [hc₁, card_omegaOne_rightConjugate]
  have hcW' : Nat.card (AschbacherTheorem3.omegaOne W') = Nat.card U := by
    rw [hc₂, card_omegaOne_rightConjugate]
  obtain ⟨s, hsWZ, hs1, hs2⟩ := exists_involution_factorZStar hloc hC hr (datum_mem_delta d) a
    d.sylowT hW hTW
  have hVZ : 2 ≤ Nat.card (V ⊓ Z : Subgroup G) := by
    have hne : (V ⊓ Z : Subgroup G) ≠ ⊥ := by
      intro hb
      have hmem : s ∈ V ⊓ Z := ⟨mem_omegaOne hsWZ.1 hs2, hsWZ.2⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact hs1 hmem
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hU4 := four_le_card_U hloc hC d
  have hU4' := four_le_card_U hloc hC d'
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hWHg : W ≤ rightConjugate H d.g := inf_le_right.trans (normalizer_conj_le hC a d.g)
  have halt' : ¬ d'.S ≤ rightConjugate H d'.g → Nat.card V ≤ Nat.card U := by
    intro hS'
    obtain ⟨b', hb'S, hb'H, hb'U⟩ := exists_conj_of_not_le d' hS'
    have hle' : rightConjugate (AschbacherTheorem3.omegaOne d'.T) b' ≤
        d'.S ⊔ AschbacherTheorem3.omegaOne d'.T := by
      rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hb'S :
        b' ∈ d'.S ⊔ AschbacherTheorem3.omegaOne d'.T)]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right b'
    have h := card_le_of_conj hloc hC d' hT'ab hW'ab hU4' (d'.sylowS.le hb'S) hb'H hle' hb'U
    rw [hcT'] at h
    exact h.trans hcW'.le
  have hend' : d'.S ≤ rightConjugate H d'.g →
      Nat.card U < Nat.card V * Nat.card (AschbacherTheorem3.omegaOne W' ⊓ Z : Subgroup G) →
      False := by
    intro hS' hlt
    have hΩ' := omegaOne_eq_of_le hloc hC hr d' hS'
    apply end_of_6_4 hin hC d'
    apply endHyp_of_le hloc hC hr d' hT'ab hW'ab hS'
    rw [hΩ', hcW', hcT']
    exact hlt
  by_cases hS : d.S ≤ rightConjugate H d.g
  · have hΩ := omegaOne_eq_of_le hloc hC hr d hS
    by_cases h5 : Nat.card (AschbacherTheorem3.omegaOne d.S) <
        Nat.card U * Nat.card (AschbacherTheorem3.omegaOne d.S ⊓ Z : Subgroup G)
    · exact end_of_6_4 hin hC d (endHyp_of_le hloc hC hr d hTab hWab hS h5)
    · rw [hΩ] at h5
      push Not at h5
      have hUV : Nat.card U < Nat.card V := by
        have : Nat.card U * 2 ≤ Nat.card V := (Nat.mul_le_mul_left _ hVZ).trans h5
        omega
      by_cases hS' : d'.S ≤ rightConjugate H d'.g
      · apply hend' hS'
        have : 1 ≤ Nat.card (AschbacherTheorem3.omegaOne W' ⊓ Z : Subgroup G) := Nat.card_pos
        nlinarith
      · have := halt' hS'
        omega
  · obtain ⟨b, hbS, hbH, hbU⟩ := exists_conj_of_not_le d hS
    have hle : rightConjugate U b ≤ d.S ⊔ U := by
      rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hbS :
        b ∈ d.S ⊔ U)]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right b
    have hUV : Nat.card U ≤ Nat.card V :=
      card_le_of_conj hloc hC d hTab hWab hU4 (d.sylowS.le hbS) hbH hle hbU
    by_cases hS' : d'.S ≤ rightConjugate H d'.g
    · rcases lt_or_eq_of_le hUV with hlt | heq
      · apply hend' hS'
        have : 1 ≤ Nat.card (AschbacherTheorem3.omegaOne W' ⊓ Z : Subgroup G) := Nat.card_pos
        nlinarith
      · by_cases hZ' : AschbacherTheorem3.omegaOne W' ⊓ Z = ⊥
        ·
          have hUZ : ∀ t ∈ U, t ∈ rightConjugate Z d.g → t = 1 := by
            intro t htU htZ
            set x := d.g⁻¹ * c₂ with hxdef
            have h1 : x⁻¹ * t * x ∈ AschbacherTheorem3.omegaOne W' ⊓ Z := by
              refine ⟨?_, ?_⟩
              · rw [hc₂, omegaOne_rightConjugate]
                exact AschbacherTheorem3.conj_mem_rightConjugate htU x
              · rw [mem_rightConjugate_iff] at htZ
                have h2 := conj_mem_factorZStar a (Subgroup.inv_mem _ hc₂A) htZ
                have heq : x⁻¹ * t * x = c₂⁻¹ * (d.g * t * d.g⁻¹) * c₂⁻¹⁻¹ := by
                  rw [hxdef]; group
                rw [heq]
                exact h2
            rw [hZ', Subgroup.mem_bot] at h1
            calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
              _ = 1 := by rw [h1]; group
          have hnot : ¬ 2 ^ (Nat.card (A ⊓ Subgroup.normalizer (L : Set G) :
              Subgroup G)).factorization 2 ≤ Nat.card d.T := by
            intro h
            obtain ⟨t, htU, htZ, ht1⟩ := exists_U_inf_zStar hloc hC hr d h
            exact ht1 (hUZ t htU htZ)
          rw [← hW.card_eq] at hnot
          push Not at hnot
          have hsz := card_S_le_of_le hC hr d d' hgg hS'
          obtain ⟨k, hk⟩ := d.sylowT.isPGroup.exists_card_eq
          obtain ⟨j, hj⟩ := hW.isPGroup.exists_card_eq
          have hkj : k < j := by
            rw [hk, hj] at hnot
            exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hnot
          have h2T : 2 * Nat.card d.T ≤ Nat.card W := by
            rw [hk, hj, ← pow_succ']
            exact Nat.pow_le_pow_right (by norm_num) hkj
          have hWS : W = d.S :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
          exact hS (hWS ▸ hWHg)
        · apply hend' hS'
          have hne : 1 < Nat.card (AschbacherTheorem3.omegaOne W' ⊓ Z : Subgroup G) :=
            (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ'
          rw [heq]
          nlinarith
    · have hVU := halt' hS'
      have heq : Nat.card U = Nat.card V := le_antisymm hUV hVU
      obtain ⟨hΩS, hwcl⟩ := hmain hin hloc hC d d' hgg hW hW' hmax hTab hWab hS hS' heq
      have hΩ : AschbacherTheorem3.omegaOne d.S = V := by
        apply le_antisymm
        · rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
          rintro x ⟨hxS, hx2⟩
          exact mem_omegaOne (hΩS (mem_omegaOne hxS hx2)) hx2
        · exact AschbacherTheorem3.omegaOne_mono inf_le_left
      refine end_of_6_4 hin hC d ⟨hTab, hΩS, AschbacherTheorem3.isMulCommutative_of_le hΩS hWab,
        hwcl, ?_⟩
      rw [hΩ, ← heq]
      have hpos : 0 < Nat.card U := Nat.card_pos
      rw [heq] at hpos ⊢
      nlinarith

end DeltaGlobal

theorem theorem_6_4_of_mainCase (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hmain : DeltaGlobal.Lemma613MainCase) {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {r : ℕ} {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hC : Counterexample G D r Abar) :
    deltaConjugates (Subgroup.normalizer (D : Set G)) = ∅ := by
  by_contra hne
  have hΔ : (deltaConjugates (Subgroup.normalizer (D : Set G))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  have hr := hloc.lemma_6_9 hC hΔ
  obtain ⟨g, hg, hmax⟩ := DeltaGlobal.exists_max D Abar ⟨0, by omega⟩ hΔ
  exact DeltaGlobal.false_of_max hin hloc hmain hC hg hmax

end CFSG.ComponentClassification.AschbacherTheorem5
