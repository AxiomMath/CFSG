module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndCentral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalCases
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSwapTen
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalThirteen

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem commZ_of_wclZ (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hwclZ : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a) :
    ∀ u ∈ AschbacherTheorem3.omegaOne d.T, ∀ s ∈ d.S,
      u⁻¹ * s⁻¹ * u * s ∈ factorZStar D Abar a := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set Z := factorZStar D Abar a with hZdef
  intro u hu s hs
  have hle : rightConjugate U s ≤ d.S ⊔ U := by
    rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hs : s ∈ d.S ⊔ U)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right s
  have h1 := hwclZ s (d.sylowS.le hs) hle (AschbacherTheorem3.conj_mem_rightConjugate hu s)
  have h2 : u⁻¹ * s⁻¹ * u * s ∈ U ⊔ Z := by
    have : u⁻¹ * s⁻¹ * u * s = u⁻¹ * (s⁻¹ * u * s) := by group
    rw [this]
    exact (U ⊔ Z).mul_mem (Subgroup.mem_sup_left (U.inv_mem hu)) h1
  have h3 : u⁻¹ * s⁻¹ * u * s ∈ A := by
    have h4 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (d.S : Set G)).inv_mem
      (EndHyp.U_le_normalizer_S hu)) s⁻¹).mp (d.S.inv_mem hs)
    rw [inv_inv] at h4
    exact d.sylowS.le (d.S.mul_mem h4 hs)
  have hUZ : U ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    le_normalizer_factorZStar a (EndHyp.U_le_H hC hu) (EndHyp.U_le_normalizer_A hu)
  have h2' : u⁻¹ * s⁻¹ * u * s ∈ ((U ⊔ Z : Subgroup G) : Set G) := h2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U Z hUZ] at h2'
  obtain ⟨u', hu', z, hz, hx⟩ := Set.mem_mul.mp h2'
  have hu'A : u' ∈ A := by
    have : u' = (u' * z) * z⁻¹ := by group
    rw [this, hx]
    exact A.mul_mem h3 (A.inv_mem hz.1)
  have hu'1 : u' ∈ U ⊓ A := ⟨hu', hu'A⟩
  rw [EndHyp.U_inf_A hC, Subgroup.mem_bot] at hu'1
  rw [← hx, hu'1, one_mul]
  exact hz

theorem false_of_wcl (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hLH : ¬ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hVZ : 2 ≤ Nat.card (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ⊓
        factorZStar D Abar a : Subgroup G))
    (hwcl : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) : False := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set W := d.S ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) with hWdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  set Z := factorZStar D Abar a with hZdef
  by_cases hΩ : AschbacherTheorem3.omegaOne d.S ≤ W
  · have hΩV : AschbacherTheorem3.omegaOne d.S = V := by
      apply le_antisymm
      · rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
        rintro x ⟨hxS, hx2⟩
        exact mem_omegaOne (hΩ (mem_omegaOne hxS hx2)) hx2
      · exact AschbacherTheorem3.omegaOne_mono inf_le_left
    refine end_of_6_4 hin hC d ⟨hT, hΩ, AschbacherTheorem3.isMulCommutative_of_le hΩ hWab,
      ?_, ?_⟩
    · rw [hΩV]
      exact hwcl
    · rw [hΩV, hcard]
      have hpos : 0 < Nat.card V := Nat.card_pos
      nlinarith
  · obtain ⟨e, heS, heH, heN, he2⟩ := exists_bad_element hloc hC hr d hT hWab hcard hSH
      (fun h => hΩ h.1)
    obtain ⟨hinj, -, hcent⟩ := bad_element_props hC d hT hWab hcard heS heH heN he2
    have hVZ' : V ≤ Z := fun v hv => mem_factorZStar_of_comm hloc hC hr d hW hLH heS hinj
      (AschbacherTheorem3.omegaOne_le _ hv) (hcent v hv)
    refine end_of_6_4_central hin hloc hC d hT ?_ ?_
    · intro u hu s hs
      have hle : rightConjugate U s ≤ d.S ⊔ U := by
        rw [← AschbacherTheorem3.rightConjugate_eq_of_mem
          (Subgroup.mem_sup_left hs : s ∈ d.S ⊔ U)]
        exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right s
      have h1 := hwcl s (d.sylowS.le hs) hle (AschbacherTheorem3.conj_mem_rightConjugate hu s)
      have h2 : u⁻¹ * s⁻¹ * u * s ∈ U ⊔ V := by
        have : u⁻¹ * s⁻¹ * u * s = u⁻¹ * (s⁻¹ * u * s) := by group
        rw [this]
        exact (U ⊔ V).mul_mem (Subgroup.mem_sup_left (U.inv_mem hu)) h1
      have h3 : u⁻¹ * s⁻¹ * u * s ∈ d.S := by
        have h4 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (d.S : Set G)).inv_mem
          (EndHyp.U_le_normalizer_S hu)) s⁻¹).mp (d.S.inv_mem hs)
        rw [inv_inv] at h4
        exact d.S.mul_mem h4 hs
      exact hVZ' (mem_omegaOne_W_of_mem_sup hC d hT hWab h2 h3)
    · intro c hc hle
      exact (hwcl c hc hle).trans (sup_le_sup_left hVZ' _)

@[expose] def Lemma613Residual : Prop :=
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
    AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a →
    (∃ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a) →
    False

theorem lemma613MainCase_of_residual (hres : Lemma613Residual) : Lemma613MainCase := by
  intro hin hloc G _ _ D r Abar hC a d d' hgg hW hW' hmax hTab hWab hS hS' heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : r = 2 := hloc.lemma_6_9 hC ⟨_, datum_mem_delta d⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  set Z := factorZStar D Abar a with hZdef
  obtain ⟨c₂, -, hc₂⟩ := swap_W d d' hgg hW'
  have hTW : Nat.card d.T ≤ Nat.card W := by
    have h1 : Nat.card d.T = Nat.card (d'.S ⊓ Subgroup.normalizer
        (rightConjugate A d'.g : Set G) : Subgroup G) := by rw [hc₂, rightConjugate_card]
    rw [h1, hW'.card_eq, hW.card_eq]
    exact Nat.pow_le_pow_right (by norm_num) (hmax d'.g (datum_mem_delta d'))
  obtain ⟨y, hy, hyN⟩ := exists_not_normalizer_of_card_le hloc hC (datum_mem_delta d) a
    d.sylowT hW hTW
  have hLH : ¬ L ⊓ H ≤ Subgroup.normalizer (A : Set G) := fun h => hyN (h hy)
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
  by_cases hwcl : ∀ c ∈ A, rightConjugate U c ≤ d.S ⊔ U → rightConjugate U c ≤ U ⊔ V
  · by_cases hΩ : AschbacherTheorem3.omegaOne d.S ≤ W
    · have hΩV : AschbacherTheorem3.omegaOne d.S = V := by
        apply le_antisymm
        · rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
          rintro x ⟨hxS, hx2⟩
          exact mem_omegaOne (hΩ (mem_omegaOne hxS hx2)) hx2
        · exact AschbacherTheorem3.omegaOne_mono inf_le_left
      refine ⟨hΩ, ?_⟩
      rw [hΩV]
      exact hwcl
    · exact (false_of_wcl hin hloc hC hr d hW hLH hTab hWab hS heq hVZ hwcl).elim
  · exfalso
    obtain ⟨e, heS, heH, heN, he2⟩ := exists_bad_element hloc hC hr d hTab hWab heq hS
      (fun h => hwcl h.2)
    obtain ⟨hinj, -, hcent⟩ := bad_element_props hC d hTab hWab heq heS heH heN he2
    have hVZ' : V ≤ Z := fun v hv => mem_factorZStar_of_comm hloc hC hr d hW hLH heS hinj
      (AschbacherTheorem3.omegaOne_le _ hv) (hcent v hv)
    by_cases hwclZ : ∀ c ∈ A, rightConjugate U c ≤ d.S ⊔ U → rightConjugate U c ≤ U ⊔ Z
    · exact end_of_6_4_central hin hloc hC d hTab (commZ_of_wclZ hC d hwclZ) hwclZ
    · push Not at hwclZ
      exact hres hin hloc hC d d' hgg hW hW' hmax hTab hWab hS hS' heq hVZ' hwclZ

end DeltaGlobal

theorem theorem_6_4_of_residual (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hres : DeltaGlobal.Lemma613Residual) {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {r : ℕ} {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hC : Counterexample G D r Abar) :
    deltaConjugates (Subgroup.normalizer (D : Set G)) = ∅ :=
  theorem_6_4_of_mainCase hin hloc (DeltaGlobal.lemma613MainCase_of_residual hres) hC

end CFSG.ComponentClassification.AschbacherTheorem5
