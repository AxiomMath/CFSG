module

public import CFSG.ClassicalInvolution.RouteD.TWED6Bridge
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fixed
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.RouteD.TWEB6YBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.D6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (polarNondegOn_sup)

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_fixed_pair_dim13 (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 13 ≤ Module.finrank K V) {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hc : VChain Q 2 L i) :
    ∃ S S' : Subgroup (V ≃ₗ[K] V), S ∈ fundSet Q ∧ S' ∈ fundSet Q ∧ Commutes S (L 0) ∧
      Commutes S (L 1) ∧ Commutes S' (L 0) ∧ ¬ Commutes S S' ∧ S ≠ S' := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, horth, -, hL⟩ := exists_chain_pairs true hodd hc (le_refl 2)
  obtain ⟨p', hp', ho'⟩ := exists_orth_ext hodd hQ p 3
    (fun a b ha hb hab => horth a b (by omega) (by omega) hab) 3 (by omega)
  have hpp : ∀ a b, a < 6 → b < 6 → a ≠ b → (p' a).Orth (p' b) :=
    fun a b ha hb hab => ho' a b (by omega) (by omega) hab
  have hL0 : L 0 = (oFrame true (p' 0) (p' 1) (hpp 0 1 (by norm_num) (by norm_num)
      (by norm_num))).La.range := by
    have := hL 0 (by norm_num)
    simpa only [hp' 0 (by norm_num), hp' 1 (by norm_num)] using this
  have hL1 : L 1 = (oFrame true (p' 1) (p' 2) (hpp 1 2 (by norm_num) (by norm_num)
      (by norm_num))).La.range := by
    have := hL 1 (by norm_num)
    simpa only [hp' 1 (by norm_num), hp' 2 (by norm_num)] using this
  set F₁ := mkFrame (p' 3) (p' 4) (hpp 3 4 (by norm_num) (by norm_num) (by norm_num)) with hF₁
  set F₂ := mkFrame (p' 4) (p' 5) (hpp 4 5 (by norm_num) (by norm_num) (by norm_num)) with hF₂
  have hne2 : F₂.La (-1) ≠ F₁.La (-1) := by
    intro h
    have hneg : negSpace (F₂.La (-1)) = negSpace (F₁.La (-1)) := by rw [h]
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2, frame_span_eq, frame_span_eq] at hneg
    have hmem : (p' 3).e ∈ hypPlane (p' 4) ⊔ hypPlane (p' 5) := by
      have : (p' 3).e ∈ hypPlane F₁.P ⊔ hypPlane F₁.P' :=
        Submodule.mem_sup_left (e_mem_hypPlane _)
      rw [← hneg] at this
      exact this
    have hnd : PolarNondegOn Q (hypPlane (p' 4) ⊔ hypPlane (p' 5)) :=
      polarNondegOn_sup (polarNondegOn_hypPlane (p' 4)) (polarNondegOn_hypPlane (p' 5))
        (polar_hypPlane_of_orth (hpp 4 5 (by norm_num) (by norm_num) (by norm_num)))
    exact (p' 3).e_ne_zero (hnd _ hmem fun y hy =>
      polar_zero_of_mem_sup (A := hypPlane (p' 3))
        (fun x hx y hy => polar_hypPlane_of_orth (hpp 3 4 (by norm_num) (by norm_num)
          (by norm_num)) x hx y hy)
        (fun x hx y hy => polar_hypPlane_of_orth (hpp 3 5 (by norm_num) (by norm_num)
          (by norm_num)) x hx y hy) _ (e_mem_hypPlane _) y hy)
  refine ⟨F₁.La.range, F₂.La.range, ⟨_, IsFundamental.of_frame F₁⟩,
    ⟨_, IsFundamental.of_frame F₂⟩, ?_, ?_, ?_, ?_, fun h => hne2 ?_⟩
  · rw [hL0]
    exact commutes_frames_of_orth _ _ (hpp 3 0 (by norm_num) (by norm_num) (by norm_num))
      (hpp 3 1 (by norm_num) (by norm_num) (by norm_num))
      (hpp 4 0 (by norm_num) (by norm_num) (by norm_num))
      (hpp 4 1 (by norm_num) (by norm_num) (by norm_num))
  · rw [hL1]
    exact commutes_frames_of_orth _ _ (hpp 3 1 (by norm_num) (by norm_num) (by norm_num))
      (hpp 3 2 (by norm_num) (by norm_num) (by norm_num))
      (hpp 4 1 (by norm_num) (by norm_num) (by norm_num))
      (hpp 4 2 (by norm_num) (by norm_num) (by norm_num))
  · rw [hL0]
    exact commutes_frames_of_orth _ _ (hpp 4 0 (by norm_num) (by norm_num) (by norm_num))
      (hpp 4 1 (by norm_num) (by norm_num) (by norm_num))
      (hpp 5 0 (by norm_num) (by norm_num) (by norm_num))
      (hpp 5 1 (by norm_num) (by norm_num) (by norm_num))
  · refine not_commutes_of_nonorth hodd (IsFundamental.of_frame F₁) (IsFundamental.of_frame F₂)
      hne2 (x := (p' 4).e) (y := (p' 4).f) ?_ ?_ (by rw [(p' 4).polar_ef]; exact one_ne_zero)
    · rw [negSpace_La_neg_one h2, frame_span_eq]
      exact Submodule.mem_sup_right (e_mem_hypPlane _)
    · rw [negSpace_La_neg_one h2, frame_span_eq]
      exact Submodule.mem_sup_left (f_mem_hypPlane _)
  · exact IsFundamental.involution_unique hodd (IsFundamental.of_frame F₂)
      (h ▸ IsFundamental.of_frame F₁)

end Model

section Spin

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}


theorem exists_fixed_pair_spin_dim13 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 13 ≤ Module.finrank (GaloisField p f) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    {R₀ R₁ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ T ∈ 𝓕, ∃ T' ∈ 𝓕, Commutes T R₀ ∧ Commutes T R₁ ∧ Commutes T' R₀ ∧ ¬ Commutes T T' ∧
      T ≠ T' := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ h₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ h₁
  have hdata := adj_data hodd (by omega) hi₀ hi₁ (cq.modelAdj h₀ h₁ hadj)
  obtain ⟨W, hW⟩ := hlin
  have hsing := hasSingularVector_of_linearPair hp2 (by omega) hi₀ hi₁ hdata.1 hdata.2.1
    hdata.2.2 ⟨_, linearBlockStandardPair_map_central hW _ cq.ker_le⟩
  have hvc : VChain Q 2 (fun a => if a = 0 then R₀.map (spinAction Q) else R₁.map (spinAction Q))
      (fun a => if a = 0 then i₀ else i₁) := by
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => ?_⟩
    · rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact hi₀
      · exact hi₁
    · obtain rfl : a = 0 := by omega
      exact hdata.1
    · obtain rfl : a = 0 := by omega
      exact hdata.2.1
    · obtain rfl : a = 0 := by omega
      exact hdata.2.2
    · obtain rfl : a = 0 := by omega
      exact hsing
    · exfalso
      omega
  obtain ⟨S, S', hS, hS', c0, c1, c0', hnc, hne⟩ := exists_fixed_pair_dim13 hodd hQ hdim hvc
  obtain ⟨T, hT, rfl⟩ := cq.surj S hS
  obtain ⟨T', hT', rfl⟩ := cq.surj S' hS'
  exact ⟨T, hT, T', hT', (cq.commutes_iff hT).mp c0, (cq.commutes_iff hT).mp c1,
    (cq.commutes_iff hT').mp c0', fun h => hnc ((cq.commutes_iff hT).mpr h),
    fun h => hne (by rw [h])⟩

end Spin

section Group

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TwinY

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}


theorem exists_fixed_member_typed (hp2 : p ≠ 2) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {u}) {t : StatedLieTag} {n : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hshape : LocalShapeT p f 0 t n Ω u) (hY : YData p f t n)
    (hF : OrthFacts (fundamentalSubgroups t (modelUniv t n p f Fact.out).D) (GaloisField p f))
    (hperf : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D, ⁅R, R⁆ = R)
    (hpair : ∀ {R₀ R₁ : Subgroup (modelUniv t n p f Fact.out).K},
      R₀ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      R₁ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R₀ R₁ →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) →
      ∃ T ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
        ∃ T' ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
          Commutes T R₀ ∧ Commutes T R₁ ∧ Commutes T' R₀ ∧ ¬ Commutes T T' ∧ T ≠ T')
    {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ N ∈ centralizingMembers Ω {u}, ∃ N' ∈ centralizingMembers Ω {u},
      Commutes K N ∧ Commutes β N ∧ Commutes K N' ∧ ¬ Commutes N N' ∧ N ≠ N' := by
  classical
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex hG2 hD4 hshape
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R₀ R₁ :=
    e.modelAdj hY hΩ hP1 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hF hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T, hT, T', hT', c0, c1, c0', hnc, hne⟩ := hpair hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N, hN, hNT⟩ := e.comp T hT
  obtain ⟨N', hN', hN'T⟩ := e.comp T' hT'
  refine ⟨N, hN, N', hN', ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN hK hT hNT hKR).mpr c0)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN hβ hT hNT hβR).mpr c1)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN' hK hT' hN'T hKR).mpr c0')
  · exact fun h => hnc ((e.commutes_iff hY hΩ hP1 hN hN' hT hNT hN'T).mp h)
  · intro h
    refine hne (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect e.φ e.ker_le
      (hperf T hT) (hperf T' hT') ?_)
    rw [← hNT, ← hN'T, h]

theorem twinYModel_plus_six_of_mod (h : p ^ f % 4 = 1) :
    twinYModel (p ^ f) .POmegaPlus 6 = (.POmegaPlus, 7) := by
  simp [twinYModel, h]

theorem twinYModel_plus_six_of_ne (h : ¬ p ^ f % 4 = 1) :
    twinYModel (p ^ f) .POmegaPlus 6 = (.POmegaMinus, 7) := by
  simp [twinYModel, h]

theorem exists_fixed_member_d6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u})
    (hshape : LocalShapeT p f 0 (twinYModel (p ^ f) .POmegaPlus 6).1
      (twinYModel (p ^ f) .POmegaPlus 6).2 Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ N ∈ centralizingMembers Ω {u}, ∃ N' ∈ centralizingMembers Ω {u},
      Commutes K N ∧ Commutes β N ∧ Commutes K N' ∧ ¬ Commutes N N' ∧ N ≠ N' := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have : Invertible (2 : GaloisField p f) :=
    invertibleOfNonzero (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2)
  by_cases h4 : p ^ f % 4 = 1
  · rw [twinYModel_plus_six_of_mod h4] at hshape
    have hadm : StatedLieAdmissible .POmegaPlus 7 p f := ⟨Fact.out, hf1, by norm_num⟩
    have cq := centralQuot_plus (m := 7) hp2 (by norm_num) (by norm_num) hq
    have hQ : (polarBilin (quadPlus 7 (GaloisField p f))).Nondegenerate :=
      nondegenerate_polarBilin_quadPlus 7 (GaloisField p f)
    have hdim : 13 ≤ Module.finrank (GaloisField p f) (Fin 7 ⊕ Fin 7 → GaloisField p f) := by
      rw [finrank_plus]
      norm_num
    exact exists_fixed_member_typed (t := .POmegaPlus) (n := 7) hp2 hΩ hex hP1 (by decide)
      (by decide) hshape (yData_plus (by norm_num) hadm (by omega))
      (orthFacts_plus (m := 7) hp2 (by norm_num) hq) (fun R hR => cq.perf R hR)
      (fun h0 h1 hadj hlin => exists_fixed_pair_spin_dim13 hp2 hq hQ hdim cq h0 h1 hadj hlin)
      hK hβ hz hs hKβ
  · rw [twinYModel_plus_six_of_ne h4] at hshape
    have hadm : StatedLieAdmissible .POmegaMinus 7 p f := ⟨Fact.out, hf1, by norm_num⟩
    have cq := Exotic.centralQuot_minus hp2 hq hadm
    have hQ : (polarBilin (quadMinus 7 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField p f) (minusCoeffs_irr p f)
    have hdim : 13 ≤ Module.finrank (GaloisField p f)
        (Fin (7 - 1) ⊕ Fin (7 - 1) ⊕ Fin 2 → GaloisField p f) := by
      rw [finrank_minus p f 7 (by norm_num)]
      norm_num
    exact exists_fixed_member_typed (t := .POmegaMinus) (n := 7) hp2 hΩ hex hP1 (by decide)
      (by decide) hshape (yData_minus (by norm_num) hp2 hadm (by omega))
      (orthFacts_minus (m := 7) hp2 (by norm_num) hq) (fun R hR => cq.perf R hR)
      (fun h0 h1 hadj hlin => exists_fixed_pair_spin_dim13 hp2 hq hQ hdim cq h0 h1 hadj hlin)
      hK hβ hz hs hKβ

theorem exists_tilted_bridge_d6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u})
    (hshape : LocalShapeT p f 0 (twinYModel (p ^ f) .POmegaPlus 6).1
      (twinYModel (p ^ f) .POmegaPlus 6).2 Ω u) {M : Subgroup G} (nd : DNodes p f 6 Ω M)
    (hx : ∀ a, nd.J a ∈ centralizingMembers Ω {u}) :
    ∃ N ∈ centralizingMembers Ω {u}, (∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a)) ∧
      ¬ Commutes N (nd.J ⟨4, by norm_num⟩) ∧ ¬ Commutes N (nd.J ⟨5, by norm_num⟩) := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have : Invertible (2 : GaloisField p f) :=
    invertibleOfNonzero (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2)
  by_cases h4 : p ^ f % 4 = 1
  · rw [twinYModel_plus_six_of_mod h4] at hshape
    have hshape' : LocalShapeT p f 0 .POmegaPlus 7 Ω u := hshape
    obtain ⟨e⟩ := Layer0.of_shape hΩ hex (by decide) (by decide) hshape'
    have hadm : StatedLieAdmissible .POmegaPlus 7 p f := ⟨Fact.out, hf1, by norm_num⟩
    have cq := centralQuot_plus (m := 7) hp2 (by norm_num) (by norm_num) hq
    have hQ : (polarBilin (quadPlus 7 (GaloisField p f))).Nondegenerate :=
      nondegenerate_polarBilin_quadPlus 7 (GaloisField p f)
    have hdim : 13 ≤ Module.finrank (GaloisField p f) (Fin 7 ⊕ Fin 7 → GaloisField p f) := by
      rw [finrank_plus]
      norm_num
    exact exists_tilted_bridge_group hp2 hΩ hP1 e (yData_plus (by norm_num) hadm (by omega))
      (orthFacts_plus (m := 7) hp2 (by norm_num) hq) (exists_tilted_bridge_spin hp2 hq hQ hdim cq)
      nd hx
  · rw [twinYModel_plus_six_of_ne h4] at hshape
    have hshape' : LocalShapeT p f 0 .POmegaMinus 7 Ω u := hshape
    obtain ⟨e⟩ := Layer0.of_shape hΩ hex (by decide) (by decide) hshape'
    have hadm : StatedLieAdmissible .POmegaMinus 7 p f := ⟨Fact.out, hf1, by norm_num⟩
    have cq := Exotic.centralQuot_minus hp2 hq hadm
    have hQ : (polarBilin (quadMinus 7 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField p f) (minusCoeffs_irr p f)
    have hdim : 13 ≤ Module.finrank (GaloisField p f)
        (Fin (7 - 1) ⊕ Fin (7 - 1) ⊕ Fin 2 → GaloisField p f) := by
      rw [finrank_minus p f 7 (by norm_num)]
      norm_num
    exact exists_tilted_bridge_group hp2 hΩ hP1 e (yData_minus (by norm_num) hp2 hadm (by omega))
      (orthFacts_minus (m := 7) hp2 (by norm_num) hq) (exists_tilted_bridge_spin hp2 hq hQ hdim cq)
      nd hx

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.D6
