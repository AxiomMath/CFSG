module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard01Red
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Alt
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03L4U4Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverSz8
import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverAltBase

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup Blueprint GSYard02

@[expose] def CsfConcl (Q : Type) [Group Q] [Finite Q] : Prop := CentralSquareFour Q

theorem exists_normal_elemAbelian_of_sz8_cover {Q : Type} [Group Q]
    [Finite Q] (hz : center Q ≠ ⊥) (hcard : Nat.card (center Q) ≤ 2) (hr : 3 ≤ CFSG.pRank 2 Q)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    (e : Q ⧸ center Q ≃* suzukiGroup 1 K) :
    ∃ S : Sylow 2 Q, ∃ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) ∧
      (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (suzukiGroup 1 K) := Finite.of_equiv (Q ⧸ center Q) e.toEquiv
  have hsup : ∃ E : Subgroup Q, CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 2 ^ CFSG.pRank 2 Q := by
    have hne : {r : ℕ | ∃ A : Subgroup Q, CFSG.IsElementaryAbelian 2 A ∧
        Nat.card A = 2 ^ r}.Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      have h0 : CFSG.pRank 2 Q = 0 := by
        unfold CFSG.pRank
        rw [hem]
        simp
      omega
    have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup Q, CFSG.IsElementaryAbelian 2 A ∧
        Nat.card A = 2 ^ r} := by
      refine ⟨Nat.card Q, ?_⟩
      rintro r ⟨A, -, hA⟩
      have h1 := Subgroup.card_le_card_group A
      rw [hA] at h1
      exact (Nat.lt_two_pow_self (n := r)).le.trans h1
    unfold CFSG.pRank
    obtain ⟨A, hA, hAc⟩ := Nat.sSup_mem hne hbdd
    exact ⟨A, hA, hAc⟩
  obtain ⟨E, hEel, hEcard⟩ := hsup
  have h8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.pRank 2 Q := Nat.pow_le_pow_right (by norm_num) hr
  have hxx : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hZ2 : ∀ c ∈ center Q, c * c = 1 := by
    have hne1 : Nat.card (center Q) ≠ 1 := fun h => hz (Subgroup.card_eq_one.mp h)
    have hpos : 0 < Nat.card (center Q) := Nat.card_pos
    have h2 : Nat.card (center Q) = 2 := by omega
    intro c hc
    have hdvd := orderOf_dvd_natCard (⟨c, hc⟩ : center Q)
    rw [h2] at hdvd
    have hpow : (⟨c, hc⟩ : center Q) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hc2 : c ^ 2 = 1 := by
      have := congrArg Subtype.val hpow
      simpa using this
    rw [pow_two] at hc2
    exact hc2
  obtain ⟨S₀, hES⟩ : ∃ S₀ : Sylow 2 Q, E ≤ (S₀ : Subgroup Q) :=
    IsPGroup.exists_le_sylow (CFSG.IsElementaryAbelian.isPGroup 2 E)
  let T₁ : Sylow 2 (Q ⧸ center Q) := S₀.mapSurjective (QuotientGroup.mk'_surjective (center Q))
  let T₂ : Sylow 2 (suzukiGroup 1 K) := T₁.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT₂ : (T₂ : Subgroup (suzukiGroup 1 K)) =
      ((S₀ : Subgroup Q).map (QuotientGroup.mk' (center Q))).map e.toMonoidHom := rfl
  have hkey : ∀ s ∈ (S₀ : Subgroup Q), ∀ x ∈ E, ∃ d ∈ center Q, s * x * s⁻¹ = d * x := by
    intro s hs x hx
    refine ⟨s * x * s⁻¹ * x⁻¹, ?_, by group⟩
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact hxx x hx
    have hmem₁ : e (QuotientGroup.mk' (center Q) x) ∈ (T₂ : Subgroup (suzukiGroup 1 K)) := by
      rw [hT₂]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hES hx))
    have hmem₂ : e (QuotientGroup.mk' (center Q) s) ∈ (T₂ : Subgroup (suzukiGroup 1 K)) := by
      rw [hT₂]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs)
    have hsq : e (QuotientGroup.mk' (center Q) x) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, hx2, map_one, map_one]
    have hcomm := GSYard02.suzuki_sylow_involution_central hK T₂ _ hmem₁ hsq _ hmem₂
    have hcomm' : QuotientGroup.mk' (center Q) x * QuotientGroup.mk' (center Q) s =
        QuotientGroup.mk' (center Q) s * QuotientGroup.mk' (center Q) x := by
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm
    have hone : QuotientGroup.mk' (center Q) (s * x * s⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm']
      group
    exact (QuotientGroup.eq_one_iff (s * x * s⁻¹ * x⁻¹)).mp hone
  have hconj : ∀ s ∈ (S₀ : Subgroup Q), ∀ a ∈ E ⊔ center Q, s * a * s⁻¹ ∈ E ⊔ center Q := by
    intro s hs a ha
    obtain ⟨x, hx, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨d, hd, hsx⟩ := hkey s hs x hx
    have hsc : s * c * s⁻¹ = c := by
      rw [(Subgroup.mem_center_iff.mp hc) s]
      group
    have hdx : x * d = d * x := (Subgroup.mem_center_iff.mp hd) x
    rw [Subgroup.mem_sup_of_normal_right]
    refine ⟨x, hx, d * c, mul_mem hd hc, ?_⟩
    calc x * (d * c) = (x * d) * c := by group
      _ = (d * x) * c := by rw [hdx]
      _ = (s * x * s⁻¹) * (s * c * s⁻¹) := by rw [hsx, hsc]
      _ = s * (x * c) * s⁻¹ := by group
  have hSA : (S₀ : Subgroup Q) ≤ normalizer ((E ⊔ center Q : Subgroup Q) : Set Q) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hconj s hs a ha
    · intro ha
      have h := hconj s⁻¹ (inv_mem hs) (s * a * s⁻¹) ha
      have h2 : s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a := by group
      rw [h2] at h
      exact h
  have hA2 : ∀ a ∈ E ⊔ center Q, a * a = 1 := by
    intro a ha
    obtain ⟨x, hx, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    have hxc : x * c = c * x := (Subgroup.mem_center_iff.mp hc) x
    calc x * c * (x * c) = x * (c * x) * c := by group
      _ = x * (x * c) * c := by rw [← hxc]
      _ = (x * x) * (c * c) := by group
      _ = 1 := by rw [hxx x hx, hZ2 c hc, mul_one]
  have hA8 : 8 ≤ Nat.card (E ⊔ center Q : Subgroup Q) :=
    h8.trans (Subgroup.card_le_of_le le_sup_left)
  exact ⟨S₀, E ⊔ center Q, hSA, hA2, hA8⟩

theorem csfLeafSz8_holds
    : CoverLeafSz8For CsfConcl := by
  intro Q _ _ hQ hLie
  have hcard : Nat.card (center Q) ≤ 2 :=
    ((CFSG.GH74.E2.e2ComponentFacts).sz8_cover Q hQ.1 hQ.2.2.1 hLie).resolve_right
      (fun h => h hQ.2.2.2.2.2)
  rcases hLie with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain rfl : a = 1 := by omega
    exact centralSquareFour_of_exists_normal_elemAbelian hQ.2.2.1
      (exists_normal_elemAbelian_of_sz8_cover hQ.2.1 hcard hQ.2.2.2.2.1 (by rw [hK]) e)

section Alt

open CFSG.Alternating.Multipliers.Spin Equiv Equiv.Perm
open scoped commutatorElement

private theorem altConjCentral {G : Type} [Group G] {a g : G} (ha : a ∈ center G) :
    a * g * a⁻¹ = g := by
  rw [← Subgroup.mem_center_iff.mp ha g]; group

private theorem altCommutatorMulCentralLeft {G : Type} [Group G] {a u w : G}
    (ha : a ∈ center G) : ⁅a * u, w⁆ = ⁅u, w⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * u * w * (a * u)⁻¹ * w⁻¹ = (a * (u * w * u⁻¹) * a⁻¹) * w⁻¹ := by group
    _ = u * w * u⁻¹ * w⁻¹ := by rw [altConjCentral ha]

private theorem altCommutatorMulCentralRight {G : Type} [Group G] {b u v : G}
    (hb : b ∈ center G) : ⁅u, b * v⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc u * (b * v) * u⁻¹ * (b * v)⁻¹ = (u * b) * v * u⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = (b * u) * v * u⁻¹ * v⁻¹ * b⁻¹ := by rw [Subgroup.mem_center_iff.mp hb u]
    _ = b * (u * v * u⁻¹ * v⁻¹) * b⁻¹ := by group
    _ = u * v * u⁻¹ * v⁻¹ := altConjCentral hb

private theorem altCommE {m : ℕ} (hm : 6 ≤ m) {p q s t : Fin (m + 2)} (hpq : p ≠ q) (hps : p ≠ s)
    (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) (e₁ e₂ : E (m + 2))
    (h₁ : permH (n := m + 2) (e₁ : H (m + 2)) = swap p q * swap s t)
    (h₂ : permH (n := m + 2) (e₂ : H (m + 2)) = swap p s * swap q t) :
    e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = negE (m := m) (by omega) := by
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : H (m + 2), (d₁ : monomial (m + 2)) = dd hpq hst :=
    ⟨⟨dd hpq hst, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d₂ : H (m + 2), (d₂ : monomial (m + 2)) = dd hps hqt :=
    ⟨⟨dd hps hqt, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩, rfl⟩
  have hp₁ : permH (n := m + 2) d₁ = swap p q * swap s t := by
    show perm (d₁ : monomial (m + 2)) = _
    rw [hd₁, perm_dd]
  have hp₂ : permH (n := m + 2) d₂ = swap p s * swap q t := by
    show perm (d₂ : monomial (m + 2)) = _
    rw [hd₂, perm_dd]
  have hk₁ : (e₁ : H (m + 2))⁻¹ * d₁ ∈ (permH (n := m + 2)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, hp₁, inv_mul_cancel]
  have hk₂ : (e₂ : H (m + 2))⁻¹ * d₂ ∈ (permH (n := m + 2)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h₂, hp₂, inv_mul_cancel]
  obtain ⟨k₁, hk₁def⟩ : ∃ k₁, k₁ = (e₁ : H (m + 2))⁻¹ * d₁ := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂def⟩ : ∃ k₂, k₂ = (e₂ : H (m + 2))⁻¹ * d₂ := ⟨_, rfl⟩
  rw [← hk₁def] at hk₁
  rw [← hk₂def] at hk₂
  have hc₁ : k₁ ∈ center (H (m + 2)) := ker_permH_le_center hk₁
  have hc₂ : k₂ ∈ center (H (m + 2)) := ker_permH_le_center hk₂
  have hd₁' : d₁ = k₁ * (e₁ : H (m + 2)) := by
    rw [← Subgroup.mem_center_iff.mp hc₁ (e₁ : H (m + 2)), hk₁def]; group
  have hd₂' : d₂ = k₂ * (e₂ : H (m + 2)) := by
    rw [← Subgroup.mem_center_iff.mp hc₂ (e₂ : H (m + 2)), hk₂def]; group
  have key : ⁅d₁, d₂⁆ = ⁅(e₁ : H (m + 2)), (e₂ : H (m + 2))⁆ := by
    rw [hd₁', hd₂', altCommutatorMulCentralLeft hc₁, altCommutatorMulCentralRight hc₂]
  have hval : ((⁅d₁, d₂⁆ : H (m + 2)) : monomial (m + 2)) = negOne := by
    have h := commutator_dd hpq hps hpt hqs hqt hst
    rw [← hd₁, ← hd₂] at h
    exact h
  rw [key] at hval
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_negE]
  exact hval

private noncomputable def altDblCoverE {m : ℕ} (hm : 6 ≤ m) : AltDblCover (E (m + 2)) (m + 2) where
  φ := (permH (n := m + 2)).comp (E (m + 2)).subtype
  z := negE (m := m) (by omega)
  sign_eq_one g := by
    have hmem : permH (n := m + 2) (g : H (m + 2)) ∈ alternatingGroup (Fin (m + 2)) := by
      rw [← range_permH]; exact ⟨(g : H (m + 2)), rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp hmem
  surj σ hσ := by
    obtain ⟨e, he⟩ := psi_surjective (m := m) (by omega)
      ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
    exact ⟨e, congrArg Subtype.val he⟩
  ker_iff g := by
    constructor
    · intro h
      exact ker_psi_eq hm g (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact map_one _
      · exact congrArg Subtype.val (psi_negE (m := m) (by omega))
  z_ne_one := negE_ne_one _
  z_mem_center := by
    rw [center_E_eq hm]; exact MonoidHom.mem_ker.mpr (psi_negE _)
  center_le g hg := ker_psi_eq hm g (by
    rw [center_E_eq hm] at hg; exact MonoidHom.mem_ker.mp hg)
  comm := fun hpq hps hpt hqs hqt hst e₁ e₂ h₁ h₂ =>
    altCommE hm hpq hps hpt hqs hqt hst e₁ e₂ h₁ h₂

theorem csfLeafAlt_holds : CoverLeafAltFor CsfConcl := by
  intro Q _ _ hQ n hn8 hn11 hQA
  obtain ⟨eQ⟩ := hQA
  obtain ⟨hquasi, hz, h2, -, -, -⟩ := hQ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 6 ≤ m := by omega
  have hzQ : Nat.card (center Q) = 2 := card_center_of_cover hquasi hz h2 (by omega) eQ
  have hGr : Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_griess_alt (by omega)
  have : Finite (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    Nat.finite_of_card_ne_zero (by rw [hGr]; norm_num)
  have := finite_E hm
  obtain ⟨e⟩ := (RankThree.PerfectCover.hopf_central_cover_consequences
    (alternatingGroup (Fin (m + 2)))).2 (fun S => card_sylow_of_card_two hGr S) Q (E (m + 2))
    hquasi (isQuasisimple_E hm) hzQ (card_center_E hm) ⟨eQ⟩ (quotCenter_E hm)
  exact CentralSquareFour.of_mulEquiv e.symm
    ((altDblCoverE hm).centralSquareFour (by omega) (by omega))

end Alt

theorem csfLeafL4_holds
    : CoverLeafL4For CsfConcl := by
  intro Q _ _ hQ p f hp hp2 _ _ h
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨F, _, _, h2F, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSL4_of_coverHyp (CFSG.GH74.Generic.genericKnownFacts_of_griess hGA) hQ
      hp hp2 h
  exact CentralSquareFour.of_mulEquiv e (centralSquareFour_statedSL4 h2F)

theorem csfLeafU4_holds
    : CoverLeafU4For CsfConcl := by
  intro Q _ _ hQ p f hp hp2 hf _ h
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSU4_of_coverHyp (CFSG.GH74.Generic.genericKnownFacts_of_griess hGA) hQ
      hp hp2 hf h
  have : Fact p.Prime := ⟨hp⟩
  exact CentralSquareFour.of_mulEquiv e (centralSquareFour_statedSU4 hp2 hK)

theorem csfLeafM12_holds
    : CoverLeafM12For CsfConcl := by
  intro Q _ _ hQ hM
  obtain ⟨S, A, -, hSA, hA2, hA8⟩ :=
    exists_normal_elemAbelian_of_m12_cover hQ.1 hQ.2.1 hQ.2.2.1 hM
  exact centralSquareFour_of_exists_normal_elemAbelian hQ.2.2.1
    ⟨S, A, hSA, hA2, hA8⟩

theorem centralSquareFour_of_quasisimple_catalogue
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    (hcat : Blueprint.Catalog (Q ⧸ center Q)) (hr : 3 ≤ CFSG.pRank 2 Q) (hz : center Q ≠ ⊥)
    (hZ : ∀ Z : Subgroup Q, Z ≤ center Q → ¬ IsKleinFour Z) : CentralSquareFour Q := by
  have h2 : IsPGroup 2 (center Q) := center_isPGroup_two_of_pPrimeCore_eq_bot hO
  by_cases hS : ∃ S : Sylow 2 Q, ∀ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) →
      (∀ a ∈ A, a * a = 1) → Nat.card A < 8
  · obtain ⟨S, hS8⟩ := hS
    have hgen : GH74.Gen4 Q := fun P hP => fourGenerated_of_noNormalEight S hS8 P hP
    have hCov : CoverHyp Q := ⟨hQ, hz, h2, center_isCyclic_of_no_kleinFour h2 hZ, hr, hgen⟩
    by_cases hlow : Open.twoRank (Q ⧸ center Q) ≤ 2
    · exact (coverLow_holds Q hCov hlow).elim
    · have hGH : GH74.GH74Conclusion (Q ⧸ center Q) :=
        GH74.Filter.filter _ hcat hQ.2.2 (by omega) (GH74.Gen4.quotient _ hgen)
      exact coverGH_of_leaves_for CsfConcl csfLeafL4_holds csfLeafU4_holds csfLeafSz8_holds
        csfLeafAlt_holds csfLeafM12_holds Q hCov hGH
  · refine centralSquareFour_of_normal_elemAbelian h2 fun S => ?_
    by_contra hne
    refine hS ⟨S, fun A hSA hA2 => ?_⟩
    by_contra hlt
    exact hne ⟨A, hSA, hA2, not_lt.mp hlt⟩

theorem quasisimpleCentralSquareFourI_holds
    : QuasisimpleCentralSquareFourI :=
  fun _ _ _ hQ hO hcat hr hz hZ _ _ =>
    centralSquareFour_of_quasisimple_catalogue hQ hO hcat hr hz hZ

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
