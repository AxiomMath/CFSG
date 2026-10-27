module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen69
public import CFSG.ClassicalInvolution.AschTight.Sec6GenCyc66
public import CFSG.ClassicalInvolution.AschTight.Sec6GenTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem eta_conj_of_sylow [Finite G] (hΩ : HypOmegaGen Ω)
    {S : Subgroup G} {η : Set (Subgroup G)} (hη : η ∈ etaSet Ω S)
    (habel : ∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x)
    (hUW : {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} = η) {K : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In (K ⊓ S) K) : ∀ r ∈ K ⊓ S, ∀ V ∈ η, conjSub r V ∈ η := by
  set R : Subgroup G := K ⊓ S with hRdef
  set W : Subgroup G := ⨆ U ∈ η, U with hWdef
  have hAW : ∀ A ∈ η, A ≤ W := fun A hA => le_iSup₂_of_le A hA le_rfl
  have hRS : R ≤ S := inf_le_right
  have hRK : R ≤ K := inf_le_left
  have hquat := isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨U₁, hU₁R, hcyc, hU₁card⟩ := hquat.exists_cyclic_index_two
  have hU₁ : U₁ ∈ USet Ω := mem_USet_of_natCard hK hR hU₁R hcyc hU₁card
  obtain ⟨V₀, hV₀η, hV₀K⟩ :=
    exists_mem_of_mem_etaSet hΩ hη hK ⟨hU₁, hU₁R.trans hRS⟩ (hU₁R.trans hRK)
  have hV₀U : V₀ ∈ USet Ω := (hη.1 hV₀η).1
  have hV₀R : V₀ ≤ R := le_inf hV₀K (hη.1 hV₀η).2
  have hV₀card : Nat.card R = 2 * Nat.card V₀ := by
    rw [hU₁card, natCard_eq_of_mem_USet hΩ hK hU₁ hV₀U (hU₁R.trans hRK) hV₀K]
  obtain ⟨zK, hzK⟩ := exists_uniqueInvolution hΩ hK
  have hV₀2 : IsPGroup 2 V₀ := isPGroup_of_mem_USet hΩ hV₀U
  have hV₀4 : 4 ≤ Nat.card V₀ := by
    obtain ⟨R', -, J, -, -, -, -, -, h4⟩ := exists_data_of_mem_USet hΩ hV₀U
    exact h4
  have hzV₀ : zK ∈ V₀ := mem_of_isUniqueInvolution_of_isPGroup hzK hV₀K hV₀2 (by omega)
  have hnormη : ∀ A ∈ η, ∀ a ∈ A, conjSub a R = R := by
    intro A hA a ha
    by_cases hAV : A = V₀
    · subst hAV
      exact conjSub_eq_self_of_mem (hV₀R ha)
    · have hAU : A ∈ USet Ω := (hη.1 hA).1
      obtain ⟨J, hJ, hAJ⟩ := exists_member_of_mem_USet hΩ hAU
      have hJK : K ≠ J := by
        rintro rfl
        exact hη.2.1 A hA V₀ hV₀η hAV K hK ⟨hAJ, hV₀K⟩
      have hA2 : IsPGroup 2 A := isPGroup_of_mem_USet hΩ hAU
      have hA4 : 4 ≤ Nat.card A := by
        obtain ⟨R', -, J', -, -, -, -, -, h4⟩ := exists_data_of_mem_USet hΩ hAU
        exact h4
      have hAc : A ≤ Subgroup.centralizer ({zK} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact habel x (hAW A hA hx) zK (hAW V₀ hV₀η hzV₀)
      have hAN := le_normalizer_of_le_centralizer hΩ hK hJ hJK hzK hAJ hA2 (by omega) hAc
      have hS : conjSub a S = S := conjSub_eq_self_of_mem ((hη.1 hA).2 ha)
      rw [hRdef, conjSub_inf, mem_normalizer_iff_conjSub_eq.mp (hAN ha), hS]
  have hconj : ∀ r ∈ R, ∀ A ∈ η, ∀ a ∈ A, r * a * r⁻¹ ∈ W := by
    intro r hr A hA a ha
    have haW : a ∈ W := hAW A hA ha
    have hnorm : ∀ x ∈ R, a⁻¹ * x * a ∈ R := by
      intro x hx
      have h1 := hnormη A hA a⁻¹ (A.inv_mem ha)
      have : a⁻¹ * x * a⁻¹⁻¹ ∈ conjSub a⁻¹ R := conj_mem_conjSub hx
      rw [h1] at this
      simpa using this
    have hcent : ∀ v ∈ V₀, a * v = v * a := fun v hv =>
      habel a haW v (hAW V₀ hV₀η hv)
    have h1 := inv_conj_mem_of_card_two_mul hV₀R hV₀card hnorm hcent hr
    set v : G := r⁻¹ * (a⁻¹ * r * a) with hv
    have hrav : r * a * r⁻¹ = a * (r * v * r⁻¹) := by
      rw [hv]
      group
    rw [hrav]
    exact W.mul_mem haW (hAW V₀ hV₀η (conj_mem_of_card_two_mul hV₀R hV₀card hr h1))
  intro r hr V hV
  have hle : conjSub r V ≤ W := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := hconj r hr V hV _ hx
    have hx' : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rwa [hx'] at this
  have hconjmem : conjSub r V ∈ USet Ω := USet.conj hΩ.conjInvariant (hη.1 hV).1 r
  have : conjSub r V ∈ {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} := ⟨hconjmem, hle⟩
  rwa [hUW] at this

theorem eta_acts_of_cyc66 [Finite G] (hΩ : HypOmegaGen Ω)
    (hC : Cyc66 Ω) {S : Sylow 2 G} {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) :
    (∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → ∀ r ∈ R, ∀ V ∈ η, conjSub r V ∈ η) ∧
    (∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ u ∈ U, ∀ V ∈ η, conjSub u V ∈ η) := by
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  obtain ⟨habel, hUW⟩ := eta_abelian_of_cyc66 hΩ hC hS₁ hinv
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  have hAW : ∀ A ∈ η, A ≤ ⨆ U ∈ η, U := fun A hA => le_iSup₂_of_le A hA le_rfl
  refine ⟨fun R hR hRS r hr V hV => ?_, fun U hU hUS u hu V hV => ?_⟩
  · obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    have hJS : J ⊓ (S : Subgroup G) = R :=
      hRJ.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hRJ.1 hRS)
    have hsyl : IsSylow2In (J ⊓ (S : Subgroup G)) J := hJS ▸ hRJ
    exact eta_conj_of_sylow hΩ hηS' habel hUW hJ hsyl r (hJS ▸ hr) V hV
  · obtain ⟨R₀, -, J, hJ, hR₀J, hUR₀, -, hcard, -⟩ := exists_data_of_mem_USet hΩ hU
    have hUJ : U ≤ J := hUR₀.trans hR₀J.1
    have hT2 : IsPGroup 2 ↥(J ⊓ (S : Subgroup G)) := S.isPGroup'.to_inf_right
    obtain ⟨R₁, hR₁, hTR₁⟩ := IsSylow2In.exists_ge hT2 (inf_le_left : J ⊓ (S : Subgroup G) ≤ J)
    have hR₁card : Nat.card R₁ = 2 * Nat.card U := by rw [← hcard, hR₁.natCard_eq hR₀J]
    have hUT : U ≤ J ⊓ (S : Subgroup G) := le_inf hUJ hUS
    rcases eq_or_eq_of_natCard_eq_two_mul hUT hTR₁ hR₁card with hT | hT
    ·
      obtain ⟨V₀, hV₀η, hV₀J⟩ := exists_mem_of_mem_etaSet hΩ hηS' hJ ⟨hU, hUS⟩ hUJ
      have hV₀U : V₀ ∈ USet Ω := (hηS'.1 hV₀η).1
      have hV₀T : V₀ ≤ U := hT ▸ le_inf hV₀J (hηS V₀ hV₀η)
      have hcard' := natCard_eq_of_mem_USet hΩ hJ hU hV₀U hUJ hV₀J
      have hUη : U ∈ η := by
        have : V₀ = U := Subgroup.eq_of_le_of_card_ge hV₀T hcard'.le
        exact this ▸ hV₀η
      have huW : u ∈ ⨆ U ∈ η, U := hAW U hUη hu
      have hcomm : Commutes (⨆ U ∈ η, U) V := fun x hx y hy =>
        habel x hx y (hAW V hV hy)
      rw [conjSub_eq_of_mem_of_commutes huW hcomm]
      exact hV
    · have hsyl : IsSylow2In (J ⊓ (S : Subgroup G)) J := hT ▸ hR₁
      exact eta_conj_of_sylow hΩ hηS' habel hUW hJ hsyl u (hUT hu) V hV

theorem l6_10Gen : L6_10Gen := by
  intro G _ _ Ω hΩ S η hη hηS
  exact eta_acts_of_cyc66 hΩ (cyc66 hΩ) hη hηS


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
