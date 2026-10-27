module

public import CFSG.LieType.SeitzGeneration.OrthDfourPivot
public import CFSG.LieType.SeitzGeneration.OrthDfourProp
public import CFSG.LieType.SeitzGeneration.OrthDfourMix
public import CFSG.LieType.SeitzGeneration.OrthRestD4

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived)

section Top

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

theorem sup_eq_top_of_two_active (hK : KernelLineData Q p E) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p)
    (hother : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → M ≠ N → lineSpace M = ⊥) :
    planeFixSpace E ⊔ lineSpace L ⊔ lineSpace N = ⊤ := by
  classical
  refine top_le_iff.mp ?_
  rw [← hK.internal.submodule_iSup_eq_top]
  refine iSup_le fun i => ?_
  rcases i with _ | ⟨M, hM⟩
  · exact le_sup_of_le_left le_sup_left
  · by_cases hML : M = L
    · subst hML
      exact le_sup_of_le_left le_sup_right
    · by_cases hMN : M = N
      · subst hMN
        exact le_sup_right
      · have := hother M hM hML hMN
        change lineSpace M ≤ _
        rw [this]
        exact bot_le

end Top

section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem closure_eq_top_of_selfdual_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (hsd : HasSelfDualFactor Q E) (hV0 : finrank K ↥(planeFixSpace E) = 0)
    (hV8 : finrank K V = 8) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨L, N, hL, hN, hLN, hVL, hVN⟩ := hK.two_active
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  obtain ⟨a, ha, h, hh, hne1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    exists_mixing_factor_orth hQ hp hpl hK hL hN hLN hVL hVN
  have hx0 := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have haL : a ∉ L := not_mem_line_of_primary hx0 hh hne1 hvL hvh hv0
  have haN : a ∉ N := not_mem_line_of_primary hx0 hh hne1 hwN hwh hw0
  obtain ⟨x, hxa⟩ : ∃ x : V ≃ₗ[K] V, x = (((a : E) : orthDerived Q) : V ≃ₗ[K] V) := ⟨_, rfl⟩
  rw [← hxa] at hh hvh hwh hm2 hx0
  have hx : OddOrderIsometry Q p x := hx0
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    obtain ⟨a₁, ha₁, ha₁1, h₁, hh₁, hne₁, hself₁⟩ := hsd
    have : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
    have hx₁ := oddOrderIsometry_of_mem hQ hp hpl hK (x := (⟨a₁, ha₁⟩ : E))
      (fun e => ha₁1 (congrArg Subtype.val e))
    obtain ⟨d, -, -, -, -, -, hroot, -⟩ := hx₁.selfDualModel hodd hh₁ hne₁ hself₁
    exact selfDual_of_dvd hx hh (hx₁.dvd_card_pow_add_one hp hh₁ hne₁ hroot)
  have hStL : ∀ s ∈ lineSpace L, x s ∈ lineSpace L := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm L a hs
  have hStN : ∀ s ∈ lineSpace N, x s ∈ lineSpace N := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm N a hs
  have hneL : lineSpace L ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hv0 (by
    have : v ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hvL, hvh⟩
    simpa using this)
  have hneN : lineSpace N ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hw0 (by
    have : w ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hwN, hwh⟩
    simpa using this)
  have hAN : ∀ s ∈ lineSpace L, ∀ t ∈ lineSpace N, polar Q s t = 0 :=
    orthSep_lineSpace hK hL hN hLN
  obtain ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩ : ∃ u w' : primaryComponent x.toLinearMap h,
      (u : V) ∈ lineSpace L ∧ (w' : V) ∈ lineSpace N ∧ u ≠ 0 ∧ w' ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x h u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x h w')) := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨-, -, u, w', hu, hw', hu0, hw0', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action_even hx hp hp5 hh hne1 hself h2 hStL hStN
          (hK.regular (some ⟨L, hL⟩)) (hK.regular (some ⟨N, hN⟩)) hAN hneL hneN
      exact ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩
    · obtain ⟨u₀, hu₀, hQu₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStL
        (hK.regular (some ⟨L, hL⟩)) hneL
      obtain ⟨w₀, hw₀, hQw₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStN
        (hK.regular (some ⟨N, hN⟩)) hneN
      obtain ⟨-, -, u, w', hu, hw', hQu, hQw', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action hx hodd hh hne1 hself h2 hStN hAN ⟨u₀, hu₀, hQu₀⟩
          ⟨w₀, hw₀, hQw₀⟩
      exact ⟨u, w', hu, hw', fun h0 => hQu (by rw [h0]; simp),
        fun h0 => hQw' (by rw [h0]; simp), hureg, hwreg⟩
  have hLr : lineSpace L = LinearMap.range (eline x h u) :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hL hN hLN hVN haL hxa u hu hu0 hureg
  have hNr : lineSpace N = LinearMap.range (eline x h w') :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hN hL hLN.symm hVL haN hxa w' hw' hw0' hwreg
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdimL : finrank K ↥(lineSpace L) = h.natDegree := by
    rw [hLr, LinearMap.finrank_range_of_inj (eline_injective h hu0), hfin]
  have hdimN : finrank K ↥(lineSpace N) = h.natDegree := by
    rw [hNr, LinearMap.finrank_range_of_inj (eline_injective h hw0'), hfin]
  have hother : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → M ≠ N → lineSpace M = ⊥ := by
    intro M hM hML hMN
    by_contra hne
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hne with h' | h'
    · exact hML h'
    · exact hMN h'
  have hn := finrank_eq_of_two_active hK hL hN hLN hother
  obtain ⟨d, hdeg, -⟩ := hx.selfDualModel hodd hh hne1 hself
  have hn4 : h.natDegree = 4 := by omega
  have hd2 : 2 ≤ d := by omega
  have hV0' : planeFixSpace E = ⊥ := Submodule.finrank_eq_zero.mp hV0
  have htop : lineSpace L ⊔ lineSpace N = ⊤ := by
    have := sup_eq_top_of_two_active hK hL hN hother
    rwa [hV0', bot_sup_eq] at this
  obtain ⟨d', hdeg', c, hc0, hfam⟩ := exists_selfdual_mixing_family hx hodd hh hne1 hself hStN hAN
    u w' hu hw' hu0 hw0' hureg hwreg
  have hdd : d' = d := by omega
  subst hdd
  obtain ⟨θ, hθ, hθK⟩ := exists_trace_zero_sq_not_mem hd2 (by rw [hfin, hdeg'])
  obtain ⟨g, hgS, hact, hbal⟩ := hfam θ hθ
  have hθ0 : θ ≠ 0 := fun h0 => hθK 0 (by rw [h0]; simp)
  have hlam : 1 + θ ≠ 0 := fun h0 => hθK 1 (by
    have : θ = -1 := eq_neg_of_add_eq_zero_right h0
    rw [this]
    simp)
  have hmu : θ * c ≠ 0 := mul_ne_zero hθ0 hc0
  have hgΩ : g ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp (by omega) hh hne1 hm2 hgS
  obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hgS)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hgH : g ∈ orthCentralizerSpan Q E := by
    refine mem_orthCentralizerSpan_of_commute (a := (a : orthDerived Q)) hgΩ a.2
      (fun e => ha (Subtype.ext e)) ?_
    rw [← hxa]
    exact LinearEquiv.ext fun v => hgx v
  have hιAL : ∀ z, eline x h u z ∈ lineSpace L := fun z => hLr ▸ ⟨z, rfl⟩
  have hιBN : ∀ z, eline x h w' z ∈ lineSpace N := fun z => smul_mem_of_stable hStN z w' hw'
  have hpivot : ∀ s ∈ lineSpace N, s ≠ 0 → Q s = 0 →
      ∃ y ∈ lineSpace L, y ≠ 0 ∧ y ∈ rootSet Q (orthCentralizerSpan Q E) s := by
    intro s hsN hs0 hsQ
    refine exists_d4_pivot hK hp hEΩ hL hN hLN (eline x h u) (eline x h w')
      (LinearMap.mulLeft K (1 + θ)) (LinearMap.mulLeft K (θ * c)) (eline_injective h hw0')
      (mul_right_injective₀ hlam) (eline_injective h hu0) (mul_right_injective₀ hmu) hLr
      (by omega) ?_ g hgH hgO hact hιBN ?_ hsN hs0 hsQ
    · intro s' hs'
      rw [hNr] at hs'
      obtain ⟨z₀, rfl⟩ := hs'
      exact ⟨(θ * c)⁻¹ * z₀, by rw [LinearMap.mulLeft_apply, mul_inv_cancel_left₀ hmu]⟩
    · exact not_proportional_of_mixing (eline x h u) (eline x h w') g hgO (1 + θ) (θ * c)
        (1 - θ ^ 2) hact (fun z z' => hAN _ (hιAL z) _ (hιBN z')) hbal hureg
        (eline_injective h hu0) (fun c' h0 => hθK c' (by rw [← h0]; ring))
  have hAreg : PolarNondegOn Q (lineSpace L) :=
    polarNondegOn_of_nondegenerate (hK.regular (some ⟨L, hL⟩))
  have hNreg : PolarNondegOn Q (lineSpace N) :=
    polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hcenter : ∀ s ∈ lineSpace N, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthCentralizerSpan Q E) s := by
    intro s hsN hs0 hsQ
    obtain ⟨y₀, hy₀L, hy₀0, hy₀R⟩ := hpivot s hsN hs0 hsQ
    have hLR : ∀ a' ∈ lineSpace L, a' ∈ rootSet Q (orthCentralizerSpan Q E) s := by
      refine mem_of_invariant_of_ne_zero hAreg (by omega)
        (rootSet Q (orthCentralizerSpan Q E) s) ?_ hy₀R hy₀L hy₀0
      intro x₁ hx₁ z₁ hz₁ _ _ m hm _
      have hH : eichler Q x₁ z₁ ∈ orthCentralizerSpan Q E :=
        eichler_mem_span_of_mem_sup hEΩ hL0 (Submodule.mem_sup_right hx₁)
          (Submodule.mem_sup_right hz₁)
      have hfix : eichler Q x₁ z₁ s = s :=
        eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hAN x₁ hx₁ s hsN)
          (by rw [polar_comm]; exact hAN z₁ hz₁ s hsN)
      have := rootSet_map (orthCentralizerSpan_le_orthogonalGroup E) hH hm
      rwa [hfix] at this
    refine ⟨hs0, hsQ, fun w₁ hw₁ => ?_⟩
    obtain ⟨a', ha', b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := w₁))
    have hsa : polar Q s a' = 0 := by rw [polar_comm]; exact hAN a' ha' s hsN
    have hsb : polar Q s b = 0 := by
      rw [polar_add_right, hsa, zero_add] at hw₁
      exact hw₁
    have hbR : b ∈ rootSet Q (orthCentralizerSpan Q E) s :=
      ⟨hsb, eichler_mem_span_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN)
        (Submodule.mem_sup_right hb)⟩
    exact ((rootSet Q (orthCentralizerSpan Q E) s).add_mem (hLR a' ha') hbR).2
  obtain ⟨a₁, ha₁N, ha₁0, hQa₁⟩ :=
    exists_singular_of_three_le_any (Q := Q) (S := lineSpace N) (by omega)
  obtain ⟨f₁, hf₁N, hQf₁, h11⟩ := exists_partner_of_polarNondegOn hNreg ha₁N hQa₁ ha₁0
  have hf₁0 : f₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at h11
    exact zero_ne_one h11
  have hle : elementaryGroup Q ≤ orthCentralizerSpan Q E :=
    elementaryGroup_le_of_hypPair hQ (orthCentralizerSpan_le_orthogonalGroup E)
      ⟨a₁, f₁, hQa₁, hQf₁, h11⟩ (hcenter a₁ ha₁N ha₁0 hQa₁) (hcenter f₁ hf₁N hf₁0 hQf₁)
  exact closure_centralizers_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

end Main

end CFSG.LieType.SeitzGeneration.OrthBlk

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.RankThree.Classical CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

theorem orthSelfDualRestD4 : OrthSelfDualRestD4 := by
  intro K V _ _ _ _ _ Q hQ hT p hp hp5 hpl hrank E hcomm hexp hcard _ hsd h0 h8
  exact OrthBlk.closure_eq_top_of_selfdual_D4 hQ hT hp hp5 hpl hrank E hcomm hexp hcard hsd h0 h8

theorem orthSelfDualTwoBlocks : OrthSelfDualTwoBlocks :=
  orthSelfDualTwoBlocks_of_restD4 orthSelfDualRestD4

end CFSG.LieType.SeitzGeneration
