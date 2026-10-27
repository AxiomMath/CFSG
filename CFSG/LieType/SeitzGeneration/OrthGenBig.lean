module

public import CFSG.LieType.SeitzGeneration.OrthGenPivot
public import CFSG.LieType.SeitzGeneration.OrthEvenMixing

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem closure_eq_top_of_selfdual_or_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) (hsd : HasSelfDualFactor Q E) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ ∨
      (finrank K ↥(planeFixSpace E) = 0 ∧ finrank K V = 8) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨L, N, hL, hN, hLN, hVL, hVN⟩ := hK.two_active
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
  obtain ⟨g, hgS, u, w', hu, hw', hu0, hw0', hureg, hwreg, lam, mu, hlam, hmu, hact⟩ :
      ∃ g ∈ specialBlock Q x h, ∃ u w' : primaryComponent x.toLinearMap h,
        (u : V) ∈ lineSpace L ∧ (w' : V) ∈ lineSpace N ∧ u ≠ 0 ∧ w' ≠ 0 ∧
        PolarNondegOn Q (LinearMap.range (eline x h u)) ∧
        PolarNondegOn Q (LinearMap.range (eline x h w')) ∧
        ∃ lam mu : AdjoinRoot h, lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ z : AdjoinRoot h,
          g (eline x h u z) = eline x h u (lam * z) + eline x h w' (mu * z) := by
    by_cases h2 : (2 : K) = 0
    · exact exists_selfdual_mixing_action_even hx hp hp5 hh hne1 hself h2 hStL hStN
        (hK.regular (some ⟨L, hL⟩)) (hK.regular (some ⟨N, hN⟩)) (orthSep_lineSpace hK hL hN hLN)
        hneL hneN
    · obtain ⟨u₀, hu₀, hQu₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStL
        (hK.regular (some ⟨L, hL⟩)) hneL
      obtain ⟨w₀, hw₀, hQw₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStN
        (hK.regular (some ⟨N, hN⟩)) hneN
      obtain ⟨g, hgS, u, w', hu, hw', hQu, hQw', hureg, hwreg, lam, mu, hlam, hmu, hact⟩ :=
        exists_selfdual_mixing_action hx hodd hh hne1 hself h2 hStN
          (orthSep_lineSpace hK hL hN hLN) ⟨u₀, hu₀, hQu₀⟩ ⟨w₀, hw₀, hQw₀⟩
      exact ⟨g, hgS, u, w', hu, hw', fun h0 => hQu (by rw [h0]; simp),
        fun h0 => hQw' (by rw [h0]; simp), hureg, hwreg, lam, mu, hlam, hmu, hact⟩
  obtain ⟨d, hdeg, -⟩ := hx.selfDualModel hodd hh hne1 hself
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
  have hV₀ : finrank K ↥(planeFixSpace E) ≤ 2 := by
    by_contra hcon
    obtain ⟨e, he, he0, heQ⟩ := exists_singular_of_three_le_any (Q := Q)
      (S := planeFixSpace E) (by omega)
    exact he0 (haniso e he heQ)
  by_cases hD : 0 < finrank K ↥(planeFixSpace E) ∨ 8 < finrank K V
  swap
  · right
    push Not at hD
    omega
  left
  have h3N : 3 ≤ finrank K ↥(lineSpace N) := by omega
  have hdimUL : finrank K ↥(planeFixSpace E ⊔ lineSpace L) =
      finrank K ↥(planeFixSpace E) + h.natDegree := by
    rw [finrank_sup_of_disjoint (disjoint_planeFixSpace_lineSpace hK hL), hdimL]
  have hdimUN : finrank K ↥(planeFixSpace E ⊔ lineSpace N) =
      finrank K ↥(planeFixSpace E) + h.natDegree := by
    rw [finrank_sup_of_disjoint (disjoint_planeFixSpace_lineSpace hK hN), hdimN]
  have h5 : 5 ≤ finrank K ↥(planeFixSpace E) + h.natDegree := by omega
  have hgΩ : g ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp (by omega) hh hne1 hm2 hgS
  obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hgS)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hgH : g ∈ orthCentralizerSpan Q E := by
    refine mem_orthCentralizerSpan_of_commute (a := (a : orthDerived Q)) hgΩ a.2
      (fun e => ha (Subtype.ext e)) ?_
    rw [← hxa]
    exact LinearEquiv.ext fun v => hgx v
  have hg0 : ∀ v ∈ planeFixSpace E, g v = v := fun v hv =>
    (mem_supportedBlock.mp (specialBlock_le_supportedBlock h hgS)).2 v
      (fixedSpace_le_othersSpace hne1 hself (mem_fixedSpace.mpr (by
        rw [hxa]; exact apply_eq_of_mem_planeFixSpace a hv)))
  have hpiv := exists_pivot_of_mixing_gen hK hp hEΩ hL hN hLN haniso (eline x h u)
    (eline x h w') (LinearMap.mulLeft K lam) (LinearMap.mulLeft K mu) (eline_injective h hu0)
    (eline_injective h hw0') (mul_right_injective₀ hlam) (mul_right_injective₀ hmu) hLr g hgH hgO
    hg0 hact (fun z => smul_mem_of_stable hStN z w' hw') (by omega) (by omega) h3N
  have hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N) :=
    hasOrthPairs_of_dim (polarNondegOn_of_nondegenerate (regular_sup hK hN)) (by omega)
  have hPL : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace L) :=
    hasOrthPairs_of_dim (polarNondegOn_of_nondegenerate (regular_sup hK hL)) (by omega)
  have hle : elementaryGroup Q ≤ orthCentralizerSpan Q E := by
    refine elementaryGroup_le_span_of_pivots hK hEΩ hp hQ hN hPN fun M hM hMN hVM => ?_
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hVM with h' | h'
    · subst h'
      exact ⟨hPL, hpiv⟩
    · exact absurd h' hMN
  exact closure_centralizers_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

end Main

end CFSG.LieType.SeitzGeneration.OrthBlk
