module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDRecognition
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBModel
public import CFSG.ClassicalInvolution.WeakCT.SpinOddWeak
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_spinOdd_subgroup_of_pair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable {G : Type} [Group G] {p f : ℕ} [hp : Fact p.Prime]

theorem exists_lieSystemData_of_chain_odd [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (U : Fin n → Subgroup G)
    (hU0 : U (zeroB (by omega)) ∈ Ω)
    (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (zeroB (by omega))))
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockPair (GaloisField p f) W (U i) (U j))
    (hgen : ⨆ k, U k = ⊤) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = n := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  set F := GaloisField p f with hFdef
  have hF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  have hadm : StatedLieAdmissible .POmegaOdd n p f := ⟨Fact.out, hf, hn, hp2⟩
  obtain ⟨Ψ, hker, hrange, hΨ⟩ := weakCT_spinOdd_subgroup_of_pair hadm hF h4 U hcomm hpair hsp
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT : FundamentalSingleClass .POmegaOdd (oddDatum n F) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n p f Fact.out hfundM
      hadm (by decide) (by decide)
  set n0 : Fin n := zeroB (by omega) with hn0
  have hlong0 : n0.val + 1 < n := by simp [n0, zeroB_val]; omega
  have hR₀ : rankOne (oddDatum n F).rootGroup n0 ∈
      fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn hlong0
  have hR₀ψ : (rankOne (oddDatum n F).rootGroup n0).map Ψ = U n0 := hΨ n0
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top, hrange]
    exact hgen
  have hconj_fund : ∀ s : spinGroup (quadOdd n F),
      conjSub s (rankOne (oddDatum n F).rootGroup n0) ∈
        fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    fun s => conjSub_mem_fundamentalSubgroups hR₀ s
  have hΩchar : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), L = R.map Ψ := by
    intro L
    constructor
    · intro hL
      obtain ⟨g, hg⟩ := hcls L hL
      obtain ⟨s, hs⟩ := hsurj g
      refine ⟨conjSub s (rankOne (oddDatum n F).rootGroup n0), hconj_fund s, ?_⟩
      rw [hg, ← hs, ← conjSub_map, hR₀ψ]
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨g, hg⟩ := hscT _ hR₀ R hR
      rw [hg, ← conjSub_map, hR₀ψ]
      exact hΩ _ _ hU0
  exact exists_lieSystemData_of_fundamental (t := .POmegaOdd) trivial hadm Ψ hsurj hker ⟨_, hR₀⟩
    hΩchar

theorem oddLieType_of_chain_odd [Finite G] [IsSimpleGroup G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 3 ≤ n) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (U : Fin n → Subgroup G)
    (hU0 : U (zeroB (by omega)) ∈ Ω)
    (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (zeroB (by omega))))
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockPair (GaloisField p f) W (U i) (U j))
    (hgen : ⨆ k, U k = ⊤) (hnab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.Blueprint.OddLieType G := by
  obtain ⟨D, -⟩ := exists_lieSystemData_of_chain_odd hp2 hq hn hΩ U hU0 hcls hcomm hpair hsp hgen
  exact CFSG.ClassicalInvolution.Generic.CoreAssembly.oddLieType_of_lieSystem (f := f) (Ω := Ω)
    hp2 hnab ⟨D⟩

theorem exists_lieSystemData_of_chain_minus [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 4 ≤ n) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) (U : Fin (n - 1) → Subgroup G) (hU0 : U (twIdx0 (by omega)) ∈ Ω)
    (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (twIdx0 (by omega))))
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (U i) (U j))
    (hgen : ⨆ k, U k = ⊤) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = n := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaMinus n p f := ⟨Fact.out, by omega, by show 4 ≤ n; omega⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hF]; omega
  set F := GaloisField p f with hFdef
  have hirr := minusCoeffs_irr p f
  obtain ⟨Ψ, hker, hrange, hblk⟩ := weakCT_spinMinus_subgroup hadm hp2 hF h4
    (minusCoeffs_irr p f) hg6 U hcomm hpair htw
  have hsingleN : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr),
      ∀ R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ∃ g, R' = conjSub g R :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus n p f Fact.out trivial
      hadm (by decide) (by decide)
  have hk0 : (twIdx0 hn3).val + 1 < n - 1 := by simp only [twIdx0]; omega
  have hr0 : (rankOne (minusDatum n hirr).rootGroup (twIdx0 hn3)).map Ψ = U (twIdx0 hn3) :=
    hblk _
  have hr0mem := rankOne_mem_fund_minus hirr hk0
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top, hrange]
    exact hgen
  have hΩchar : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), L = R.map Ψ := by
    intro L
    constructor
    · intro hL
      obtain ⟨g, hg⟩ := hcls L hL
      obtain ⟨s, hs⟩ := hsurj g
      refine ⟨conjSub s (rankOne (minusDatum n hirr).rootGroup (twIdx0 hn3)),
        conjSub_mem_fundamentalSubgroups hr0mem s, ?_⟩
      rw [hg, ← hs, ← conjSub_map, hr0]
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨g, hg⟩ := hsingleN _ hr0mem R hR
      rw [hg, ← conjSub_map, hr0]
      exact hΩ _ _ hU0
  exact exists_lieSystemData_of_fundamental (t := .POmegaMinus) trivial hadm Ψ hsurj hker
    ⟨_, hr0mem⟩ hΩchar

theorem oddLieType_of_chain_minus [Finite G] [IsSimpleGroup G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 4 ≤ n) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (U : Fin (n - 1) → Subgroup G)
    (hU0 : U (twIdx0 (by omega)) ∈ Ω)
    (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (twIdx0 (by omega))))
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (U i) (U j))
    (hgen : ⨆ k, U k = ⊤) (hnab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.Blueprint.OddLieType G := by
  obtain ⟨D, -⟩ := exists_lieSystemData_of_chain_minus hp2 hq hn hg6 hΩ U hU0 hcls hcomm hpair htw
    hgen
  exact CFSG.ClassicalInvolution.Generic.CoreAssembly.oddLieType_of_lieSystem (f := f) (Ω := Ω)
    hp2 hnab ⟨D⟩

end CFSG.ClassicalInvolution.Asc77
