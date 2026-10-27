module

public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {G : Type} [Group G] {p f : ℕ} [hp : Fact p.Prime]

theorem exists_lieSystemData_of_chain_plus [Finite G] (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 4 ≤ n)
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (U : Fin n → Subgroup G)
    (hUΩ : ∀ k, U k ∈ Ω) (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (zeroD (by omega))))
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hgen : ⨆ k, U k = ⊤) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = n := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp.out, hf, by show 4 ≤ n; omega⟩
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag .POmegaPlus := trivial
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have e1 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus n p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadm (by decide)
      (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum n (GaloisField p f) hn3) := by
    revert hscT; rw [e1]; exact id
  obtain ⟨ψ0, hker0, hψ0⟩ := exists_psi_of_chain_plus hadm (by omega) U hcomm hpair
  set R₀ := rankOne (plusDatum n (GaloisField p f) hn3).rootGroup (zeroD (n := n) (by omega))
    with hR₀def
  have hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3) :=
    rankOne_mem_fundamentalSubgroups_plusDatum hn3 _
  have hR₀ψ : R₀.map ψ0 = U (zeroD (n := n) (by omega)) := hψ0 _
  have hsurj : Function.Surjective ψ0 := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← hψ0 k]
    exact Subgroup.map_le_range ψ0 _
  have hconj_fund : ∀ s : spinGroup (quadPlus n (GaloisField p f)),
      conjSub s R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3) := by
    intro s
    obtain ⟨g, γ, hγ, hg⟩ := hR₀
    exact ⟨s * g, γ, hγ, by rw [hg, conjSub_mul]⟩
  have hΩchar : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3),
        L = R.map ψ0 := by
    intro L
    constructor
    · intro hL
      obtain ⟨g, hg⟩ := hcls L hL
      obtain ⟨s, hs⟩ := hsurj g
      refine ⟨conjSub s R₀, hconj_fund s, ?_⟩
      rw [hg, ← hs, ← conjSub_map, hR₀ψ]
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨g, hg⟩ := hscT' R₀ hR₀ R hR
      rw [hg, ← conjSub_map, hR₀ψ]
      exact hΩ _ _ (hUΩ _)
  have hψ : ∃ ψ : (modelUniv .POmegaPlus n p f hp.out).K →* G,
      ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus n p f hp.out).K ∧ Function.Surjective ψ ∧
      ∀ L : Subgroup G, L ∈ Ω ↔
        ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f hp.out).D,
          L = R.map ψ := by
    rw [e1]
    exact ⟨ψ0, hker0, hsurj, hΩchar⟩
  have hne : (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n p f hp.out).D).Nonempty := by
    rw [e1]
    exact ⟨R₀, hR₀⟩
  obtain ⟨ψ, hker, hsurj', hΩ'⟩ := hψ
  exact exists_lieSystemData_of_fundamental hfund hadm ψ hsurj' hker hne hΩ'

theorem oddLieType_of_chain_plus [Finite G] [IsSimpleGroup G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 4 ≤ n) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (U : Fin n → Subgroup G)
    (hUΩ : ∀ k, U k ∈ Ω) (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (zeroD (by omega))))
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hgen : ⨆ k, U k = ⊤) (hnab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.Blueprint.OddLieType G := by
  obtain ⟨D, -⟩ := exists_lieSystemData_of_chain_plus hq hn hΩ U hUΩ hcls hcomm hpair hgen
  exact CFSG.ClassicalInvolution.Generic.CoreAssembly.oddLieType_of_lieSystem (f := f) (Ω := Ω)
    hp2 hnab ⟨D⟩

end CFSG.ClassicalInvolution.Asc77
