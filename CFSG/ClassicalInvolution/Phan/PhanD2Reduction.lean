module

public import CFSG.ClassicalInvolution.Phan.PhanD1Family
public import CFSG.ClassicalInvolution.Asc77.AscR31Phan

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (Su)

@[expose] def PhanD4Universal (p f : ℕ) [Fact p.Prime] : Prop :=
  ∃ S : PhanFamilyD4 (GaloisField p (2 * f)) p f (spinGroup (quadPlus 4 (GaloisField p f))),
    (S.ι 0).range ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)) ∧
    ∀ (Y : Type) [Group Y] (F : PhanFamilyD4 (GaloisField p (2 * f)) p f Y),
      ∃ ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* Y,
        (∀ i, ψ.comp (S.ι i) = F.ι i) ∧ (∀ e, ψ.comp (S.θ e) = F.θ e)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G]


theorem exists_lieSystemData_of_hom_plus [Finite G] (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) (U₀ : Subgroup G) (hU₀ : U₀ ∈ Ω)
    (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g U₀)
    (ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* G) (hker : ψ.ker ≤ Subgroup.center _)
    (hsurj : Function.Surjective ψ) {R₀ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hR₀ψ : R₀.map ψ = U₀) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = 4 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨hp.out, hf, by show 4 ≤ 4; omega⟩
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag .POmegaPlus := trivial
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have e1 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadm (by decide)
      (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) := by
    revert hscT; rw [e1]; exact id
  have hconj_fund : ∀ s : spinGroup (quadPlus 4 (GaloisField p f)),
      conjSub s R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) := by
    intro s
    obtain ⟨g, γ, hγ, hg⟩ := hR₀
    exact ⟨s * g, γ, hγ, by rw [hg, conjSub_mul]⟩
  have hΩchar : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
        L = R.map ψ := by
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
      exact hΩ _ _ hU₀
  have hψ : ∃ ψ : (modelUniv .POmegaPlus 4 p f hp.out).K →* G,
      ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 4 p f hp.out).K ∧ Function.Surjective ψ ∧
      ∀ L : Subgroup G, L ∈ Ω ↔
        ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f hp.out).D,
          L = R.map ψ := by
    rw [e1]
    exact ⟨ψ, hker, hsurj, hΩchar⟩
  have hne : (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 p f hp.out).D).Nonempty := by
    rw [e1]
    exact ⟨R₀, hR₀⟩
  obtain ⟨ψ, hker, hsurj', hΩ'⟩ := hψ
  exact exists_lieSystemData_of_fundamental hfund hadm ψ hsurj' hker hne hΩ'

theorem phanD4Recognition_of_universal (hU : p ≠ 2 → 5 ≤ p ^ f → PhanD4Universal p f) :
    CFSG.ClassicalInvolution.Asc77.R31.PhanD4Recognition p f := by
  intro hp2 hq G _ _ _ Ω hΩ U hUΩ hcls hcomm hpair hgen
  obtain ⟨S, hfund, huniv⟩ := hU hp2 hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  obtain ⟨F, hFr, -, -⟩ := exists_family hK U (fun i j h1 h2 h3 => hcomm i j h1 h2 h3) hpair
  obtain ⟨ψ, hψι, -⟩ := huniv G F
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← hFr k, ← hψι k, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : IsQuasisimple (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isQuasisimple_spinGroup_quadPlus (by norm_num)
  have hnt : ∃ k, ψ k ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨k, rfl⟩ := hsurj g
    exact ⟨k, hg⟩
  have hker := ker_le_center_of_isQuasisimple hquasi hnt
  have hR₀ψ : (S.ι 0).range.map ψ = U 0 := by
    rw [← MonoidHom.range_comp, hψι 0, hFr 0]
  exact exists_lieSystemData_of_hom_plus hq hΩ (U 0) (hUΩ 0) hcls ψ hker hsurj hfund hR₀ψ

end CFSG.ClassicalInvolution.PhanD4
