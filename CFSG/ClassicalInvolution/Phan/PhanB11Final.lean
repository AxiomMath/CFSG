module

public import CFSG.ClassicalInvolution.Phan.PhanB10Family
public import CFSG.ClassicalInvolution.Phan.PhanB8Tits
public import CFSG.ClassicalInvolution.Asc77.AscB3C2
import CFSG.ClassicalInvolution.Asc77.AscT7BChain23

public section

namespace CFSG.ClassicalInvolution.PhanB3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.B3C (PhanB3Recognition SymplecticPhanPair)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G]


theorem exists_lieSystemData_of_hom_odd [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (U₀ : Subgroup G) (hU₀ : U₀ ∈ Ω)
    (hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g U₀)
    (ψ : spinGroup (quadOdd 3 (GaloisField p f)) →* G) (hker : ψ.ker ≤ Subgroup.center _)
    (hsurj : Function.Surjective ψ) {R₀ : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)))
    (hR₀ψ : R₀.map ψ = U₀) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = 3 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨hp.out, hf, by norm_num, hp2⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT : FundamentalSingleClass .POmegaOdd (oddDatum 3 (GaloisField p f)) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd 3 p f Fact.out hfundM
      hadm (by decide) (by decide)
  have hconj_fund : ∀ s : spinGroup (quadOdd 3 (GaloisField p f)),
      conjSub s R₀ ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)) :=
    fun s => conjSub_mem_fundamentalSubgroups hR₀ s
  have hΩchar : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)), L = R.map ψ := by
    intro L
    constructor
    · intro hL
      obtain ⟨g, hg⟩ := hcls L hL
      obtain ⟨s, hs⟩ := hsurj g
      refine ⟨conjSub s R₀, hconj_fund s, ?_⟩
      rw [hg, ← hs, ← conjSub_map, hR₀ψ]
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨g, hg⟩ := hscT _ hR₀ R hR
      rw [hg, ← conjSub_map, hR₀ψ]
      exact hΩ _ _ hU₀
  exact exists_lieSystemData_of_fundamental (t := .POmegaOdd) trivial hadm ψ hsurj hker ⟨_, hR₀⟩
    hΩchar

@[expose] def PhanB3Universal (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → p ^ f % 4 = 3 →
    ∀ (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) (h2 : (2 : GaloisField p f) ≠ 0),
      ∃ (C : B2Coord hK (GaloisField p f) h2)
        (S : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))),
        (S.ι 0).range ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)) ∧
        ∀ (Y : Type) [Group Y] (E : PhanFamilyB3 C Y),
          ∃ ψ : spinGroup (quadOdd 3 (GaloisField p f)) →* Y, ∀ i, ψ.comp (S.ι i) = E.ι i

theorem phanB3Recognition_of_universal (hU : PhanB3Universal p f) : PhanB3Recognition p f := by
  intro hmod hp2 hq G _ _ _ Ω hΩ U hU0 hcls hcomm h01 h12 hgen
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  have h2F : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨C, S, hfund, huniv⟩ := hU hp2 hq hmod hK h2F
  obtain ⟨E, hE⟩ := exists_familyB3 C hq hmod hcomm h01 h12
  obtain ⟨ψ, hψ⟩ := huniv G E
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← hE k, ← hψ k, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : IsQuasisimple (spinGroup (quadOdd 3 (GaloisField p f))) :=
    isQuasisimple_spinGroup_quadOdd h2F (by norm_num)
  have hnt : ∃ k, ψ k ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨k, rfl⟩ := hsurj g
    exact ⟨k, hg⟩
  have hker := ker_le_center_of_isQuasisimple hquasi hnt
  have hR₀ψ : (S.ι 0).range.map ψ = U 0 := by
    rw [← MonoidHom.range_comp, hψ 0, hE 0]
  exact exists_lieSystemData_of_hom_odd hp2 hq hΩ (U 0) hU0 hcls ψ hker hsurj hfund hR₀ψ

end CFSG.ClassicalInvolution.PhanB3
