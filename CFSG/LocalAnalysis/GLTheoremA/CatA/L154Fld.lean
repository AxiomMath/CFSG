module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FP


@[expose] def NIDFacts (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  (¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → GGOddAutInnField p I F) ∧
    (¬ (lab.tag = .triD4 ∧ p = 3) → ConjBody p R I F)

theorem canonNIDFacts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : CAll lab (LargeEvenSimpleGuard (NIDFacts p lab)) := by
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
      rintro ⟨h, -⟩
      rw [hD.1] at h
      exact absurd h (by decide)
    refine (canonRawFieldConj hp hp2 hlab h3).mono ?_
    rintro R _ I F hL hs hna
    exact ⟨fun h => absurd hD h, fun _ => hL hs hna⟩
  · by_cases h3 : lab.tag = .triD4 ∧ p = 3
    · refine (canonOddAut hp hp2 hlab hD).mono ?_
      rintro R _ I F hO hs hna
      exact ⟨fun _ => hO hs hna, fun h => absurd h3 h⟩
    · refine ((canonOddAut hp hp2 hlab hD).and (canonRawFieldConj hp hp2 hlab h3)).mono ?_
      rintro R _ I F ⟨hO, hL⟩ hs hna
      exact ⟨fun _ => hO hs hna, fun _ => hL hs hna⟩

variable {G : Type} [Group G] [Finite G]

theorem fieldOn_of_notInner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgp : g ^ p = 1)
    (hP : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I _ θ =>
      (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧ ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) ∧
        MulAut.congr θ (indAut p L g hg) ∉ I) :
    FieldOn p g L := by
  have h := canon_marking_and_labelAll_simple' (P' := fun lab => NIDFacts p lab)
    (fun lab hlab => canonNIDFacts hp hp2 hlab) hP
  refine ⟨hg, Canonical.largeEvenMarking_mono ?_ h⟩
  rintro lab R _ I F θ ⟨⟨hlt, hD, hnot⟩, hO, hLS⟩
  have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, h'⟩
    rcases hlt with h0 | h0
    · exact h0 h
    · exact h0 h'
  have hpα : MulAut.congr θ (indAut p L g hg) ^ p = 1 := by
    have h1 : indAut p L g hg ^ p = 1 := by
      have e : (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
        Subtype.ext (by simp [inv_pow, hgp])
      show chevAut p L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ ^ p = 1
      rw [← map_pow, e, map_one]
    rw [← map_pow, h1, map_one]
  obtain ⟨u, hu, f, hf, huf⟩ := hO hD _ hpα
  have hnot' : u * f ∉ I := huf ▸ hnot
  have hpow : (u * f) ^ p = 1 := huf ▸ hpα
  obtain ⟨f', hf', u', hu', hord, heq⟩ := hLS h3 u hu f hf hnot' hpow
  refine ⟨hlt, f', hf', u', hu', hord, (induces_indRel_iff hg θ).2 ?_⟩
  rw [← heq, ← huf]

end CFSG.LocalAnalysis.GLTheoremA.K155X
