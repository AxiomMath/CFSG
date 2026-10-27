module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitness

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_fiveCycleLine_not_le {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    {U : Subgroup G} (hU : IIPlane 5 P x J U) (hγ : A10PlaneShape J (u3T P x J) ψ U)
    {A : Subgroup G} (hA : IsFiveCycleLine J (u3T P x J) ψ A) : ¬ A ≤ U := by
  intro hAU
  obtain ⟨hAT, hAcard, a, ha, haA, hψa, hcent⟩ := hA
  obtain ⟨d, hd, hdUT, hψd, hcentd⟩ := hγ
  have hAeq : A = U ⊓ u3T P x J :=
    Subgroup.eq_of_le_of_card_ge (le_inf hAU hAT) (by rw [hU.card_inf, hAcard])
  have hdA : d ∈ A := hAeq ▸ hdUT
  have ha1 : a ≠ 1 := by
    intro h
    apply hψa
    have : (⟨a, ha⟩ : ↥J) = 1 := Subtype.ext h
    rw [this, map_one]
  have hAgen : A = Subgroup.zpowers a :=
    eq_zpowers_of_card_prime (p := 5) (by norm_num) hAcard haA ha1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hAgen ▸ hdA)
  have hψdk : ψ ⟨d, hd⟩ = (ψ ⟨a, ha⟩) ^ k := by
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk.symm)
  have hle : Subgroup.centralizer ({ψ ⟨a, ha⟩} : Set Q) ≤
      Subgroup.centralizer ({ψ ⟨d, hd⟩} : Set Q) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [hψdk]
    exact (Commute.zpow_right (hc : Commute c (ψ ⟨a, ha⟩)) k).eq
  have := Subgroup.card_le_of_le hle
  rw [hcent, hcentd] at this
  omega

theorem a10_lemma42_i {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hB : A10StageB P x J ψ)
    {U : Subgroup G} (hU : IIPlane 5 P x J U) (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ U →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  intro g hg
  have hUP : U ≤ (P : Subgroup G) := hU.le.trans inf_le_left
  have hmem : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∈ conjLines x (P : Subgroup G) :=
    ⟨g, rfl, hg.trans hUP⟩
  obtain ⟨-, hB2⟩ := hB
  rcases hB2 with h1 | ⟨A₁, A₂, hne, hA₁, hA₂, h3⟩
  · rw [h1] at hmem
    exact hmem
  · rw [h3] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact h
    · exact absurd (h ▸ hg) (a10_fiveCycleLine_not_le ψ hU hγ hA₁)
    · exact absurd (h ▸ hg) (a10_fiveCycleLine_not_le ψ hU hγ hA₂)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
