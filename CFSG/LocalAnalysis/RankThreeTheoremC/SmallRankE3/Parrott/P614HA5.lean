module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HKbar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

theorem kbarA5_of_a5Case (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (hA : A5Case H S K) : KbarA5 H K := by
  obtain ⟨f, hfs, hfk⟩ := hA
  let ι : K →* ↥(K ⊔ S) := inclusion le_sup_left
  let g : K →* Equiv.Perm (Fin 5) := f.comp ι
  have hsign : ∀ k : K, Equiv.Perm.sign (g k) = 1 := by
    intro k
    have hk : k ∈ commutator K := by
      rw [commutator_K_eq_top h618]
      trivial
    have h := Abelianization.commutator_subset_ker ((Equiv.Perm.sign).comp g) hk
    rwa [MonoidHom.mem_ker, MonoidHom.comp_apply] at h
  let g' : K →* alternatingGroup (Fin 5) :=
    g.codRestrict (alternatingGroup (Fin 5))
      fun k => Equiv.Perm.mem_alternatingGroup.mpr (hsign k)
  have hg'k : ∀ k : K, ((g' k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = f (ι k) :=
    fun k => rfl
  have hker : ∀ k : K, g' k = 1 ↔ f (ι k) = 1 := by
    intro k
    rw [← hg'k]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  refine ⟨g', ?_, fun k => (hker k).trans (hfk (ι k))⟩
  have hnorm : g'.range.Normal := by
    constructor
    rintro _ ⟨k, rfl⟩ σ
    obtain ⟨y, hy⟩ := hfs (σ : Equiv.Perm (Fin 5))
    have hyK : (y : G) * k * (y : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (sup_le_normalizer hyp h618 y.2) k).mp k.2
    refine ⟨⟨_, hyK⟩, Subtype.ext ?_⟩
    have hι : ι ⟨_, hyK⟩ = y * ι k * y⁻¹ := Subtype.ext (by simp [ι])
    rw [hg'k, hι, map_mul, map_mul, map_inv, hy, coe_mul, coe_mul, coe_inv, hg'k]
  haveI := alternatingGroup.isSimpleGroup_five
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g'.range with h | h
  · exfalso
    obtain ⟨k₀, hk₀K, hk₀O⟩ := exists_not_mem_pCoreOf h618
    apply hk₀O
    have h1 : g' ⟨k₀, hk₀K⟩ = 1 := by
      have h2 : g' ⟨k₀, hk₀K⟩ ∈ g'.range := ⟨_, rfl⟩
      rw [h] at h2
      exact h2
    exact (hfk _).1 ((hker _).1 h1)
  · exact MonoidHom.range_eq_top.mp h

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H
