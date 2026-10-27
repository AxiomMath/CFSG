
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrSylow

@[expose] public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem outerTable_map_inj {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {ζ α t g₁ g₂ h₁ h₂ : X} (h : OuterTable ζ α t g₁ g₂ h₁ h₂) :
    OuterTable (f ζ) (f α) (f t) (f g₁) (f g₂) (f h₁) (f h₂) := by
  obtain ⟨hζζ, hαα, htt, hα1, ht1, hαt, hαtc, hζα, hζt, hh1, hh2, hP, hcs, hsq1, hsq2,
    hgg, hhh, hgh, hhg, hg1h1, hg2h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [← map_mul, hζζ, map_one]
  · simp only [← map_mul, hαα, map_one]
  · simp only [← map_mul, htt, map_one]
  · exact fun he => hα1 (hf (he.trans (map_one f).symm))
  · exact fun he => ht1 (hf (he.trans (map_one f).symm))
  · exact fun he => hαt (hf he)
  · simp only [← map_mul, hαtc]
  · have := congrArg f hζα
    simpa [map_mul, map_inv] using this
  · have := congrArg f hζt
    simpa [map_mul, map_inv] using this
  · rw [hh1]
    simp only [map_mul, map_inv]
  · rw [hh2]
    simp only [map_mul, map_inv]
  · have hEq : (Subgroup.closure ({f α, f t, f g₁, f g₂, f h₁, f h₂} : Set Y)) =
        (Subgroup.closure ({α, t, g₁, g₂, h₁, h₂} : Set X)).map f := by
      rw [MonoidHom.map_closure]
      simp [Set.image_insert_eq]
    rw [hEq]
    exact hP.map f
  · intro c hc
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ ({g₁, g₂, h₁, h₂} : Set X), f x = c := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨g₁, by simp, rfl⟩
      · exact ⟨g₂, by simp, rfl⟩
      · exact ⟨h₁, by simp, rfl⟩
      · exact ⟨h₂, by simp, rfl⟩
    obtain ⟨hxα, hxt⟩ := hcs x hx
    exact ⟨by rw [← map_mul, ← map_mul, hxα], by rw [← map_mul, ← map_mul, hxt]⟩
  · rcases hsq1 with h1 | h1
    · left
      simp only [← map_mul, h1, map_one]
    · right
      simp only [← map_mul, h1]
  · rcases hsq2 with h1 | h1
    · left
      simp only [← map_mul, h1, map_one]
    · right
      simp only [← map_mul, h1]
  · have := congrArg f hgg
    simpa [map_mul, map_inv] using this
  · have := congrArg f hhh
    simpa [map_mul, map_inv] using this
  · have := congrArg f hgh
    simpa [map_mul, map_inv] using this
  · have := congrArg f hhg
    simpa [map_mul, map_inv] using this
  · simp only [← map_mul, hg1h1]
  · simp only [← map_mul, hg2h2]

theorem outerTableWreath_of_noTabSig (hsig : TS8Wr.NoTabSig) : OuterTableWreath := by
  intro X _ _ N hN hnon hc ζ α t g₁ g₂ h₁ h₂ h
  haveI := hN
  obtain ⟨e0⟩ := hnon
  have hinj : Function.Injective (TS8Wr.Phi N e0) := TS8Wr.Phi_injective N e0 hc
  exact TS8Wr.no_table_Wfull hsig (outerTable_map_inj (TS8Wr.Phi N e0) hinj h)

end CFSG.EvenSporadicStandard.Fin76b
