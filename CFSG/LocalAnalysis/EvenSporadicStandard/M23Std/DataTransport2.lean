module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KDichotomy

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G X : Type} [Group G] [Group X]

theorem FixedData.map {φ : X →* G} (hφ : Function.Injective φ) {F : Subgroup X}
    (D : FixedData (⊤ : Subgroup X) F) : FixedData φ.range (F.map φ) := by
  refine ⟨?_⟩
  rintro _ ⟨f₀, hf₀, rfl⟩ hf1 _ ⟨x₀, hx₀, rfl⟩ H
  have hf₀1 : f₀ ≠ 1 := fun h => hf1 (by rw [h, map_one])
  have key := D.fixed f₀ hf₀ hf₀1 x₀ hx₀ (fun b hb hbF hbf => by
    have h1 := H (φ b) ⟨b, rfl⟩ (mem_map_iff_conj hφ hbF) (by
      rw [← map_mul, ← map_inv, ← map_mul, hbf])
    rcases h1 with h2 | h2
    · left
      apply hφ
      rw [map_mul, map_mul, map_inv]
      exact h2
    · right
      apply hφ
      rw [map_mul, map_mul, map_inv, map_mul]
      exact h2)
  rcases key with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

theorem Trans2Data.map {φ : X →* G} (hφ : Function.Injective φ) {F : Subgroup X}
    (D : Trans2Data (⊤ : Subgroup X) F) : Trans2Data φ.range (F.map φ) := by
  refine ⟨?_⟩
  rintro _ ⟨f₀, hf₀, rfl⟩ hf1 _ ⟨f₀', hf₀', rfl⟩ hf'1 hff _ ⟨g₀, hg₀, rfl⟩ hg1 _ ⟨g₀', hg₀', rfl⟩
    hg'1 hgg
  obtain ⟨b, -, hbF, hbf, hbf'⟩ := D.trans2 f₀ hf₀ (fun h => hf1 (by rw [h, map_one])) f₀' hf₀'
    (fun h => hf'1 (by rw [h, map_one])) (fun h => hff (by rw [h])) g₀ hg₀
    (fun h => hg1 (by rw [h, map_one])) g₀' hg₀' (fun h => hg'1 (by rw [h, map_one]))
    (fun h => hgg (by rw [h]))
  refine ⟨φ b, ⟨b, rfl⟩, mem_map_iff_conj hφ hbF, ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul, hbf]
  · rw [← map_inv, ← map_mul, ← map_mul, hbf']

end CFSG.EvenSporadicStandard.M23Std
