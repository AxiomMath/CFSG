module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84h_cover_le_closure {G H : Type} [Group G] [Group H] {L : Subgroup G}
    {φ : ↥L →* H} (hφ : OddCentralCover φ) {S₀ : Subgroup G} (hSL : S₀ ≤ L)
    (hS2 : IsPGroup 2 S₀) (hω : omega1 (ffImg φ S₀) = ffImg φ S₀) {C : Set G} (hCS : C ⊆ S₀)
    (hC : ∀ u ∈ S₀, u * u = 1 → u ≠ 1 → u ∈ C) : S₀ ≤ Subgroup.closure C := by
  let H₀ : Subgroup G := Subgroup.closure C
  have hHS : H₀ ≤ S₀ := (Subgroup.closure_le S₀).mpr hCS
  have hPf : ffImg φ S₀ ≤ ffImg φ H₀ := by
    calc ffImg φ S₀ = omega1 (ffImg φ S₀) := hω.symm
      _ ≤ ffImg φ H₀ := by
        rw [omega1]
        refine (Subgroup.closure_le (ffImg φ H₀)).mpr ?_
        intro x hx
        obtain ⟨hxS, hx2⟩ := hx
        obtain ⟨l, hlS, hlx⟩ := mem_ffImg_iff.mp hxS
        have hllS : ((l * l : ↥L) : G) ∈ S₀ := by
          simpa using S₀.mul_mem hlS hlS
        have h1S : ((1 : ↥L) : G) ∈ S₀ := by simpa using S₀.one_mem
        have hφll : φ (l * l) = φ 1 := by
          rw [map_mul, map_one, hlx, ← pow_two, hx2]
        have hll : l * l = 1 :=
          ff_cover_eq_of_pGroup (B := S₀) (l := l * l) (l' := 1) hφ hS2 hllS h1S hφll
        have hllG : (l : G) * (l : G) = 1 := by
          simpa using congrArg (fun y : ↥L => (y : G)) hll
        by_cases h1 : (l : G) = 1
        · have hl1 : l = 1 := Subtype.ext (by simpa using h1)
          rw [← hlx, hl1, map_one]
          exact (ffImg φ H₀).one_mem
        · have hmemC : (l : G) ∈ C := hC (l : G) hlS hllG h1
          have hmemH : (l : G) ∈ H₀ := Subgroup.subset_closure hmemC
          rw [← hlx]
          exact mem_ffImg_iff.mpr ⟨l, hmemH, rfl⟩
  intro u hu
  have huS : φ ⟨u, hSL hu⟩ ∈ ffImg φ S₀ :=
    mem_ffImg_iff.mpr ⟨⟨u, hSL hu⟩, hu, rfl⟩
  obtain ⟨l', hl'H, hl'φ⟩ := mem_ffImg_iff.mp (hPf huS)
  have heq : l' = ⟨u, hSL hu⟩ :=
    ff_cover_eq_of_pGroup (B := S₀) (l := l') (l' := ⟨u, hSL hu⟩)
      hφ hS2 (hHS hl'H) hu hl'φ
  have hval : (l' : G) = u := congrArg (fun y : ↥L => (y : G)) heq
  rw [← hval]
  exact hl'H

end CFSG.OddStandard.SmallF3.Omega
