module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X]

theorem gnImg_gnStab (T : Subgroup X) (N : Subgroup (X ⧸ gnC T)) :
    gnImg T (gnStab T N) = gnImg T T ⊓ N := by
  ext y
  simp only [gnImg, gnStab, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨hxT, hxN⟩, rfl⟩
    exact ⟨⟨x, hxT, rfl⟩, hxN⟩
  · rintro ⟨⟨x, hxT, rfl⟩, hyN⟩
    exact ⟨x, ⟨hxT, hyN⟩, rfl⟩

theorem pCoreOf_le_gnStab [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    (N : Subgroup (X ⧸ gnC T)) :
    pCoreOf 2 (⊤ : Subgroup X) ≤ gnStab T N := by
  intro x hx
  rw [mem_gnStab]
  refine ⟨CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow hx, ?_⟩
  have h1 : QuotientGroup.mk' (gnC T) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr (CFSG.AGLEmbeddingD2.GN.pCoreOf_le_gnC hX hx)
  rw [h1]
  exact N.one_mem

end CFSG.AGLEmbeddingD2.Tits.GN516

end
