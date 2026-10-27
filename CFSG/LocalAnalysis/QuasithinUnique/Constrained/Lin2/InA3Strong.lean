module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Ord2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

namespace Lin2Hyp

section Strong

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

omit E in
theorem R_inf_le_T_inf {s : G} :
    thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤ T ⊓ Subgroup.centralizer ({s} : Set G) :=
  inf_le_inf_right _ ((thompsonJ_le_self S).trans hcfg.S_le_T)

theorem R_s_eq_strongClosure {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hxT : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S) :
    thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) =
      strongClosure (pCoreOf 2 H) (T ⊓ Subgroup.centralizer ({s} : Set G)) := by
  set C := Subgroup.centralizer ({s} : Set G) with hC
  have hUQ := E.UQ hcfg
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxT.2
  have hRU := (E.RUU hcfg hxT.1 hxS).1
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  apply le_antisymm
  ·
    obtain ⟨-, hset, -⟩ := E.U_s_card hcfg hs hsR hs2 hxT.1 hxS
    intro r hr
    have hr' : r ∈ ((blockU L ⊓ C : Subgroup G) : Set G) * ((conjR (blockU L) x ⊓ C : Subgroup G) :
        Set G) := by rw [hset]; exact hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr'
    refine (strongClosure (pCoreOf 2 H) (T ⊓ C)).mul_mem (Subgroup.subset_closure ?_)
      (Subgroup.subset_closure ?_)
    · exact ⟨⟨hRT (hUR hu.1), hu.2⟩, u, hUQ ▸ hu.1, 1, by simp⟩
    · have hvx : x * v * x⁻¹ ∈ blockU L := mem_conjR.mp hv.1
      refine ⟨⟨hRT (hVR hv.1), hv.2⟩, x * v * x⁻¹, hUQ ▸ hvx, x, ?_⟩
      group
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyT, a, ha, g, rfl⟩
    have hyR : g⁻¹ * a * g ∈ thompsonJ S := by
      rw [E.Rstrong hcfg]
      exact Subgroup.subset_closure ⟨hyT.1, a, ha, g, rfl⟩
    exact ⟨hyR, hyT.2⟩

end Strong

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
