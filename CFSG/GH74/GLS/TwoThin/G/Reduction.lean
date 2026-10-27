module

public import CFSG.GH74.GLS.TwoThin.Main

public section

namespace CFSG.GH74.GLS

open Blueprint Assembly.LowTwoRank

@[expose] def S_twoThinOfB2G : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → IsKProperSimple G → 3 ≤ pRank 2 G →
    ¬ L2Meets G InG2 → L2Meets G InB2 → HasTwoThinConfiguration G

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank

theorem gen4_barQ {G : Type} [Group G] [Finite G] (hG : Gen4 G) (x : G) :
    Gen4 (barQ ↥(centralizer ({x} : Set G))) :=
  Gen4.quotient (pPrimeCore 2 ↥(centralizer ({x} : Set G))) (Gen4.subgroup _ hG)

theorem barMk_centralizer_mem_center {G : Type} [Group G] [Finite G] {x : G}
    (hxx : x ∈ centralizer ({x} : Set G)) :
    barMk ↥(centralizer ({x} : Set G)) ⟨x, hxx⟩ ∈
      center (barQ ↥(centralizer ({x} : Set G))) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := barMk_surjective (Y := ↥(centralizer ({x} : Set G))) y
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact ((Subgroup.mem_centralizer_iff.mp y'.2) x (Set.mem_singleton x)).symm

theorem gen4Cen_barQ {G : Type} [Group G] [Finite G] (hG : Gen4 G) {x : G}
    (hx : orderOf x = 2) : Gen4Cen (barQ ↥(centralizer ({x} : Set G))) := by
  have hxx : x ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
  refine ⟨gen4_barQ hG x, barMk ↥(centralizer ({x} : Set G)) ⟨x, hxx⟩,
    barMk_centralizer_mem_center hxx, orderOf_barMk (orderOf_mk_centralizer hxx hx)⟩

abbrev TwoThinC2VerticalGC : Prop := TwoThinC2VerticalP Gen4Comp

abbrev TwoThinKGroupCoreGC : Prop := TwoThinKGroupCoreP Gen4Comp

theorem TwoThinC2CoverP.mono {P P' : GroupPred} (hPP : ∀ (L : Type) [Group L], P L → P' L)
    (h : TwoThinC2CoverP P') : TwoThinC2CoverP P := by
  intro L L₁ K₀ _ _ _ _ δ φ hP hq hC hδs hδk hφs hφo hK₀
  exact h L L₁ K₀ δ φ (hPP L hP) hq hC hδs hδk hφs hφo hK₀

theorem s_twoThinOfB2G_of_coreGC (h : TwoThinKGroupCoreGC) : S_twoThinOfB2G :=
  s_twoThinOfB2P_of_core (PG := Gen4) (Q := Gen4Cen) (P := Gen4Comp)
    (fun _ _ _ hG _ hx => gen4Cen_barQ hG hx)
    (fun _ _ _ hH L => gen4Comp_of_gen4Cen hH L) h

end CFSG.GH74.GLS.TwoThin
