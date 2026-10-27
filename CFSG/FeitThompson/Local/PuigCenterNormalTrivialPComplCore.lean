module

import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Local.PuigCenterSylowInPrimeCore
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
public import CFSG.FeitThompson.Local.SylowPuigCentralizerExtension
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.SylowInterNormalSylowOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem map_mk'_inf_sylow_eq_pCore [Finite G] (hp : p.Prime) (S : Sylow p G) :
    (puigCentralizerContainer p G ⊓ (S : Subgroup G)).map
        (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)))
      = pCore p (G ⧸ centralizer (puigCenterPCore p G : Set G)) := by
  have := Fact.mk hp
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G))) :=
    QuotientGroup.mk'_surjective _
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact mem_puigCentralizerContainer_iff.1 (mem_inf.1 hx).1
  · intro q hq
    have hqS : q ∈ (S : Subgroup G).map
        (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G))) := by
      have h := pCore_le_sylow hp (Sylow.mapSurjective hsurj S) hq
      rwa [Sylow.coe_mapSurjective] at h
    obtain ⟨s, hs, rfl⟩ := hqS
    exact mem_map_of_mem _ (mem_inf.2 ⟨mem_puigCentralizerContainer_iff.2 hq, hs⟩)

theorem centralizer_sup_inf_sylow [Finite G] (hp : p.Prime) (S : Sylow p G) :
    centralizer (puigCenterPCore p G : Set G)
        ⊔ (puigCentralizerContainer p G ⊓ (S : Subgroup G))
      = puigCentralizerContainer p G := by
  have hker : (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G))).ker
      = centralizer (puigCenterPCore p G : Set G) := QuotientGroup.ker_mk' _
  calc centralizer (puigCenterPCore p G : Set G)
        ⊔ (puigCentralizerContainer p G ⊓ (S : Subgroup G))
      = comap (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)))
          ((centralizer (puigCenterPCore p G : Set G)
            ⊔ (puigCentralizerContainer p G ⊓ (S : Subgroup G))).map
            (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)))) :=
        (comap_map_eq_self (by rw [hker]; exact le_sup_left)).symm
    _ = comap (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)))
          (pCore p (G ⧸ centralizer (puigCenterPCore p G : Set G))) := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
          map_mk'_inf_sylow_eq_pCore hp S]
    _ = puigCentralizerContainer p G := (puigCentralizerContainer_eq p G).symm

theorem map_puigCenter_inf_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) :
    (puigCenter ↥(puigCentralizerContainer p G ⊓ (S : Subgroup G))).map
        (puigCentralizerContainer p G ⊓ (S : Subgroup G)).subtype
      = (puigCenter (S : Subgroup G)).map (S : Subgroup G).subtype := by
  rw [map_puigCenter_subtype, map_puigCenter_subtype, map_puigSubgroup_inf_sylow hp hGodd S]

theorem normal_map_puigCenter_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime) (hpodd : Odd p)
    (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) (S : Sylow p G) :
    ((puigCenter (S : Subgroup G)).map (S : Subgroup G).subtype).Normal := by
  have := Fact.mk hp
  set Y : Subgroup G := puigCenterPCore p G with hY
  set C : Subgroup G := puigCentralizerContainer p G with hC
  set R : Subgroup G := C ⊓ (S : Subgroup G) with hR
  set K : Subgroup G := (puigCenter (S : Subgroup G)).map (S : Subgroup G).subtype with hK
  have hfrat : normalizer (R : Set G) ⊔ C = ⊤ :=
    normalizer_sup_eq_top_of_normal (p := p) inf_le_left (natCard_inf_sylow C S)
  have hCsup : centralizer (Y : Set G) ⊔ R = C := centralizer_sup_inf_sylow hp S
  have hRK : normalizer (R : Set G) ≤ normalizer (K : Set G) := by
    have h := normalizer_le_normalizer_map_subtype R (puigCenter R)
    rwa [map_puigCenter_inf_sylow hp hGodd S] at h
  have hKY : K ≤ Y := by
    rw [hY, puigCenterPCore_eq]
    exact map_puigCenter_sylow_le_map_puigCenter_pCore hp hpodd hGodd hp' S
  have hNK : centralizer (Y : Set G) ≤ normalizer (K : Set G) :=
    (centralizer_le (by exact_mod_cast hKY)).trans (centralizer_le_normalizer _)
  rw [← normalizer_eq_top_iff]
  refine top_le_iff.1 ?_
  rw [← hfrat]
  exact sup_le hRK (hCsup.ge.trans (sup_le hNK (le_normalizer.trans hRK)))

theorem conj_mem_map_puigCenter_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime) (hpodd : Odd p)
    (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) (S : Sylow p G) {x : G}
    (hx : x ∈ (puigCenter (S : Subgroup G)).map (S : Subgroup G).subtype) (g : G) :
    g * x * g⁻¹ ∈ (puigCenter (S : Subgroup G)).map (S : Subgroup G).subtype :=
  (normal_map_puigCenter_sylow hp hpodd hGodd hp' S).conj_mem x hx g

end CFSG.FeitThompson

end
