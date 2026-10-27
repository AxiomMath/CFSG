module

public import CFSG.CGT.Timmesfeld75.JLemmaTrans
public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Lift

variable {G : Type} [Group G] [Finite G] {R T L : Subgroup G}

theorem exists_mem_normalizer_conj_ne (hT : IsWC T) (hTR : T ≤ R) (hLT : L ≤ T)
    (htrans : ∀ x ∈ (T.subgroupOf R).map (jMap ↥R), x ≠ 1 →
      ∀ y ∈ (T.subgroupOf R).map (jMap ↥R), y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (((T.subgroupOf R).map (jMap ↥R) : Subgroup (jQuot ↥R)) :
          Set (jQuot ↥R)), g * x * g⁻¹ = y)
    (h1 : (L.subgroupOf R).map (jMap ↥R) ≠ ⊥)
    (h2 : (L.subgroupOf R).map (jMap ↥R) ≠ (T.subgroupOf R).map (jMap ↥R)) :
    ∃ n ∈ R, conjSubgroup n T = T ∧ conjSubgroup n L ≠ L := by
  have hLR : L ≤ R := hLT.trans hTR
  have hPV : (L.subgroupOf R).map (jMap ↥R) ≤ (T.subgroupOf R).map (jMap ↥R) :=
    Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.2 (hLT (Subgroup.mem_subgroupOf.1 hz))
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h1
  obtain ⟨y, hyV, hyP⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hPV h2)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hy1 : y ≠ 1 := fun h => hyP (h ▸ Subgroup.one_mem _)
  obtain ⟨k, hk, hkxy⟩ := htrans x (hPV hx) hx1' y hyV hy1
  obtain ⟨r, hr⟩ := jMap_surjective k
  have hn : (r : G) ∈ R := r.2
  have hkV := mem_normalizer_iff_conjSubgroup_eq.1 hk
  have hmapT : (conjSubgroup r (T.subgroupOf R)).map (jMap ↥R) =
      (T.subgroupOf R).map (jMap ↥R) := by
    rw [map_conjSubgroup, hr, hkV]
  have hTeq : conjSubgroup r (T.subgroupOf R) = conjSubgroup 1 (T.subgroupOf R) := by
    refine eq_of_map_jMap_le (isWC_subgroupOf hT R hTR) (le_of_eq ?_)
    rw [hmapT, conjSubgroup_one]
  refine ⟨(r : G), hn, ?_, fun hL => ?_⟩
  · rw [conjSubgroup_one, conjSubgroup_subgroupOf] at hTeq
    have := Subgroup.subgroupOf_inj.1 hTeq
    rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem hTR hn), inf_of_le_left hTR] at this
  · have hLeq : conjSubgroup r (L.subgroupOf R) = L.subgroupOf R := by
      rw [conjSubgroup_subgroupOf, hL]
    have hmapL : conjSubgroup k ((L.subgroupOf R).map (jMap ↥R)) =
        (L.subgroupOf R).map (jMap ↥R) := by
      have := congrArg (Subgroup.map (jMap ↥R)) hLeq
      rwa [map_conjSubgroup, hr] at this
    have hxk := conj_mem_conjSubgroup k hx
    rw [hmapL, hkxy] at hxk
    exact hyP hxk

end Lift

end CFSG.CGT.Timmesfeld75
