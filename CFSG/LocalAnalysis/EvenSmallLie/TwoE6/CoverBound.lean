module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2Diag
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.RankThree.CentralLiftU.PerfectSplit
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift

public section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.LieType.Steinberg.Exceptional

theorem map_subtype_commutator {G : Type*} [Group G] (P : Subgroup G) :
    (commutator P).map P.subtype = ⁅P, P⁆ := by
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, P.range_subtype]

theorem card_ker_le_four
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (η : E →* twistedE6Group 2 1)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 4 := by
  set L := (twistedE6Datum 2 1).levi levi34 with hL
  set P := L.comap η with hP
  let ηP : P →* L := (η.comp P.subtype).codRestrict L fun x => x.2
  have hηP : Function.Surjective ηP := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hη y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hmemP : ∀ c ∈ η.ker, c ∈ P := fun c hc => by
    rw [hP, mem_comap, MonoidHom.mem_ker.1 hc]
    exact L.one_mem
  have hkerP : ∀ x : P, ηP x = 1 ↔ (x : E) ∈ η.ker := fun x => by
    rw [MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let ρ : P →* Matrix.SpecialLinearGroup (Fin 3) CFSG.LieType.Chevalley.C2E6Overlap.K :=
    levi34Equiv.toMonoidHom.comp ηP
  have hρ : Function.Surjective ρ := levi34Equiv.surjective.comp hηP
  have hρker : ∀ x : P, ρ x = 1 ↔ (x : E) ∈ η.ker := fun x => by
    rw [← hkerP x]
    exact MulEquiv.map_eq_one_iff levi34Equiv
  have hρc : ρ.ker ≤ center P := fun x hx => by
    have hx' := (hρker x).1 hx
    exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 (hC hx') y)
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) CFSG.LieType.Chevalley.C2E6Overlap.K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  obtain ⟨hperf, hsurj, hkc⟩ := CFSG.RankThree.CentralLiftU.derived_restrict_facts ρ hρ hρc
  set D := commutator P
  have : Group.IsPerfect D := hperf
  set ρD := ρ.comp D.subtype
  have hK4 : Nat.card CFSG.LieType.Chevalley.C2E6Overlap.K = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact CFSG.LieType.Chevalley.C2E6Overlap.card_K
  have hsq : ∀ c ∈ ρD.ker, c ^ 2 = 1 := fun c hc => by
    have hc' : ((c : P) : E) ∈ η.ker := (hρker c).1 hc
    have h1 : ((c : P) : E) ^ 2 = 1 := sq_eq_one_of_mem_ker η hη hC h2 hc'
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  have hle := CFSG.LieType.Multipliers.L34Upper.card_ker_le_four hK4 ρD hsurj hkc hsq
  have hmemD : ∀ c ∈ η.ker, ∃ d : D, ((d : P) : E) = c := fun c hc => by
    have hc' := ker_le_commutator_comap_levi34 η hη hC h2 hc
    rw [← map_subtype_commutator] at hc'
    obtain ⟨p, hp, rfl⟩ := hc'
    exact ⟨⟨p, hp⟩, rfl⟩
  let f : ρD.ker → η.ker := fun d => ⟨((d : D) : P), (hρker _).1 d.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun d d' h => ?_, fun c => ?_⟩
    · have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    · obtain ⟨d, hd⟩ := hmemD c c.2
      refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hρker, hd]
      exact c.2
  rw [← Nat.card_eq_of_bijective f hf]
  exact hle

end CFSG.EvenSmallLie.TwoE6
