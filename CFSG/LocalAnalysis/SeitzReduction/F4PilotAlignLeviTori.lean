module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignTori

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotAlignLeviToriNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Split

variable {K : Type} [Field K]

variable (K) in
theorem leviTorusOf_top (J : Finset (Fin (Tag.rank .F4))) : leviTorusOf K ⊤ J = leviTorus K J := by
  ext g
  rw [mem_leviTorusOf, mem_leviTorus]
  constructor
  · rintro ⟨b, ⟨hb, -⟩, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, ⟨hb, fun _ => mem_top _⟩, rfl⟩

theorem three_le_natCard_top_units [Finite K] (hq : 4 ≤ Nat.card K) :
    3 ≤ Nat.card (⊤ : Subgroup Kˣ) := by
  rw [Subgroup.card_top, Nat.card_units]
  omega


theorem perfectCore_inf_centralizer_leviTorus [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    perfectCore (adjointGroup .F4 K ⊓ centralizer (leviTorus K J : Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) := by
  rw [← leviTorusOf_top]
  exact perfectCore_inf_centralizer_leviTorusOf ⊤ (three_le_natCard_top_units hq) hJ

theorem perfectCore_levi_inf_centralizer_leviTorus [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) (N : AmalgamNeighbour)
    (hJN : J ⊆ N.nodes) :
    perfectCore ((N.levi K).map (adjointGroup .F4 K).subtype ⊓
        centralizer (leviTorus K J : Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) := by
  rw [← leviTorusOf_top]
  exact perfectCore_levi_inf_centralizer_leviTorusOf ⊤ (three_le_natCard_top_units hq) hJ N hJN

end Split

section Subfield

variable {k K : Type} [Field k] [Field K]

theorem baseChangeGL_rootDiagUnit_eq_map
    (f : k →+* K) {τ : Tag}
    (a : Fin τ.rank → kˣ) :
    baseChangeGL f (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map f.toMonoidHom (a i) := by
  refine Units.ext (end_ext_single fun b => ?_)
  rw [baseChangeGL_apply_single]
  change Finsupp.mapRange f f.map_zero (rootDiag a (Finsupp.single b 1)) =
    rootDiag (fun i => Units.map f.toMonoidHom (a i)) (Finsupp.single b 1)
  rcases b with i | α
  · rw [rootDiag_single_inl, rootDiag_single_inl, Finsupp.mapRange_single, map_one]
  · rw [rootDiag_single_inr, rootDiag_single_inr, Finsupp.smul_single_one,
      Finsupp.smul_single_one, Finsupp.mapRange_single]
    congr 1
    simp [map_prod, map_zpow₀]

theorem natCard_range_unitsMap (f : k →+* K) :
    Nat.card (Units.map f.toMonoidHom).range = Nat.card kˣ :=
  (Nat.card_congr (MonoidHom.ofInjective (Units.map_injective (f := f.toMonoidHom)
    f.injective)).toEquiv).symm

theorem three_le_natCard_range_unitsMap [Finite k] (f : k →+* K) (hq : 4 ≤ Nat.card k) :
    3 ≤ Nat.card (Units.map f.toMonoidHom).range := by
  rw [natCard_range_unitsMap, Nat.card_units]
  omega

theorem map_baseChangeGL_leviTorus
    (f : k →+* K) (J : Finset (Fin (Tag.rank .F4))) :
    (leviTorus k J).map (baseChangeGL f) =
      leviTorusOf K (Units.map f.toMonoidHom).range J := by
  ext g
  rw [mem_map, mem_leviTorusOf]
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hx
    refine ⟨fun i => Units.map f.toMonoidHom (b i), ⟨fun j hj => ?_, fun i => ⟨b i, rfl⟩⟩,
      (baseChangeGL_rootDiagUnit_eq_map f b).symm⟩
    change Units.map f.toMonoidHom (b j) = 1
    rw [hb j hj, map_one]
  · rintro ⟨b', ⟨hb1, hbA⟩, rfl⟩
    choose b hb using hbA
    refine ⟨rootDiagUnit .F4 b, mem_leviTorus.2 ⟨b, fun j hj => ?_, rfl⟩, ?_⟩
    · apply Units.map_injective (f := f.toMonoidHom) f.injective
      rw [hb j, hb1 j hj, map_one]
    · rw [baseChangeGL_rootDiagUnit_eq_map]
      exact congrArg _ (funext hb)


theorem perfectCore_inf_centralizer_map_leviTorus [Finite k] (f : k →+* K)
    (hq : 4 ≤ Nat.card k) {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    perfectCore (adjointGroup .F4 K ⊓
        centralizer (((leviTorus k J).map (baseChangeGL f) : Subgroup (ModGL .F4 K)) :
          Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) := by
  rw [map_baseChangeGL_leviTorus]
  exact perfectCore_inf_centralizer_leviTorusOf _ (three_le_natCard_range_unitsMap f hq) hJ

theorem perfectCore_levi_inf_centralizer_map_leviTorus [Finite k] (f : k →+* K)
    (hq : 4 ≤ Nat.card k) {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (N : AmalgamNeighbour) (hJN : J ⊆ N.nodes) :
    perfectCore ((N.levi K).map (adjointGroup .F4 K).subtype ⊓
        centralizer (((leviTorus k J).map (baseChangeGL f) : Subgroup (ModGL .F4 K)) :
          Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) := by
  rw [map_baseChangeGL_leviTorus]
  exact perfectCore_levi_inf_centralizer_leviTorusOf _ (three_le_natCard_range_unitsMap f hq)
    hJ N hJN

end Subfield

end CFSG.SeitzReduction.F4Pilot
