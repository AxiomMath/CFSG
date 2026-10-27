module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.HarrisLit

variable {G : Type} [Group G]

private theorem isPComponent_two_of_isComponent {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) : IsPComponent 2 L := by
  refine CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hL ?_
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hL
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) hle

theorem centralizer_pair_subgroupOf (y : G) (s : ↥(centralizer ({y} : Set G))) :
    (centralizer ({(s : G), y} : Set G)).subgroupOf (centralizer ({y} : Set G)) =
      centralizer ({s} : Set ↥(centralizer ({y} : Set G))) := by
  ext ⟨g, hg⟩
  have hyg : y * g = g * y := mem_centralizer_iff.mp hg y (Set.mem_singleton y)
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subtype.ext (h (s : G) (Set.mem_insert _ _))
  · intro h x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact congrArg Subtype.val (h s (Set.mem_singleton s))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hyg

theorem centralizer_pair_le (u y : G) :
    centralizer ({u, y} : Set G) ≤ centralizer ({y} : Set G) :=
  Subgroup.centralizer_le (by simp)

theorem isTwoComponentIn_subgroupOf_of_isComponentIn [Finite G] (y : G)
    (s : ↥(centralizer ({y} : Set G))) {J : Subgroup G}
    (hJ : IsComponentIn J (centralizer ({(s : G), y} : Set G))) :
    IsTwoComponentIn (J.subgroupOf (centralizer ({y} : Set G)))
      (centralizer ({s} : Set ↥(centralizer ({y} : Set G)))) := by
  have hle : centralizer ({(s : G), y} : Set G) ≤ centralizer ({y} : Set G) :=
    centralizer_pair_le _ _
  have hJle : J.subgroupOf (centralizer ({y} : Set G)) ≤
      centralizer ({s} : Set ↥(centralizer ({y} : Set G))) := by
    rw [← centralizer_pair_subgroupOf y s]
    exact fun g hg => hJ.1 hg
  rw [isTwoComponentIn_iff hJle, ← centralizer_pair_subgroupOf y s,
    ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2
      Nat.prime_two]
  exact isPComponent_two_of_isComponent hJ.2

theorem isComponentIn_map_subtype_of_isTwoComponent [Finite G] (hA1 : AschA1 G) {y : G}
    (hy : orderOf y = 2) {K' : Subgroup ↥(centralizer ({y} : Set G))} (hK' : IsTwoComponent K') :
    IsComponentIn (K'.map (centralizer ({y} : Set G)).subtype) (centralizer ({y} : Set G)) := by
  have h1 : IsComponent K' := hA1 y hy K' ((isTwoComponent_iff_isPComponent K').1 hK')
  refine ⟨Subgroup.map_subtype_le K', ?_⟩
  have h2 : (K'.map (centralizer ({y} : Set G)).subtype).subgroupOf (centralizer ({y} : Set G)) =
      K' := Subgroup.comap_map_eq_self_of_injective (centralizer _).subtype_injective K'
  rw [h2]
  exact h1

theorem map_subtype_conj_eq_conjugate {y u : G} (hu : orderOf u = 2)
    (s : ↥(centralizer ({y} : Set G))) (hs : (s : G) = u)
    (K : Subgroup ↥(centralizer ({y} : Set G))) :
    (K.map (MulAut.conj s).toMonoidHom).map (centralizer ({y} : Set G)).subtype =
      CFSG.conjugate (K.map (centralizer ({y} : Set G)).subtype) u := by
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu, pow_two] at h
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  unfold CFSG.conjugate
  rw [hinv, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, hs]

end CFSG.OddStandard.SmallF3.Omega
