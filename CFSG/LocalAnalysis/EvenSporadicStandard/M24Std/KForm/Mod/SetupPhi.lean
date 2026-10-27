module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.PerfectSocle
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.TwoComponent

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Group K] (S : Subgroup K) [S.Normal] (z : K)
  (ψ : ↥(centralizer ({z} : Set K)) →* Z2S6)

@[expose] def fixedPhi : ↥(fixedSubgroup (MulAut.conjNormal (H := S) z)) →* Z2S6 :=
  ψ.comp ((S.subgroupOf (centralizer ({z} : Set K))).subtype.comp
    (CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z).symm.toMonoidHom)

theorem fixedPhi_apply (x : ↥(S.subgroupOf (centralizer ({z} : Set K)))) :
    fixedPhi S z ψ
      (CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z x) = ψ x := by
  simp [fixedPhi]

variable {S z ψ}

theorem odd_ker_fixedPhi (hodd : Odd (Nat.card ψ.ker)) :
    Odd (Nat.card (fixedPhi S z ψ).ker) := by
  let ι : ↥(fixedSubgroup (MulAut.conjNormal (H := S) z)) →*
      ↥(centralizer ({z} : Set K)) :=
    (S.subgroupOf (centralizer ({z} : Set K))).subtype.comp
      (CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z).symm.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.subtype_injective _).comp
      (CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z).symm.injective
  have hcomp : fixedPhi S z ψ = ψ.comp ι := rfl
  have hle : (fixedPhi S z ψ).ker.map ι ≤ ψ.ker := by
    rw [hcomp, ← MonoidHom.comap_ker ψ ι]
    exact Subgroup.map_comap_le ι ψ.ker
  have hcard : Nat.card ((fixedPhi S z ψ).ker.map ι) = Nat.card (fixedPhi S z ψ).ker :=
    Subgroup.card_map_of_injective (K := (fixedPhi S z ψ).ker) (f := ι) hι
  exact Odd.of_dvd_nat hodd (hcard ▸ Subgroup.card_dvd_of_le hle)

variable [Finite K]

theorem a6Factor_le_range_fixedPhi (hC : centralizer (S : Set K) = ⊥)
    (hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S))
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) :
    a6Factor ≤ (fixedPhi S z ψ).range := by
  let C : Subgroup K := centralizer ({z} : Set K)
  have hA : a6Factor ≤ ψ.range := by
    rw [MonoidHom.range_eq_top.2 hψ]
    exact le_top
  obtain ⟨J, -, hJperf, hJmap, -, -, -⟩ := exists_twoComponent ψ hodd hA
  let eF := CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z
  let J' : Subgroup K := J.map C.subtype
  have hJ'perf : ⁅J', J'⁆ = J' := by
    change ⁅J.map C.subtype, J.map C.subtype⁆ = J.map C.subtype
    rw [← Subgroup.map_commutator J J C.subtype, hJperf]
  have hJ'S : J' ≤ S := perfect_le_socle_of_perfect S hC hsolv J' hJ'perf
  intro g hg
  have hg' : g ∈ J.map ψ := by rw [hJmap]; exact hg
  obtain ⟨l, hlJ, hlψ⟩ := Subgroup.mem_map.mp hg'
  have hlS : (l : K) ∈ S := hJ'S ⟨l, hlJ, rfl⟩
  have hlC : l ∈ S.subgroupOf C := Subgroup.mem_subgroupOf.2 hlS
  refine ⟨eF ⟨l, hlC⟩, ?_⟩
  rw [fixedPhi_apply]
  exact hlψ

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
