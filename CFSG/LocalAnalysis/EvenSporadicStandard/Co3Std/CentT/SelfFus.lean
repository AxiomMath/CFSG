module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint

section Certified


theorem false_of_fus_self {X : Type} [Group X] [Finite X] (Y : Subgroup X) [Y.Normal]
    (hq : LieModel (X ⧸ Y) .PSp 3 2 1) {w : X} (hw : w * w = 1) (hwY : w ∉ Y)
    (hD : CentFacts ↥(centralizer ({w} : Set X)))
    (hP : ∀ P : Subgroup X, P ≤ Y → IsPGroup 2 P →
      ∃ M : Subgroup X, M ≤ P ∧ IsCyclic ↥M ∧ M.relIndex P ≤ 2) : False := by
  let D : Subgroup X := centralizer ({w} : Set X)
  let Q := X ⧸ Y
  let wbar : Q := (w : Q)
  haveI : Finite Q := Quotient.finite _
  have hw2bar : wbar * wbar = 1 := by
    change (w : Q) * (w : Q) = 1
    rw [← QuotientGroup.mk_mul, hw, QuotientGroup.mk_one]
  have hwbar1 : wbar ≠ 1 := by
    intro h
    exact hwY ((QuotientGroup.eq_one_iff (N := Y) w).mp h)
  have hDfact : CentFacts ↥D := hD
  obtain ⟨N, _hNn, hmap, ⟨S, hSN, hS2, hScyc⟩, _h711⟩ := hDfact.core
  let ψ : ↥N →* Q := (QuotientGroup.mk' Y).comp (D.subtype.comp N.subtype)
  have hψmem : ψ.range ≤ centralizer ({wbar} : Set Q) := by
    rintro _ ⟨n, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hnD : D.subtype (N.subtype n) ∈ D := (N.subtype n).2
    have hcomm : D.subtype (N.subtype n) * w = w * D.subtype (N.subtype n) :=
      Subgroup.mem_centralizer_singleton_iff.mp hnD
    change ((D.subtype (N.subtype n) : X) : Q) * (w : Q) =
      (w : Q) * ((D.subtype (N.subtype n) : X) : Q)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg (fun x : X => (x : Q)) hcomm
  have hcard_range : Nat.card ↥ψ.range ≤ 23040 :=
    (Subgroup.card_le_of_le hψmem).trans
      (sp62_involution_centralizer_card hq hw2bar hwbar1).2
  have hψ1 : ψ = 1 := by
    have h := hmap ↥ψ.range hcard_range ψ.rangeRestrict
    rw [← MonoidHom.subtype_comp_rangeRestrict ψ, h]
    ext n
    simp
  have hmkY : ∀ n : ↥N, ((n : ↥D) : X) ∈ Y := by
    intro n
    have h3 : (((n : ↥D) : X) : X ⧸ Y) = 1 := by
      change ψ n = 1
      rw [hψ1]
      rfl
    exact (QuotientGroup.eq_one_iff (N := Y) ((n : ↥D) : X)).mp h3
  let P : Subgroup X := S.map D.subtype
  have hPY : P ≤ Y := by
    intro x hx
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
    exact hmkY ⟨s, hSN hsS⟩
  have hP2 : IsPGroup 2 P := by
    show IsPGroup 2 (S.map D.subtype)
    exact IsPGroup.map hS2 D.subtype
  obtain ⟨M, hMP, hMcyc, hMrel⟩ := hP P hPY hP2
  have hMD : M ≤ D := hMP.trans (by
    show S.map D.subtype ≤ D
    exact Subgroup.map_subtype_le S)
  let M' : Subgroup ↥D := M.subgroupOf D
  have hM'S : M' ≤ S := by
    intro m hm
    have hmM : (m : X) ∈ M := hm
    have hmP : (m : X) ∈ S.map D.subtype := hMP hmM
    obtain ⟨s, hsS, hse⟩ := Subgroup.mem_map.mp hmP
    have hsm : s = m := D.subtype_injective hse
    rwa [hsm] at hsS
  have hM'cyc : IsCyclic ↥M' :=
    (Subgroup.subgroupOfEquivOfLe hMD).isCyclic.mpr hMcyc
  have hrel : M'.relIndex S = M.relIndex P :=
    Subgroup.relIndex_comap (f := D.subtype) (H := M) (K := S)
  have hgt := hScyc M' hM'S hM'cyc
  have hle : M'.relIndex S ≤ 2 := (le_of_eq hrel).trans hMrel
  omega

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
