module

public import CFSG.Milestones.ASVolI.I3
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentral

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG
open CFSG.ASVolI.ChIJK (IsComponentIn)

private theorem isSubnormal_subgroupOf_map_of_surjective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Surjective f) {L C : Subgroup G} (hLC : L ≤ C)
    (h : (L.subgroupOf C).IsSubnormal) :
    ((L.map f).subgroupOf (C.map f)).IsSubnormal := by
  let φ : C →* C.map f :=
    { toFun := fun c => ⟨f (c : G), Subgroup.mem_map_of_mem f c.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨c, hc, hcf⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcf⟩
  have hmap := h.map hφ
  have heq : (L.subgroupOf C).map φ = (L.map f).subgroupOf (C.map f) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact Subgroup.mem_map_of_mem f hc
    · intro hy
      obtain ⟨l, hl, hlf⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨l, hLC hl⟩, hl, Subtype.ext hlf⟩
  rw [heq] at hmap
  exact hmap

private theorem normal_map_centralizer_subgroupOf_centralizer {Y : Type*} [Group Y] (v : Y) :
    (((centralizer {v}).map (QuotientGroup.mk' (center Y))).subgroupOf
      (centralizer {(QuotientGroup.mk v : Y ⧸ center Y)})).Normal := by
  let π : Y →* Y ⧸ center Y := QuotientGroup.mk' (center Y)
  let D : Subgroup (Y ⧸ center Y) := centralizer {π v}
  let P : Subgroup Y := D.comap π
  change (((centralizer {v}).map π).subgroupOf D).Normal
  have hCP : centralizer {v} ≤ P := by
    intro c hc
    change π c ∈ D
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc])
  have hCPnormal : ((centralizer {v}).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCP, Subgroup.le_normalizer_iff]
    intro p hp c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpcomm : π p * π v = π v * π p := Subgroup.mem_centralizer_singleton_iff.mp hp
    have hπeq : π (p⁻¹ * v * p) = π v := by
      calc π (p⁻¹ * v * p)
          = (π p)⁻¹ * π v * π p := by rw [map_mul, map_mul, map_inv]
        _ = π v := by rw [mul_assoc, hpcomm.symm, ← mul_assoc, inv_mul_cancel, one_mul]
    set z : Y := p⁻¹ * v * p * v⁻¹ with hzdef
    have hz : z ∈ center Y := by
      have := (QuotientGroup.eq_iff_div_mem (N := center Y)).mp hπeq
      simpa only [div_eq_mul_inv, hzdef] using this
    have hzv : p⁻¹ * v * p = v * z := by
      rw [(Subgroup.mem_center_iff.mp hz) v, hzdef]
      group
    have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcz : c * z = z * c := (Subgroup.mem_center_iff.mp hz) c
    have hconj : c * (p⁻¹ * v * p) = (p⁻¹ * v * p) * c := by
      rw [hzv]
      calc c * (v * z) = (c * v) * z := by rw [mul_assoc]
        _ = (v * c) * z := by rw [hcv]
        _ = v * (c * z) := by rw [mul_assoc]
        _ = v * (z * c) := by rw [hcz]
        _ = (v * z) * c := by rw [← mul_assoc]
    calc (p * c * p⁻¹) * v
        = p * (c * (p⁻¹ * v * p)) * p⁻¹ := by group
      _ = p * ((p⁻¹ * v * p) * c) * p⁻¹ := by rw [hconj]
      _ = v * (p * c * p⁻¹) := by group
  let ψ : P →* D :=
    { toFun := fun p => ⟨π (p : Y), p.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective (center Y) (y : Y ⧸ center Y)
    refine ⟨⟨p, ?_⟩, ?_⟩
    · change π p ∈ D
      rw [hp]
      exact y.2
    · exact Subtype.ext hp
  have hmapnorm : (((centralizer {v}).subgroupOf P).map ψ).Normal := hCPnormal.map ψ hψ
  have heq : ((centralizer {v}).subgroupOf P).map ψ =
      ((centralizer {v}).map π).subgroupOf D := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact Subgroup.mem_map_of_mem π hc
    · intro hy
      obtain ⟨c, hc, hcπ⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨c, hCP hc⟩, hc, Subtype.ext hcπ⟩
  rw [heq] at hmapnorm
  exact hmapnorm

theorem isComponentIn_map_quotient_center {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) {v : Y} {L : Subgroup Y}
    (hL : IsComponentIn L (centralizer {v})) :
    IsComponentIn (L.map (QuotientGroup.mk' (center Y)))
        (centralizer {(QuotientGroup.mk v : Y ⧸ center Y)}) ∧
      Nonempty (↥L ⧸ center ↥L ≃* ↥(L.map (QuotientGroup.mk' (center Y))) ⧸
        center ↥(L.map (QuotientGroup.mk' (center Y)))) := by
  obtain ⟨hLC, hLq, hLsn⟩ := hL
  let π : Y →* Y ⧸ center Y := QuotientGroup.mk' (center Y)
  let C : Subgroup Y := centralizer {v}
  let D : Subgroup (Y ⧸ center Y) := centralizer {π v}
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective (center Y)
  have hLD : L.map π ≤ D := by
    rw [Subgroup.map_le_iff_le_comap]
    intro l hl
    change π l ∈ D
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)])
  let f : ↥L →* ↥(L.map π) :=
    { toFun := fun l => ⟨π (l : Y), Subgroup.mem_map_of_mem π l.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, hl, hlπ⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨l, hl⟩, Subtype.ext hlπ⟩
  have hker : f.ker ≤ center ↥L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (QuotientGroup.mk (x : Y) : Y ⧸ center Y) = 1 := by
      have := congrArg Subtype.val hx
      simpa [f, π] using this
    have hxZ : (x : Y) ∈ center Y := (QuotientGroup.eq_one_iff (x : Y)).mp hx1
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hxZ) (g : Y))
  have hLq' : IsQuasisimple ↥(L.map π) := isQuasisimple_of_central_ker hLq f hf hker
  have hcenter : Nonempty (↥L ⧸ center ↥L ≃* ↥(L.map π) ⧸ center ↥(L.map π)) :=
    nonempty_quotCenter_equiv_of_central_ker hLq f hf hker
  have hAB : L.map π ≤ C.map π := Subgroup.map_mono hLC
  have hCD : C.map π ≤ D := by
    rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    change π c ∈ D
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc])
  have hLB : ((L.map π).subgroupOf (C.map π)).IsSubnormal :=
    isSubnormal_subgroupOf_map_of_surjective π hπsurj hLC hLsn
  have hBD : ((C.map π).subgroupOf D).IsSubnormal :=
    (normal_map_centralizer_subgroupOf_centralizer v).isSubnormal
  have hLDsn : ((L.map π).subgroupOf D).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hAB hCD hLB hBD
  exact ⟨⟨hLD, hLq', hLDsn⟩, hcenter⟩

end CFSG.OddStandard.HigherRank.F3
