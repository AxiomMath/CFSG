module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY12

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AS81 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {z : G} {R : Subgroup G}

private theorem fz_map_subgroupOf_closure_le (hRC : R ≤ centralizer ({z} : Set G)) :
    (((fzCClosure z R).subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (zpowers (zC z))))
      ≤ normalClosure ((fzBar z R : Subgroup (FzCbar z)) : Set (FzCbar z)) := by
  have hK_le : fzCClosure z R ≤
      ((normalClosure ((fzBar z R : Subgroup (FzCbar z)) : Set (FzCbar z))).comap
        (QuotientGroup.mk' (zpowers (zC z)))).map (centralizer ({z} : Set G)).subtype := by
    rw [fzCClosure, closure_le]
    rintro y ⟨g, hg, a, ha, rfl⟩
    have haC : a ∈ centralizer ({z} : Set G) := hRC ha
    have hyC : g * a * g⁻¹ ∈ centralizer ({z} : Set G) :=
      (centralizer ({z} : Set G)).mul_mem
        ((centralizer ({z} : Set G)).mul_mem hg haC)
        ((centralizer ({z} : Set G)).inv_mem hg)
    refine ⟨⟨g * a * g⁻¹, hyC⟩, ?_, rfl⟩
    refine Subgroup.mem_comap.mpr ?_
    have hmem : QuotientGroup.mk' (zpowers (zC z)) ⟨a, haC⟩ ∈
        (fzBar z R : Subgroup (FzCbar z)) := by
      rw [fzBar]
      exact ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hmemM : QuotientGroup.mk' (zpowers (zC z)) ⟨a, haC⟩ ∈
        normalClosure ((fzBar z R : Subgroup (FzCbar z)) : Set (FzCbar z)) :=
      Subgroup.subset_normalClosure hmem
    have hconj : QuotientGroup.mk' (zpowers (zC z)) ⟨g * a * g⁻¹, hyC⟩ =
        QuotientGroup.mk' (zpowers (zC z)) ⟨g, hg⟩ *
          QuotientGroup.mk' (zpowers (zC z)) ⟨a, haC⟩ *
          (QuotientGroup.mk' (zpowers (zC z)) ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [hconj]
    exact (inferInstance : (normalClosure
      ((fzBar z R : Subgroup (FzCbar z)) : Set (FzCbar z))).Normal).conj_mem _ hmemM _
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  have hxK : (x : G) ∈ fzCClosure z R := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨w, hw, hwx⟩ := hK_le hxK
  refine Subgroup.mem_comap.mpr ?_
  have hwx' : w = x := Subtype.ext hwx
  rw [← hwx']
  exact Subgroup.mem_comap.mp hw

theorem fz_relIndex_of_bar_sylow (hzR : z ∈ R) (hRC : R ≤ centralizer ({z} : Set G))
    (h : IsSylowOf 2 (fzBar z R) (normalClosure ((fzBar z R : Subgroup (FzCbar z)) :
      Set (FzCbar z)))) : ¬ 2 ∣ R.relIndex (fzCClosure z R) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  set π : ↥C →* FzCbar z := QuotientGroup.mk' (zpowers (zC z)) with hπ
  set K : Subgroup G := fzCClosure z R with hK
  set Mbar : Subgroup (FzCbar z) :=
    normalClosure ((fzBar z R : Subgroup (FzCbar z)) : Set (FzCbar z)) with hM
  have hnot : ¬ 2 ∣ (fzBar z R).relIndex Mbar := by
    rw [hM]
    exact (isSylowOf_iff.mp h).2.2
  have hker_le : π.ker ≤ R.subgroupOf C := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    rw [hπ, QuotientGroup.ker_mk'] at hy
    exact zpowers_le.mpr hzR (mem_zpowers_zC.mp hy)
  have hRK : R ≤ K := by
    rw [hK]
    exact le_fzCClosure z R
  have hKC : K ≤ C := by
    rw [hK, hC]
    exact fzCClosure_le_centralizer hRC
  have hsupR : (R.subgroupOf C) ⊔ π.ker = R.subgroupOf C := sup_eq_left.mpr hker_le
  have hsupK : (K.subgroupOf C) ⊔ π.ker = K.subgroupOf C :=
    sup_eq_left.mpr (hker_le.trans (Subgroup.subgroupOf_mono C hRK))
  have hmap : ((R.subgroupOf C).map π).relIndex ((K.subgroupOf C).map π) =
      (R.subgroupOf C).relIndex (K.subgroupOf C) := by
    rw [Subgroup.relIndex_map_map π (R.subgroupOf C) (K.subgroupOf C), hsupR, hsupK]
  have hsub : (R.subgroupOf C).relIndex (K.subgroupOf C) = R.relIndex K :=
    Subgroup.relIndex_subgroupOf (H := R) (K := K) (L := C) hKC
  have hRmap : (R.subgroupOf C).map π = fzBar z R := by
    change (R.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (zpowers (zC z))) = fzBar z R
    rfl
  have hRK_eq : R.relIndex K = (fzBar z R).relIndex ((K.subgroupOf C).map π) := by
    rw [← hsub, ← hmap, hRmap]
  have hKL : (K.subgroupOf C).map π ≤ Mbar := by
    change (((fzCClosure z R).subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (zpowers (zC z))))
      ≤ normalClosure ((fzBar z R : Subgroup (FzCbar z)) : Set (FzCbar z))
    exact fz_map_subgroupOf_closure_le hRC
  have hHK : fzBar z R ≤ (K.subgroupOf C).map π := by
    rw [← hRmap]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono C hRK)
  have hrel : (fzBar z R).relIndex Mbar =
      (fzBar z R).relIndex ((K.subgroupOf C).map π) *
        ((K.subgroupOf C).map π).relIndex Mbar :=
    (Subgroup.relIndex_mul_relIndex (fzBar z R) ((K.subgroupOf C).map π) Mbar
      hHK hKL).symm
  intro h2
  have h2' : 2 ∣ R.relIndex K := by
    rw [hK]
    exact h2
  exact hnot (by rw [hrel, ← hRK_eq]; exact dvd_mul_of_dvd_left h2' _)

end CFSG.OddStandard.SmallF3.FritzII
