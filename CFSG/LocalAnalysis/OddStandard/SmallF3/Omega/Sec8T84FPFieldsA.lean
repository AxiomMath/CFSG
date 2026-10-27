module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPList
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.Asc82NormA6 (Facts)

theorem sec8t84FPP0_card (F : Facts) (G : Certificates.T84P.Facts) :
    Nat.card (sec8t84FPP0 F G) = 128 := by
  rw [sec8t84FPP0,
    sec8t84FPOfList_card_eq_length F G.p0.2.2.1 G.p0.2.2.2.2 G.p0.2.2.2.1 G.p0.1]
  exact G.p0.2.1

theorem sec8t84FPP0_sylow (F : Facts) (G : Certificates.T84P.Facts) :
    IsSylow2Of (sec8t84FPP0 F G) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 7) (by rw [sec8t84FPP0_card F G]; norm_num)
  · rw [Subgroup.relIndex_top_right]
    intro h
    have hmul := Subgroup.card_mul_index (sec8t84FPP0 F G)
    rw [sec8t84FPP0_card F G, sec8t84FPM0_card F] at hmul
    have hidx : (sec8t84FPP0 F G).index = 45 := by omega
    rw [hidx] at h
    norm_num at h

theorem sec8t84FPV0_le_P0 (F : Facts) (G : Certificates.T84P.Facts) :
    Sec8T84FPV0 F ≤ sec8t84FPP0 F G := by
  intro x hx
  rw [sec8t84FPV0_mem] at hx
  show sec8t84FPRaw F x ∈ Certificates.T84P.P0l
  exact G.vf.1.2.2.1 _ hx

theorem sec8t84FPF0_le_P0 (F : Facts) (G : Certificates.T84P.Facts) :
    sec8t84FPF0 F G ≤ sec8t84FPP0 F G := by
  intro x hx
  show sec8t84FPRaw F x ∈ Certificates.T84P.P0l
  exact G.vf.2.1.2.2.1 _ hx

theorem sec8t84FPF0_card (F : Facts) (G : Certificates.T84P.Facts) :
    Nat.card (sec8t84FPF0 F G) = 16 := by
  rw [sec8t84FPF0,
    sec8t84FPOfList_card_eq_length F (sec8t84_oneE_F0l G) G.vf.2.1.2.2.2.1
      (fun z hz => G.p0.2.2.2.1 z (G.vf.2.1.2.2.1 z hz)) G.vf.2.1.1]
  exact G.vf.2.1.2.1

theorem sec8t84FPF0_e16 (F : Facts) (G : Certificates.T84P.Facts) :
    IsElemAb2 (sec8t84FPF0 F G) 4 := by
  obtain ⟨-, -, -, -, hsq, hcomm, -⟩ := G.vf.2.1
  have hcomm' : IsMulCommutative (sec8t84FPF0 F G) :=
    ⟨⟨fun a b => by
      apply Subtype.ext
      change (a : Sec8T84FPM0 F) * (b : Sec8T84FPM0 F) =
        (b : Sec8T84FPM0 F) * (a : Sec8T84FPM0 F)
      rw [← sec8t84FPRaw_commE_iff]
      exact hcomm (sec8t84FPRaw F a.1) a.2 (sec8t84FPRaw F b.1) b.2⟩⟩
  have hsq' : ∀ x ∈ sec8t84FPF0 F G, x ^ 2 = 1 := by
    intro x hx
    rw [pow_two, ← sec8t84FPRaw_mul_self_iff]
    exact hsq (sec8t84FPRaw F x) hx
  exact ⟨⟨hcomm', hsq'⟩, by rw [sec8t84FPF0_card F G]; norm_num⟩

theorem sec8t84FPF0_ne (F : Facts) (G : Certificates.T84P.Facts) :
    sec8t84FPF0 F G ≠ Sec8T84FPV0 F := by
  obtain ⟨x, hxF, hxV⟩ := G.vf.2.2.1
  obtain ⟨y, hy⟩ := sec8t84FPRaw_surj F (G.p0.2.2.2.1 x (G.vf.2.1.2.2.1 x hxF))
  intro h
  have hyF : y ∈ sec8t84FPF0 F G := by
    show sec8t84FPRaw F y ∈ Certificates.T84P.F0l
    rw [hy]
    exact hxF
  have hyV : sec8t84FPRaw F y ∈ Certificates.T84P.Vl :=
    (sec8t84FPV0_mem F y).mp (h ▸ hyF)
  rw [hy] at hyV
  exact hxV hyV

theorem sec8t84FPF0_norm (F : Facts) (G : Certificates.T84P.Facts) :
    ((sec8t84FPF0 F G).subgroupOf (sec8t84FPP0 F G)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (sec8t84FPF0_le_P0 F G)).mpr ?_
  intro h k hh hk
  have hh' : sec8t84FPRaw F h ∈ Certificates.T84P.F0l := hh
  have hk' : sec8t84FPRaw F k ∈ Certificates.T84P.P0l := hk
  have hkq : sec8t84FPRaw F k⁻¹ ∈ Certificates.T84P.P0l :=
    (sec8t84FPP0 F G).inv_mem hk
  have hnorm := G.vf.2.1.2.2.2.2.2.2
  have hres := hnorm (sec8t84FPRaw F k) hk' (sec8t84FPRaw F k⁻¹) hkq
    (sec8t84FPRaw_mul_inv F k) (sec8t84FPRaw F h) hh'
  show sec8t84FPRaw F (k * h * k⁻¹) ∈ Certificates.T84P.F0l
  rw [sec8t84FPRaw_mul, sec8t84FPRaw_mul]
  exact hres

end CFSG.OddStandard.SmallF3.Omega
