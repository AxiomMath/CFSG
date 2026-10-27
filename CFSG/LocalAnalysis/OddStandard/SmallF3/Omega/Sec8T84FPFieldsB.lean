module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPList

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.Asc82NormA6 (Facts)
open Certificates.T84P (Elt mulE oneE M0l Vl F0l Jl P0l)

private lemma t84B_mulE_oneE (x : Elt) : mulE x oneE = x := by
  simp [mulE, oneE]

private lemma t84B_mulE_oneE_left (x : Elt) : mulE oneE x = x := by
  simp [mulE, oneE]

private lemma t84B_oneE_mem_Vl (F : Facts) : oneE ∈ Vl := by
  rw [← sec8t84FPRaw_one F]
  exact (sec8t84FPV0_mem F 1).mp (Sec8T84FPV0 F).one_mem

theorem sec8t84FPJ_eq (F : Facts) (G : Certificates.T84P.Facts) :
    Sec8T84FPV0 F ⊔ sec8t84FPF0 F G = sec8t84FPJ0 F G := by
  obtain ⟨-, -, hVP0, hVmul, -, -, -⟩ := G.vf.1
  obtain ⟨hFnd, hFlen, hFP0, hFmul, -, -, -⟩ := G.vf.2.1
  obtain ⟨-, -, hJP0, hJmul⟩ := G.j
  obtain ⟨-, -, h1P0, hP0M, hP0mul⟩ := G.p0
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro x hx
    change sec8t84FPRaw F x ∈ Jl
    rw [Jl, List.mem_dedup]
    exact List.mem_flatMap.mpr ⟨sec8t84FPRaw F x, (sec8t84FPV0_mem F x).mp hx,
      List.mem_map.mpr ⟨oneE, sec8t84_oneE_F0l G, t84B_mulE_oneE _⟩⟩
  · intro x hx
    have hxF : sec8t84FPRaw F x ∈ F0l :=
      (sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) hFmul x).mp hx
    change sec8t84FPRaw F x ∈ Jl
    rw [Jl, List.mem_dedup]
    exact List.mem_flatMap.mpr ⟨oneE, t84B_oneE_mem_Vl F,
      List.mem_map.mpr ⟨sec8t84FPRaw F x, hxF, t84B_mulE_oneE_left _⟩⟩
  · intro z hz
    change sec8t84FPRaw F z ∈ Jl at hz
    rw [Jl, List.mem_dedup] at hz
    obtain ⟨x, hxV, hxJ⟩ := List.mem_flatMap.mp hz
    obtain ⟨y, hyF, hyx⟩ := List.mem_map.mp hxJ
    obtain ⟨u, hu⟩ := sec8t84FPRaw_surj F (hP0M x (hVP0 x hxV))
    obtain ⟨w, hw⟩ := sec8t84FPRaw_surj F (hP0M y (hFP0 y hyF))
    have hraw : sec8t84FPRaw F (u * w) = sec8t84FPRaw F z := by
      rw [sec8t84FPRaw_mul, hu, hw, hyx]
    have hz_eq : z = u * w := (sec8t84FPRaw_injective F hraw).symm
    rw [hz_eq]
    exact Subgroup.mul_mem_sup
      ((sec8t84FPV0_mem F u).mpr (by rw [hu]; exact hxV))
      ((sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) hFmul w).mpr (by rw [hw]; exact hyF))

theorem sec8t84FPJ_card (F : Facts) (G : Certificates.T84P.Facts) :
    Nat.card ↥(Sec8T84FPV0 F ⊔ sec8t84FPF0 F G) = 64 := by
  obtain ⟨-, hJlen, hJP0, hJmul⟩ := G.j
  obtain ⟨-, -, -, hP0M, -⟩ := G.p0
  rw [sec8t84FPJ_eq F G]
  change Nat.card (sec8t84FPOfList F Jl (sec8t84_oneE_Jl G) hJmul) = 64
  rw [sec8t84FPOfList_card_eq_length F (sec8t84_oneE_Jl G) hJmul
    (fun z hz => hP0M z (hJP0 z hz)) G.j.1]
  exact hJlen

theorem sec8t84FPEF_card (F : Facts) (G : Certificates.T84P.Facts) :
    Nat.card ↥(Sec8T84FPV0 F ⊓ sec8t84FPF0 F G) = 4 := by
  obtain ⟨hVnd, -, hVP0, hVmul, -, -, -⟩ := G.vf.1
  obtain ⟨-, -, hFP0, hFmul, -, -, -⟩ := G.vf.2.1
  obtain ⟨-, -, -, hP0M, -⟩ := G.p0
  have hl1 : oneE ∈ Vl.filter (fun x => x ∈ F0l) := by
    rw [List.mem_filter]
    exact ⟨t84B_oneE_mem_Vl F, by simp [sec8t84_oneE_F0l G]⟩
  have hmul : ∀ x ∈ Vl.filter (fun x => x ∈ F0l),
      ∀ y ∈ Vl.filter (fun x => x ∈ F0l),
        mulE x y ∈ Vl.filter (fun x => x ∈ F0l) := by
    intro x hx y hy
    rw [List.mem_filter] at hx hy ⊢
    simp only [decide_eq_true_eq] at hx hy ⊢
    exact ⟨hVmul x hx.1 y hy.1, hFmul x hx.2 y hy.2⟩
  have hl : ∀ z ∈ Vl.filter (fun x => x ∈ F0l), z ∈ M0l := by
    intro z hz
    rw [List.mem_filter] at hz
    exact hP0M z (hVP0 z hz.1)
  have hnd : (Vl.filter (fun x => x ∈ F0l)).Nodup := hVnd.filter _
  have hsub : Sec8T84FPV0 F ⊓ sec8t84FPF0 F G =
      sec8t84FPOfList F (Vl.filter fun x => x ∈ F0l) hl1 hmul := by
    ext x
    rw [Subgroup.mem_inf, sec8t84FPV0_mem]
    change (sec8t84FPRaw F x ∈ Vl ∧ sec8t84FPRaw F x ∈ F0l) ↔
      sec8t84FPRaw F x ∈ Vl.filter (fun x => x ∈ F0l)
    rw [List.mem_filter]
    simp [decide_eq_true_eq]
  have hcard : Nat.card ↥(Sec8T84FPV0 F ⊓ sec8t84FPF0 F G) =
      (Vl.filter (fun x => x ∈ F0l)).length := by
    rw [hsub]
    exact sec8t84FPOfList_card_eq_length F hl1 hmul hl hnd
  rw [hcard]
  exact G.vf.2.2.2

theorem sec8t84FPcent_V (F : Facts) (G : Certificates.T84P.Facts) :
    sec8t84FPP0 F G ⊓ centralizer (Sec8T84FPV0 F : Set (Sec8T84FPM0 F)) = Sec8T84FPV0 F := by
  obtain ⟨-, -, hVP0, hVmul, hVsq, hVcomm, -⟩ := G.vf.1
  obtain ⟨-, -, h1P0, hP0M, hP0mul⟩ := G.p0
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxP0, hxcent⟩ := hx
    rw [sec8t84FPV0_mem]
    refine G.cent.1 (sec8t84FPRaw F x) ?_ ?_
    · exact (sec8t84FPOfList_mem F h1P0 hP0mul x).mp hxP0
    · intro y hy
      obtain ⟨u, hu⟩ := sec8t84FPRaw_surj F (hP0M y (hVP0 y hy))
      have huV : u ∈ Sec8T84FPV0 F := (sec8t84FPV0_mem F u).mpr (by rw [hu]; exact hy)
      have hcomm : u * x = x * u := (Subgroup.mem_centralizer_iff.mp hxcent) u huV
      rw [← hu]
      exact (sec8t84FPRaw_commE_iff F x u).mpr hcomm.symm
  · intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨(sec8t84FPOfList_mem F h1P0 hP0mul x).mpr
      (hVP0 (sec8t84FPRaw F x) ((sec8t84FPV0_mem F x).mp hx)), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (sec8t84FPRaw_commE_iff F h x).mp
      (hVcomm (sec8t84FPRaw F h) ((sec8t84FPV0_mem F h).mp hh)
        (sec8t84FPRaw F x) ((sec8t84FPV0_mem F x).mp hx))

theorem sec8t84FPcent_F (F : Facts) (G : Certificates.T84P.Facts) :
    sec8t84FPP0 F G ⊓ centralizer (sec8t84FPF0 F G : Set (Sec8T84FPM0 F)) =
      sec8t84FPF0 F G := by
  obtain ⟨-, -, hFP0, hFmul, -, hFcomm, -⟩ := G.vf.2.1
  obtain ⟨-, -, h1P0, hP0M, hP0mul⟩ := G.p0
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxP0, hxcent⟩ := hx
    change sec8t84FPRaw F x ∈ F0l
    refine G.cent.2 (sec8t84FPRaw F x) ?_ ?_
    · exact (sec8t84FPOfList_mem F h1P0 hP0mul x).mp hxP0
    · intro y hy
      obtain ⟨u, hu⟩ := sec8t84FPRaw_surj F (hP0M y (hFP0 y hy))
      have huF : u ∈ sec8t84FPF0 F G :=
        (sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) hFmul u).mpr (by rw [hu]; exact hy)
      have hcomm : u * x = x * u := (Subgroup.mem_centralizer_iff.mp hxcent) u huF
      rw [← hu]
      exact (sec8t84FPRaw_commE_iff F x u).mpr hcomm.symm
  · intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨(sec8t84FPOfList_mem F h1P0 hP0mul x).mpr
      (hFP0 (sec8t84FPRaw F x)
        ((sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) hFmul x).mp hx)), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (sec8t84FPRaw_commE_iff F h x).mp
      (hFcomm (sec8t84FPRaw F h) ((sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) hFmul h).mp hh)
        (sec8t84FPRaw F x) ((sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) hFmul x).mp hx))

end CFSG.OddStandard.SmallF3.Omega
