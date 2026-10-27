module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenMatrix
public import CFSG.LieType.CentralExt.CoprimeLift

public section

open Subgroup
open CFSG.LieType.CentralExt
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.RankTwoL3Even

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem normal_sylow_two_involution_centralizer_of_odd_central_psl_three
    {A : Type u} [Group A] [Finite A]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (π : A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (hker : π.ker ≤ Subgroup.center A)
    (hodd : Odd (Nat.card π.ker))
    {v : A} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (P : Sylow 2 (Subgroup.centralizer ({v} : Set A))) :
    (P : Subgroup (Subgroup.centralizer ({v} : Set A))).Normal := by
  classical
  have hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup A := Subgroup.centralizer ({v} : Set A)
  have hnot2 : ¬ 2 ∣ Nat.card π.ker := hodd.not_two_dvd_nat
  have hpi2 : π v * π v = 1 := by
    rw [← map_mul, hv2, map_one]
  have hpi1 : π v ≠ 1 := by
    intro h
    apply hv1
    refine eq_one_of_mem_ker (p := 2) (hp := hprime) hnot2 ?_ (n := 1) ?_
    · simpa [MonoidHom.mem_ker] using h
    · simpa [pow_two] using hv2
  obtain ⟨y, hy⟩ := exists_conj_eq_x0 (F := F) hpi2 hpi1
  let α : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    MulAut.conj y
  have hαv : α (π v) = x0 F := by
    simpa [α, MulAut.conj_apply] using hy
  let V : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    (projUnip F).map α.symm.toMonoidHom
  have hV : IsPGroup 2 V := by
    have hU : IsPGroup 2 (projUnip F) := by
      obtain ⟨S, hS⟩ :=
        exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
      rw [projUnip_eq_projUnitriangular, ← hS]
      exact S.isPGroup'
    exact hU.map α.symm.toMonoidHom
  let L : Subgroup A := liftSubgroup 2 π V
  have hLp : IsPGroup 2 L := liftSubgroup_isPGroup (hp := hprime) hker hV
  let Q : Subgroup C := L.subgroupOf C
  have hQp : IsPGroup 2 Q :=
    show IsPGroup 2 (L.comap C.subtype) from hLp.comap_subtype (K := C)
  have hSQ : ∀ S : Sylow 2 C, (S : Subgroup C) ≤ Q := by
    intro S a ha
    obtain ⟨n, hn⟩ := exists_orderOf_eq_pow_of_mem (hp := hprime) S.isPGroup' ⟨a, ha⟩
    have hnC : orderOf (a : C) = 2 ^ n := by
      simpa using hn
    have hnA : orderOf (a : A) = 2 ^ n := by
      rw [Subgroup.orderOf_coe]
      exact hnC
    have hpowA : (a : A) ^ 2 ^ n = 1 := by
      rw [← hnA, pow_orderOf_eq_one]
    have hcommA : (a : A) * v = v * (a : A) :=
      Subgroup.mem_centralizer_singleton_iff.mp a.2
    have hcommπ : π (a : A) * π v = π v * π (a : A) := by
      simpa using congrArg π hcommA
    have hcommα : α (π (a : A)) * x0 F =
        x0 F * α (π (a : A)) := by
      simpa [map_mul, hαv] using congrArg α hcommπ
    have hpowπ : (π (a : A)) ^ 2 ^ n = 1 := by
      rw [← map_pow, hpowA, map_one]
    have hpowα : (α (π (a : A))) ^ 2 ^ n = 1 := by
      rw [← map_pow, hpowπ, map_one]
    have hmemU : α (π (a : A)) ∈ projUnip F :=
      mem_projUnip_of_commute_x0 hcommα hpowα
    have hpiV : π (a : A) ∈ V := by
      refine Subgroup.mem_map.2 ⟨α (π (a : A)), hmemU, ?_⟩
      exact α.symm_apply_apply (π (a : A))
    have hmemL : (a : A) ∈ L :=
      (mem_liftSubgroup_iff (hp := hprime) hker hV).2 ⟨hpiV, ⟨n, hnA⟩⟩
    show a ∈ Q
    rw [Subgroup.mem_subgroupOf]
    exact hmemL
  have hsingle : Subsingleton (Sylow 2 C) := by
    refine ⟨fun S T => ?_⟩
    have hS : Q = (S : Subgroup C) := S.is_maximal' hQp (hSQ S)
    have hT : Q = (T : Subgroup C) := T.is_maximal' hQp (hSQ T)
    apply Sylow.ext
    rw [← hS, ← hT]
  exact @Sylow.normal_of_subsingleton C _ 2 hsingle P

end CFSG.ComponentClassification.GS79bSec5
