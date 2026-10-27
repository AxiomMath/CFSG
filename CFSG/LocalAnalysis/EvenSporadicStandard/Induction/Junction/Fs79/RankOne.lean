module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Quat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.GWExc
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Sylow

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

theorem sol78RankOne_proved : Sol78RankOne := by
  intro X _ _ hq hr
  have hsimple : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hP2 := hq.2.2
  let P : Sylow 2 X := default
  let π : X →* X ⧸ center X := QuotientGroup.mk' (center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let P' : Sylow 2 (X ⧸ center X) := Sylow.mapSurjective hπ P
  have hP' : (P' : Subgroup (X ⧸ center X)) = (P : Subgroup X).map π := Sylow.coe_mapSurjective hπ P
  let gP : ↥(P : Subgroup X) →* ↥(P' : Subgroup (X ⧸ center X)) :=
    (π.comp (P : Subgroup X).subtype).codRestrict _ (fun x => hP' ▸ ⟨x, x.2, rfl⟩)
  have hgP : Function.Surjective gP := by
    rintro ⟨y, hy⟩
    rw [hP'] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp⟩, rfl⟩
  rcases sylow_cyclic_or_quaternion hr P with hcyc | ⟨e, he, ⟨eQ⟩⟩
  · exfalso
    have : IsCyclic ↥(P' : Subgroup (X ⧸ center X)) := isCyclic_of_surjective gP hgP
    exact not_isCyclic_sylow_two hP2 P' this
  · have hm : NeZero (2 ^ e) := ⟨by positivity⟩
    set m : ℕ := 2 ^ e with hmdef
    have hm2 : 2 ≤ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hsq : (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) ^ 2 = 1 := by
      rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
      congr 1
      simpa only [two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)
    have hne1 : (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) ≠ 1 := by
      intro h
      rw [QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h
      have h1 := (ZMod.natCast_eq_zero_iff m (2 * m)).1 h
      have := Nat.le_of_dvd (by omega) h1
      omega
    have hord : orderOf (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) = 2 :=
      orderOf_eq_prime hsq hne1
    set t : X := ((eQ (QuaternionGroup.a (m : ZMod (2 * m))) : ↥(P : Subgroup X)) : X) with ht
    have htP : t ∈ (P : Subgroup X) := (eQ (QuaternionGroup.a (m : ZMod (2 * m)))).2
    have htord : orderOf t = 2 := by
      rw [ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
    have hquat : Nonempty ((P : Subgroup X) ≃* QuaternionGroup (2 ^ (e + 2 - 2))) := by
      rw [Nat.add_sub_cancel]
      exact ⟨eQ.symm⟩
    have hBS := CFSG.BrauerSuzuki.brauer_suzuki (e + 2) (by omega) P hquat t htP htord
    have htc : t ∈ center X := mem_center_of_mk_mem_center_oddCore hq hBS
    let g : QuaternionGroup m →* ↥(P' : Subgroup (X ⧸ center X)) := gP.comp eQ.toMonoidHom
    have hg : Function.Surjective g := hgP.comp eQ.surjective
    have hgt : g (QuaternionGroup.a (m : ZMod (2 * m))) = 1 := by
      apply Subtype.ext
      show π t = 1
      exact (QuotientGroup.eq_one_iff t).2 htc
    have hB := isCyclic_or_dihedral_of_gen (A := QuaternionGroup m) P'.isPGroup' g
      (ρ := QuaternionGroup.a 1) (σ := QuaternionGroup.xa 0)
      (by rw [quaternion_gen m, Subgroup.map_top_of_surjective g hg])
      (by rw [MonoidHom.mem_ker, QuaternionGroup.xa_sq]; exact hgt)
      (by rw [MonoidHom.mem_ker, quaternion_rel m, map_one])
    rcases hB with hB | ⟨j, hj, hS⟩
    · exact absurd hB (not_isCyclic_sylow_two hP2 P')
    · exact excType_of_dihedral_sylow hq P' hj hS

end CFSG.EvenSporadicStandard.Induction.Junction
