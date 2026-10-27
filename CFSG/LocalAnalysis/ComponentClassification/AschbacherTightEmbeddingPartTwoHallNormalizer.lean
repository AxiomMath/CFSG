module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normal_subgroup_conjugate_map_subtype (M : Subgroup G) [M.Normal]
    (D : Subgroup M) (g : G) :
    (D.map (MulAut.conjNormal g).toMonoidHom).map M.subtype =
      (D.map M.subtype).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem normal_hall_normalizer_factorization (M : Subgroup G) [M.Normal]
    (hsolv : Group.IsSolvable M) (π : Set Nat.Primes) (D : Subgroup M)
    (hHall : CFSG.IsHallSubgroup π D) (g : G) :
    ∃ m : M, ∃ n ∈ Subgroup.normalizer (D.map M.subtype : Set G),
      g = (m : G) * n := by
  let e : MulAut M := MulAut.conjNormal g
  obtain ⟨m, hm⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable
    hsolv hHall (hHall.map_mulAut e)
  have hmaps : (D.map M.subtype).map (MulAut.conj g).toMonoidHom =
      (D.map M.subtype).map (MulAut.conj (m : G)).toMonoidHom := by
    have h := congrArg (fun E : Subgroup M => E.map M.subtype) hm
    rw [show e = MulAut.conjNormal g from rfl,
      normal_subgroup_conjugate_map_subtype,
      ← MulAut.conjNormal_val (h := m),
      normal_subgroup_conjugate_map_subtype] at h
    exact h
  let n : G := (m : G)⁻¹ * g
  have hn : n ∈ Subgroup.normalizer (D.map M.subtype : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (D.map M.subtype).map (MulAut.conj n).toMonoidHom = D.map M.subtype
    have hcomp : (MulAut.conj n).toMonoidHom =
        (MulAut.conj (m : G)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      dsimp only [n]
      group
    rw [hcomp, ← Subgroup.map_map, hmaps, Subgroup.map_map]
    have hcancel :
        (MulAut.conj (m : G)⁻¹).toMonoidHom.comp
          (MulAut.conj (m : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, MonoidHom.id_apply]
      group
    rw [hcancel, Subgroup.map_id]
  exact ⟨m, n, hn, by dsimp only [n]; group⟩

theorem normal_hall_complement_normalizer_factorization
    (M : Subgroup G) [M.Normal] (hsolv : Group.IsSolvable M)
    (π : Set Nat.Primes) (R D : Subgroup M)
    (hHall : CFSG.IsHallSubgroup π D) (hcompl : R.IsComplement' D) (g : G) :
    ∃ r ∈ R.map M.subtype,
      ∃ n ∈ Subgroup.normalizer (D.map M.subtype : Set G), g = r * n := by
  obtain ⟨m, n, hn, hmn⟩ := normal_hall_normalizer_factorization M hsolv π D hHall g
  obtain ⟨⟨r, d⟩, hrd⟩ := hcompl.2 m
  have hrdG : (r : G) * (d : G) = (m : G) := congrArg Subtype.val hrd
  have hd : (d : G) ∈ Subgroup.normalizer (D.map M.subtype : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_map_of_mem M.subtype d.property)
  refine ⟨r, Subgroup.mem_map_of_mem M.subtype r.property, (d : G) * n,
    (Subgroup.normalizer _).mul_mem hd hn, ?_⟩
  rw [hmn, ← hrdG, mul_assoc]

theorem hall_normalizer_intersection_odd (Q R D : Subgroup G)
    (hcontain : ∀ x ∈ Q, orderOf x = 2 → x ∈ R)
    (hdisjoint : Disjoint R (Subgroup.normalizer (D : Set G))) :
    Odd (Nat.card (Q ⊓ Subgroup.normalizer (D : Set G) : Subgroup G)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let N := Subgroup.normalizer (D : Set G)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q ⊓ N)) 2 heven.two_dvd
  have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxR : (x : G) ∈ R := hcontain x x.property.1 hxG
  have hxone : (x : G) = 1 :=
    Subgroup.disjoint_def.mp hdisjoint hxR x.property.2
  have hxone' : x = 1 := Subtype.ext hxone
  rw [hxone', orderOf_one] at hx
  norm_num at hx

theorem hall_normalizer_internal_complement
    (M : Subgroup G) [M.Normal] (hsolv : Group.IsSolvable M)
    (π : Set Nat.Primes) (R D : Subgroup M)
    (hHall : CFSG.IsHallSubgroup π D) (hcompl : R.IsComplement' D)
    (Q : Subgroup G) (hRQ : R.map M.subtype ≤ Q)
    (hdisjoint : Disjoint (R.map M.subtype)
      (Subgroup.normalizer (D.map M.subtype : Set G))) :
    ((R.map M.subtype).subgroupOf Q).IsComplement'
      ((Subgroup.normalizer (D.map M.subtype : Set G)).subgroupOf Q) := by
  let A := (R.map M.subtype).subgroupOf Q
  let B := (Subgroup.normalizer (D.map M.subtype : Set G)).subgroupOf Q
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro x hxA hxB
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisjoint hxA hxB
  · apply Set.eq_univ_of_forall
    intro q
    obtain ⟨r, hr, n, hn, hqn⟩ :=
      normal_hall_complement_normalizer_factorization M hsolv π R D hHall hcompl q
    have hrQ := hRQ hr
    have hnQ : n ∈ Q := by
      have h := Q.mul_mem (Q.inv_mem hrQ) q.property
      rw [hqn] at h
      simpa only [inv_mul_cancel_left] using h
    let rQ : Q := ⟨r, hrQ⟩
    let nQ : Q := ⟨n, hnQ⟩
    exact Set.mem_mul.mpr ⟨rQ, hr, nQ, hn, Subtype.ext hqn.symm⟩

theorem odd_relative_index_of_hall_normalizer
    (M : Subgroup G) [M.Normal] (hsolv : Group.IsSolvable M)
    (π : Set Nat.Primes) (R D : Subgroup M)
    (hHall : CFSG.IsHallSubgroup π D) (hcompl : R.IsComplement' D)
    (Q : Subgroup G) (hRQ : R.map M.subtype ≤ Q)
    (hcontain : ∀ x ∈ Q, orderOf x = 2 → x ∈ R.map M.subtype)
    (hdisjoint : Disjoint (R.map M.subtype)
      (Subgroup.normalizer (D.map M.subtype : Set G))) :
    Odd ((R.map M.subtype).subgroupOf Q).index := by
  have hc := hall_normalizer_internal_complement M hsolv π R D hHall hcompl Q hRQ hdisjoint
  rw [hc.symm.index_eq_card]
  have hcard :
      Nat.card ((Subgroup.normalizer (D.map M.subtype : Set G)).subgroupOf Q) =
        Nat.card (Q ⊓ Subgroup.normalizer (D.map M.subtype : Set G) : Subgroup G) := by
    calc
      _ = Nat.card (((Subgroup.normalizer (D.map M.subtype : Set G)).subgroupOf Q).map
          Q.subtype) := (Subgroup.card_subtype _ _).symm
      _ = _ := by rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hcard]
  exact hall_normalizer_intersection_odd Q (R.map M.subtype) (D.map M.subtype)
    hcontain hdisjoint

end CFSG.ComponentClassification.AschbacherTightEmbedding
