module

public import CFSG.FeitThompson.Local.Omega1CentralizerCommutatorBound
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.MaximalNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion
import CFSG.FeitThompson.Local.PrimeGeneratedCentralTorsionExponent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p n : ℕ} {P : Type*} [Group P] {D : Subgroup P}

theorem exists_maximal_normal_isMulCommutative_ge [Finite P] (hDn : D.Normal)
    (hDc : IsMulCommutative ↥D) :
    ∃ A : Subgroup P, D ≤ A ∧
      Maximal (fun B : Subgroup P => B.Normal ∧ IsMulCommutative ↥B) A := by
  obtain ⟨A, hDA, hA⟩ := Set.Finite.exists_le_maximal
    (s := {B : Subgroup P | B.Normal ∧ IsMulCommutative ↥B}) (Set.toFinite _) ⟨hDn, hDc⟩
  exact ⟨A, hDA, hA⟩

theorem conj_mem_setOf_mem_centralizer_pow_eq_one {N : Subgroup P} [hN : N.Normal] (g : P) {x : P}
    (hx : x ∈ centralizer (N : Set P) ∧ x ^ p = 1) :
    g * x * g⁻¹ ∈ centralizer (N : Set P) ∧ (g * x * g⁻¹) ^ p = 1 := by
  refine ⟨mem_centralizer_iff.2 fun d hd => ?_, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
  have hd' : g⁻¹ * d * g ∈ N := by simpa using hN.conj_mem d hd g⁻¹
  have hcomm := mem_centralizer_iff.1 hx.1 _ hd'
  calc d * (g * x * g⁻¹) = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * x * g⁻¹) * d := by group

theorem normal_closure_setOf_mem_centralizer_pow_eq_one {N : Subgroup P} [N.Normal] :
    (closure {x : P | x ∈ centralizer (N : Set P) ∧ x ^ p = 1}).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have key : ∀ y ∈ closure {x : P | x ∈ centralizer (N : Set P) ∧ x ^ p = 1},
      g * y * g⁻¹ ∈ closure {x : P | x ∈ centralizer (N : Set P) ∧ x ^ p = 1} := by
    intro y hy
    induction hy using closure_induction with
    | mem z hz => exact subset_closure (conj_mem_setOf_mem_centralizer_pow_eq_one g hz)
    | one => simp
    | mul a b _ _ ha hb =>
        rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
        exact mul_mem ha hb
    | inv a _ ha =>
        rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
        exact inv_mem ha
  exact key x hx

theorem closure_setOf_mem_centralizer_pow_eq_one_eq_of_maximal
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hD : Maximal (fun B : Subgroup P => B.Normal ∧ IsElementaryAbelian p B) D) :
    closure {x : P | x ∈ centralizer (D : Set P) ∧ x ^ p = 1} = D := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨⟨hDn, hDea⟩, hDmax⟩ := hD
  have hDn' := hDn
  have hDc : IsMulCommutative ↥D := hDea.isMulCommutative
  obtain ⟨A, hDA, hA⟩ := exists_maximal_normal_isMulCommutative_ge hDn hDc
  have hAn : A.Normal := hA.prop.1
  have hAc : IsMulCommutative ↥A := hA.prop.2
  have hcentA : centralizer (A : Set P) = A :=
    centralizer_eq_of_maximal_normal_isMulCommutative hp hcard hA
  have hApD : pTorsionSet p A = (D : Set P) := by
    have hset : pTorsionSet p A = (((omega1 p ↥A).map A.subtype : Subgroup P) : Set P) :=
      pTorsionSet_eq_coe_omega1_map A
    have hDpn : ((omega1 p ↥A).map A.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hDple : (omega1 p ↥A).map A.subtype ≤ A := map_subtype_le _
    have hDpea : IsElementaryAbelian p ((omega1 p ↥A).map A.subtype) := by
      refine isElementaryAbelian_iff.2 ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
        setLike_mul_comm (s := A) (hDple ha) (hDple hb), fun x hx => ?_⟩
      have hx' : x ∈ pTorsionSet p A := by rw [hset]; exact hx
      exact (mem_pTorsionSet.1 hx').2
    have hDDp : D ≤ (omega1 p ↥A).map A.subtype := by
      intro x hx
      have hx' : x ∈ pTorsionSet p A := mem_pTorsionSet.2 ⟨hDA hx, hDea.pow_eq_one hx⟩
      rw [hset] at hx'; exact hx'
    have heq : (omega1 p ↥A).map A.subtype = D :=
      le_antisymm (hDmax ⟨hDpn, hDpea⟩ hDDp) hDDp
    rw [hset, heq]
  have hXeq : omega1Centralizer p A
      = closure {x : P | x ∈ centralizer (D : Set P) ∧ x ^ p = 1} := by
    rw [omega1Centralizer_eq_closure, hApD]
  rw [← hXeq]
  have hXcentD : omega1Centralizer p A ≤ centralizer (D : Set P) := by
    have := omega1Centralizer_le_centralizer (p := p) (B := A)
    rwa [hApD] at this
  have hXclos : closure {x : P | x ∈ omega1Centralizer p A ∧ x ^ p = 1}
      = omega1Centralizer p A := by
    refine le_antisymm ((closure_le _).2 fun x hx => hx.1) ?_
    rw [omega1Centralizer_eq_closure]
    exact (closure_le _).2 fun x hx => subset_closure ⟨subset_closure hx, hx.2⟩
  have hgen : omega1 p ↥(omega1Centralizer p A) = ⊤ := by
    refine Subgroup.map_injective (subtype_injective _) ?_
    rw [coe_map_omega1_subtype, hXclos, ← MonoidHom.range_eq_map, range_subtype]
  have hcent : ∀ c ∈ commutator ↥(omega1Centralizer p A), c ^ p = 1 →
      c ∈ center ↥(omega1Centralizer p A) := by
    intro c hc hcp
    have hmapc : (commutator ↥(omega1Centralizer p A)).map (omega1Centralizer p A).subtype
        = ⁅omega1Centralizer p A, omega1Centralizer p A⁆ := by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    have hcP : (c : P) ∈ ⁅omega1Centralizer p A, omega1Centralizer p A⁆ :=
      hmapc ▸ mem_map_of_mem _ hc
    have hcpP : (c : P) ^ p = 1 := by simpa using congrArg Subtype.val hcp
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (by
      simpa using
        mul_comm_of_mem_commutator_of_pow_eq_one A hp hodd hcard hcentA hcP hcpP g.2)
  have hexp : ∀ x ∈ omega1Centralizer p A, x ^ p = 1 := by
    intro x hx
    have h := pow_eq_one_of_omega1_eq_top hp hodd
      ((IsPGroup.of_card hcard).to_subgroup _) hgen hcent ⟨x, hx⟩
    simpa using congrArg Subtype.val h
  have hXn : (omega1Centralizer p A).Normal := by
    rw [hXeq]; exact normal_closure_setOf_mem_centralizer_pow_eq_one
  have hDX : D ≤ omega1Centralizer p A := by
    intro x hx
    refine mem_omega1Centralizer_of ?_ (hDea.pow_eq_one hx)
    rw [hApD]
    exact Subgroup.le_centralizer D hx
  refine le_antisymm ?_ hDX
  by_contra hne
  have hker : (QuotientGroup.mk' D).ker = D := QuotientGroup.ker_mk' D
  have hLne : (omega1Centralizer p A).map (QuotientGroup.mk' D) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, hker] at h
    exact hne h
  have : ((omega1Centralizer p A).map (QuotientGroup.mk' D)).Normal :=
    hXn.map _ (QuotientGroup.mk'_surjective D)
  obtain ⟨b, hb⟩ := ((IsPGroup.of_card hcard).to_quotient D).exists_card_eq
  obtain ⟨Q, hQle, hQcard⟩ :=
    exists_le_inf_center_natCard_eq ((omega1Centralizer p A).map (QuotientGroup.mk' D)) hp hb hLne
  have hDE : D ≤ Q.comap (QuotientGroup.mk' D) := fun x hx => Subgroup.mem_comap.mpr <| by
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem Q
  have hEX : Q.comap (QuotientGroup.mk' D) ≤ omega1Centralizer p A :=
    calc Q.comap (QuotientGroup.mk' D)
        ≤ ((omega1Centralizer p A).map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D) :=
          Subgroup.comap_mono (hQle.trans inf_le_left)
      _ = omega1Centralizer p A := Subgroup.comap_map_eq_self (hker.le.trans hDX)
  have hQn : Q.Normal :=
    ⟨fun m hm g => by
      rw [Subgroup.mem_center_iff.mp (hQle.trans inf_le_right hm) g, mul_inv_cancel_right]
      exact hm⟩
  have hEn : (Q.comap (QuotientGroup.mk' D)).Normal := hQn.comap _
  have hEc : IsMulCommutative ↥(Q.comap (QuotientGroup.mk' D)) := by
    have : IsCyclic Q := isCyclic_of_prime_card hQcard
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (((QuotientGroup.mk' D).comp (Q.comap (QuotientGroup.mk' D)).subtype).codRestrict Q
        (fun x => Subgroup.mem_comap.mp x.2)) ?_
    intro x hx
    have hxD : (x : P) ∈ D := by
      have hx1 : (QuotientGroup.mk' D) (x : P) = 1 := by
        have := congrArg Subtype.val hx
        simpa [MonoidHom.codRestrict] using this
      exact (QuotientGroup.eq_one_iff (x : P)).mp (by simpa using hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := Subgroup.mem_centralizer_iff.mp (hXcentD (hEX y.2)) (x : P) hxD
    exact Subtype.ext (by simpa using hy.symm)
  have hEea : IsElementaryAbelian p (Q.comap (QuotientGroup.mk' D)) :=
    isElementaryAbelian_iff.2 ⟨hEc, fun x hx => hexp x (hEX hx)⟩
  have hED : Q.comap (QuotientGroup.mk' D) = D :=
    le_antisymm (hDmax ⟨hEn, hEea⟩ hDE) hDE
  have hQbot : Q = ⊥ := by
    have hmc := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D) Q
    rw [hED] at hmc
    rw [← hmc, Subgroup.map_eq_bot_iff, hker]
  rw [hQbot, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hQcard
  exact hp.one_lt.ne hQcard

theorem mem_of_mem_centralizer_of_pow_eq_one_of_maximal
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hD : Maximal (fun B : Subgroup P => B.Normal ∧ IsElementaryAbelian p B) D)
    {x : P} (hx : x ∈ centralizer (D : Set P)) (hxp : x ^ p = 1) : x ∈ D :=
  closure_setOf_mem_centralizer_pow_eq_one_eq_of_maximal hp hodd hcard hD ▸
    subset_closure (⟨hx, hxp⟩ : x ∈ {y : P | y ∈ centralizer (D : Set P) ∧ y ^ p = 1})

theorem setOf_mem_centralizer_pow_eq_one_eq_of_maximal
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hD : Maximal (fun B : Subgroup P => B.Normal ∧ IsElementaryAbelian p B) D) :
    {x : P | x ∈ centralizer (D : Set P) ∧ x ^ p = 1} = (D : Set P) := by
  refine Set.Subset.antisymm (fun x hx =>
    mem_of_mem_centralizer_of_pow_eq_one_of_maximal hp hodd hcard hD hx.1 hx.2) fun x hx => ?_
  have hDc : IsMulCommutative ↥D := hD.prop.2.isMulCommutative
  exact ⟨Subgroup.le_centralizer D hx, hD.prop.2.pow_eq_one hx⟩

theorem omega1Centralizer_eq_of_maximal
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hD : Maximal (fun B : Subgroup P => B.Normal ∧ IsElementaryAbelian p B) D) :
    omega1Centralizer p D = D := by
  have hDD : pTorsionSet p D = (D : Set P) :=
    Set.Subset.antisymm (fun _ h => (mem_pTorsionSet.1 h).1) fun x hx =>
      mem_pTorsionSet.2 ⟨hx, hD.prop.2.pow_eq_one hx⟩
  rw [omega1Centralizer_eq_closure, hDD]
  exact closure_setOf_mem_centralizer_pow_eq_one_eq_of_maximal hp hodd hcard hD

theorem closure_setOf_mem_centralizer_pow_eq_one_eq_of_maximal_of_isPGroup [Finite P]
    (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hD : Maximal (fun B : Subgroup P => B.Normal ∧ IsElementaryAbelian p B) D) :
    closure {x : P | x ∈ centralizer (D : Set P) ∧ x ^ p = 1} = D := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  exact closure_setOf_mem_centralizer_pow_eq_one_eq_of_maximal hp hodd ha hD

end

end CFSG.FeitThompson
