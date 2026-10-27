module

public import CFSG.ClassicalInvolution.Uniform.UFacts
public import CFSG.ClassicalInvolution.Asc77.AscSixBasic
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RThmI
public import CFSG.ClassicalInvolution.Q3.TwinLemmaSL2

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylow2In (K : Subgroup G) : ∃ P : Subgroup G, IsSylow2In P K := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (P := K) (T := ⊥) (IsPGroup.of_card (n := 0) (by simp))
    bot_le
  exact ⟨V, hV⟩

@[expose] noncomputable def sylowOfIsSylow2In {K P : Subgroup G} (h : IsSylow2In P K) :
    Sylow 2 ↥K where
  toSubgroup := P.subgroupOf K
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : P ≤ Q.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
    rfl

omit [Finite G] in
theorem coe_sylowOfIsSylow2In {K P : Subgroup G} (h : IsSylow2In P K) :
    (sylowOfIsSylow2In h : Subgroup ↥K) = P.subgroupOf K := rfl

omit [Finite G] in
theorem natCard_sylow_eq {H : Type*} [Group H] [Finite H] (T : Sylow 2 H) :
    Nat.card T = 2 ^ (Nat.card (H ⧸ classicalInvolutionOddCore H)).factorization 2 := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore H)) :=
    CFSG.ComponentClassification.OddCore.odd_card H
  rw [Sylow.card_eq_multiplicity T,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore H),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

theorem natCard_isSylow2In_eq {K P : Subgroup G} (hP : IsSylow2In P K) :
    Nat.card P = 2 ^ (Nat.card (K ⧸ classicalInvolutionOddCore K)).factorization 2 := by
  rw [← natCard_sylow_eq (sylowOfIsSylow2In hP), coe_sylowOfIsSylow2In,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv]

theorem injective_mk_oddCore_of_isPGroup (K : Subgroup G) {S : Subgroup ↥K} (hS : IsPGroup 2 S) :
    Function.Injective ((QuotientGroup.mk' (classicalInvolutionOddCore K)).comp S.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxN : ((x : ↥K)) ∈ classicalInvolutionOddCore K := (QuotientGroup.eq_one_iff _).mp hx
  have hodd : Odd (Nat.card (classicalInvolutionOddCore K)) :=
    CFSG.ComponentClassification.OddCore.odd_card K
  obtain ⟨k, hk⟩ := hS.exists_orderOf_eq_pow x
  have h1 : (x : ↥K) = 1 := eq_one_of_mem_odd_of_orderOf_eq_two_pow hodd hxN (k := k) (by
    rw [Subgroup.orderOf_coe]
    exact hk)
  exact Subtype.ext h1

omit [Finite G] in
theorem not_isMulCommutative_of_sylowOf {K P : Subgroup G} (hP : IsSylow2In P K)
    (h : ∃ x ∈ (sylowOfIsSylow2In hP : Subgroup ↥K), ∃ y ∈ (sylowOfIsSylow2In hP : Subgroup ↥K),
      x * y ≠ y * x) : ¬ IsMulCommutative ↥P := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  intro hc
  have hx' : ((x : ↥K) : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
  have hy' : ((y : ↥K) : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
  have h1 := hc.is_comm.comm ⟨((x : ↥K) : G), hx'⟩ ⟨((y : ↥K) : G), hy'⟩
  have h2 : ((x : ↥K) : G) * ((y : ↥K) : G) = ((y : ↥K) : G) * ((x : ↥K) : G) :=
    congrArg Subtype.val h1
  exact hxy (Subtype.ext h2)

theorem exists_noncomm_of_quaternion {X : Type*} [Group X] {S : Subgroup X} {r : ℕ} (hr : 3 ≤ r)
    (φ : ↥S ≃* QuaternionGroup (2 ^ (r - 2))) : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x := by
  have h2 : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨((φ.symm (QuaternionGroup.a 1) : ↥S) : X), (φ.symm (QuaternionGroup.a 1)).2,
    ((φ.symm (QuaternionGroup.xa 0) : ↥S) : X), (φ.symm (QuaternionGroup.xa 0)).2, fun hc => ?_⟩
  have hc' : φ.symm (QuaternionGroup.a 1) * φ.symm (QuaternionGroup.xa 0) =
      φ.symm (QuaternionGroup.xa 0) * φ.symm (QuaternionGroup.a 1) := Subtype.ext hc
  rw [← map_mul, ← map_mul] at hc'
  exact Hat2A7R.quaternionGroup_a_one_xa_zero_not_comm h2 (φ.symm.injective hc')

end General

namespace IsClassicalMemberU

variable {t : MemberType} {G : Type} [Group G] [Finite G] {K J : Subgroup G} {z w : G}

theorem natCard_isSylow2In_eq_of_members (hK : IsClassicalMemberU t K z)
    (hJ : IsClassicalMemberU t J w) {P Q : Subgroup G} (hP : IsSylow2In P K)
    (hQ : IsSylow2In Q J) : Nat.card P = Nat.card Q := by
  rw [natCard_isSylow2In_eq hP, natCard_isSylow2In_eq hQ, hK.natCard_quot_eq hJ]

theorem exists_noncomm_sylow_of_solvable (h : IsClassicalMemberU t K z) (hs : t.IsSolvableType)
    (T : Sylow 2 ↥K) : ∃ x ∈ (T : Subgroup ↥K), ∃ y ∈ (T : Subgroup ↥K), x * y ≠ y * x := by
  obtain ⟨e⟩ := h.nonempty_equiv_sl2Three hs
  set S : Subgroup ↥K := (T : Subgroup ↥K) with hS
  have hS2 : IsPGroup 2 S := T.isPGroup'
  let ψ : ↥K →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore K))
  have hinj : Function.Injective (ψ.comp S.subtype) :=
    e.injective.comp (injective_mk_oddCore_of_isPGroup K hS2)
  have hcard : Nat.card (S.map ψ) = 8 := by
    have h1 : S.map ψ = (ψ.comp S.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    have h2 : Nat.card S = 2 ^ (Nat.card (↥K ⧸ classicalInvolutionOddCore K)).factorization 2 :=
      natCard_sylow_eq T
    rw [h2, Nat.card_congr e.toEquiv, natCard_sl2Three]
    have : (Nat.factorization 24) 2 = 3 := by decide +kernel
    rw [this]
    norm_num
  have hpg : IsPGroup 2 (S.map ψ) := hS2.map ψ
  let etop : (⊤ : Subgroup SL(2, ZMod 3)) ≃* SL(2, ZMod 3) := Subgroup.topEquiv
  have hq := Q3.Twin.eq_quatIn_of_card_eq etop le_top hpg hcard
  obtain ⟨a, b, ha, hb, hab⟩ := Q3.Twin.exists_noncomm_quatIn etop
  rw [← hq] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ⟨x, hx, y, hy, fun hxy => hab (by rw [← map_mul, ← map_mul, hxy])⟩

theorem exists_noncomm_sylow (hc : t.Cert) (h : IsClassicalMemberU t K z) (T : Sylow 2 ↥K) :
    ∃ x ∈ (T : Subgroup ↥K), ∃ y ∈ (T : Subgroup ↥K), x * y ≠ y * x := by
  by_cases hs : t.IsSolvableType
  · exact h.exists_noncomm_sylow_of_solvable hs T
  · cases t with
    | sl2 p f =>
      obtain ⟨hp, ⟨e⟩⟩ := h.witness
      have := hp
      have hodd := odd_natCard_galoisField_of_pos h.admissible.2.1 h.admissible.2.2
      have h3 : 3 ≤ p ^ f := three_le_pow_of_odd_prime h.admissible.1 h.admissible.2.1
        h.admissible.2.2
      have hns : p ^ f ≠ 3 := hs
      have h5 : 5 ≤ Nat.card (GaloisField p f) := by
        rw [natCard_galoisField_eq h.admissible.2.2]
        have hodd' : Odd (p ^ f) := by
          rw [← natCard_galoisField_eq h.admissible.2.2]
          exact hodd
        obtain ⟨m, hm⟩ := hodd'
        omega
      obtain ⟨r, hr, ⟨φ⟩⟩ := Disconnected.exists_quaternion_of_sl2 hodd h5 e T
      exact exists_noncomm_of_quaternion hr φ
    | twoA7 =>
      exact Hat2A7R.nonabelian_sylow_of_witness h.witness T

theorem not_isMulCommutative_sylow (hc : t.Cert) (h : IsClassicalMemberU t K z) {P : Subgroup G}
    (hP : IsSylow2In P K) : ¬ IsMulCommutative ↥P :=
  not_isMulCommutative_of_sylowOf hP (h.exists_noncomm_sylow hc (sylowOfIsSylow2In hP))

end IsClassicalMemberU

end CFSG.ClassicalInvolution.Uniform
