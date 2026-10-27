module

public import CFSG.GH74.GLS.Balance.SolvCompBasic
public import CFSG.GH74.GLS.Balance.SubnormalChain

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

namespace SolvComp

variable {X : Type} [Group X]

structure Pre (x : X) (V : Subgroup X) where
  E : SL23.Ext ↥V
  hVC : V ≤ centralizer ({x} : Set X)
  hsub : (V.subgroupOf (centralizer ({x} : Set X))).IsSubnormal
  hOV : pPrimeCoreOf 2 (centralizer ({x} : Set X)) ≤ V
  ker_iff : ∀ v : ↥V, E.π v = 1 ↔ (v : X) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X))
  Q_le : ∀ v : ↥V, E.π v ^ 4 = 1 →
    (v : X) ∈ (pPrimePCore 2 ↥(centralizer ({x} : Set X))).map (centralizer ({x} : Set X)).subtype
  P' : Subgroup ↥V
  P'_two : IsPGroup 2 P'
  P'_card : Nat.card P' = 8
  w' : ↥V
  w'_norm : w' ∈ normalizer (P' : Set ↥V)
  w'_three : ∃ k : ℕ, orderOf w' = 3 ^ k
  w'_ne : E.π w' ≠ 1
  w'_cube : E.π w' ^ 3 = 1

namespace Pre

variable {x : X} {V : Subgroup X} (A : Pre x V)

include A

@[expose] def P : Subgroup X := A.P'.map V.subtype

@[expose] def w : X := (A.w' : X)

theorem w_mem : A.w ∈ V := A.w'.2

theorem P_le : A.P ≤ V := Subgroup.map_subtype_le _

theorem P_two : IsPGroup 2 A.P := A.P'_two.map V.subtype

theorem P_card : Nat.card A.P = 8 := by
  rw [P, Subgroup.card_map_of_injective V.subtype_injective]
  exact A.P'_card

theorem P_sylow (T : Subgroup X) (hT : T ≤ V) (hT2 : IsPGroup 2 T) :
    Nat.card T ≤ Nat.card A.P := by
  rw [A.P_card]
  have hT' : IsPGroup 2 (T.subgroupOf V) := hT2.comap_of_injective V.subtype V.subtype_injective
  have : Nat.card (T.subgroupOf V) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  rw [← this]
  exact A.E.card_le hT'

theorem w_three : ∃ k : ℕ, orderOf A.w = 3 ^ k := by
  rw [w, Subgroup.orderOf_coe]
  exact A.w'_three

theorem w_norm : A.w ∈ normalizer (A.P : Set X) := mem_normalizer_map_subtype A.w'_norm

theorem w3 : ∀ a ∈ A.P, A.w ^ 3 * a = a * A.w ^ 3 := by
  rintro _ ⟨a', ha', rfl⟩
  have h := A.E.w3_comm A.P'_two A.w'_norm A.w'_cube ha'
  exact congrArg Subtype.val h

theorem P_le_R : A.P ≤ oPrimeResidualOf 2 V := by
  apply Subgroup.map_mono
  intro a ha
  obtain ⟨k, hk⟩ := A.P'_two ⟨a, ha⟩
  exact Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem R_le_pPrimePCore : oPrimeResidualOf 2 V ≤
    (pPrimePCore 2 ↥(centralizer ({x} : Set X))).map (centralizer ({x} : Set X)).subtype := by
  have h : oPrimeResidual 2 ↥V ≤
      ((pPrimePCore 2 ↥(centralizer ({x} : Set X))).map
        (centralizer ({x} : Set X)).subtype).comap V.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨j, hj⟩
    exact A.Q_le y (A.E.pow_four_of_two_pow hj)
  rintro _ ⟨y, hy, rfl⟩
  exact h hy

theorem central_mod {N : Subgroup X} (hVN : V ≤ normalizer (N : Set X))
    (hRN : ¬ oPrimeResidualOf 2 V ≤ N) :
    ∀ g ∈ N ⊓ V, ∀ v ∈ V, ⁅g, v⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X)) := by
  set M : Subgroup ↥V := N.comap V.subtype with hM
  have hMn : M.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : ↥V) : X) ∈ N
    have := (Subgroup.mem_normalizer_iff.mp (hVN g.2) (n : X)).mp hn
    simpa using this⟩
  have hsq : ∀ m ∈ M, A.E.π m ^ 2 = 1 := by
    intro m hm
    by_contra hne
    apply hRN
    have hle : oPrimeResidual 2 ↥V ≤ M := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro z ⟨j, hj⟩
      exact A.E.two_elt_mem_of_normal hm hne hj
    rintro _ ⟨y, hy, rfl⟩
    exact hle hy
  intro g hg v hv
  have hgM : (⟨g, hg.2⟩ : ↥V) ∈ M := hg.1
  have hk := A.E.comm_mem_ker_of_sq (hsq _ hgM) ⟨v, hv⟩
  exact (A.ker_iff _).mp hk

section FiniteSec

variable [Finite X]

theorem P_nonab : ∃ a ∈ A.P, ∃ b ∈ A.P, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := A.E.nonab A.P'_two A.P'_card
  exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, fun h => hab (Subtype.ext h)⟩

theorem P_comm : ⁅A.P, zpowers A.w⁆ = A.P := by
  have h := A.E.commutator_eq A.P'_two A.P'_card A.w'_norm A.w'_ne A.w'_cube
  have := congrArg (Subgroup.map V.subtype) h
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at this
  exact this

theorem R_gen (K : Subgroup X) (hRK : oPrimeResidualOf 2 V ≤ normalizer (K : Set X))
    (hPK : A.P ≤ K) : oPrimeResidualOf 2 V ≤ K := by
  have h : oPrimeResidual 2 ↥V ≤ K.comap V.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨j, hj⟩
    obtain ⟨a, ha, k, hk, hyak⟩ := A.E.exists_mul_of_two_elt A.P'_two A.P'_card hj
    have haK : (a : X) ∈ K := hPK ⟨a, ha, rfl⟩
    have hyR : (y : X) ∈ oPrimeResidualOf 2 V := ⟨y, Subgroup.subset_closure ⟨j, hj⟩, rfl⟩
    have hkN : (k : X) ∈ normalizer (K : Set X) := by
      have : (k : X) = (a : X)⁻¹ * (y : X) := by rw [hyak]; simp
      rw [this]
      exact mul_mem (inv_mem (Subgroup.le_normalizer haK)) (hRK hyR)
    refine SL23.mem_of_mul_odd (K := K) (j := j) haK hkN (congrArg Subtype.val hyak) ?_ ?_
    · rw [Subgroup.orderOf_coe]
      exact A.E.odd_orderOf_of_mem_ker hk
    · simpa using congrArg Subtype.val hj
  rintro _ ⟨y, hy, rfl⟩
  exact h hy

theorem gen (H : Subgroup X) (h : ∀ v ∈ V, Nat.Coprime (orderOf v) 2 → v ∈ H) : V ≤ H := by
  have hH : H.comap V.subtype = ⊤ := by
    refine A.E.gen3 (fun g hg => h g g.2 ?_) (fun g hg => h g g.2 ?_)
    · rw [Subgroup.orderOf_coe]
      exact (A.E.odd_orderOf_of_mem_ker hg).coprime_two_right
    · obtain ⟨k, hk⟩ := hg
      rw [Subgroup.orderOf_coe]
      have hdvd : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      exact (Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) hdvd).coprime_two_right
  intro v hv
  have : (⟨v, hv⟩ : ↥V) ∈ H.comap V.subtype := by rw [hH]; trivial
  exact this

theorem T_le (T : Subgroup X) (hTC : T ≤ centralizer ({x} : Set X)) (hT2 : IsPGroup 2 T)
    (hwT : A.w ∈ normalizer (T : Set X)) (hc : ⁅T, zpowers A.w⁆ = T) (hT0 : T ≠ ⊥) :
    T ≤ V ∧ Nat.card T = Nat.card A.P ∧ ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a := by
  have hTV : T ≤ V := le_of_commutator_eq_of_isSubnormal A.hVC A.hsub A.w_mem hTC hc
  set T' : Subgroup ↥V := T.subgroupOf V with hT'
  have hT'2 : IsPGroup 2 T' := hT2.comap_of_injective V.subtype V.subtype_injective
  have hwT' : A.w' ∈ normalizer (T' : Set ↥V) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact Subgroup.mem_normalizer_iff.mp hwT (h : X)
  have hcT' : ⁅T', zpowers A.w'⁆ = T' := by
    apply Subgroup.map_injective V.subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hTV]
    exact hc
  have hT'0 : T' ≠ ⊥ := by
    intro h
    apply hT0
    rw [← Subgroup.map_subgroupOf_eq_of_le hTV, ← hT', h, Subgroup.map_bot]
  obtain ⟨hcard, a, ha, b, hb, hab⟩ := A.E.T_analysis hT'2 hT'0 hwT' A.w'_ne A.w'_cube hcT'
  have hcT : Nat.card T = Nat.card T' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTV).toEquiv).symm
  refine ⟨hTV, ?_, (a : X), ha, (b : X), hb, fun h => hab (Subtype.ext h)⟩
  rw [hcT, hcard, A.P_card]

end FiniteSec

end Pre

end SolvComp

end CFSG.GH74.GLS.Balance
