module

public import CFSG.GH74.GLS.Balance.SolvCompPre
public import CFSG.GH74.GLS.Balance.SolvAPIDefs

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

namespace SolvComp

variable {X : Type} [Group X] [Finite X] {x : X} {V : Subgroup X} (A : Pre x V)

include A

namespace Pre

theorem abelian (hx : orderOf x = 2) {T : Subgroup X} (hT : IsPGroup 2 T)
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hwT : A.w ∈ normalizer (T : Set X))
    (hxT : x ∈ normalizer (T : Set X)) : ⁅T, zpowers A.w⁆ = ⊥ := by
  set C := centralizer ({x} : Set X) with hC
  set T₀ : Subgroup X := T ⊓ C with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT.to_le inf_le_left
  have hwC : A.w ∈ C := A.hVC A.w_mem
  have hwT₀ : A.w ∈ normalizer (T₀ : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hT1 := Subgroup.mem_normalizer_iff.mp hwT h
    constructor
    · rintro ⟨hhT, hhC⟩
      exact Subgroup.mem_inf.mpr ⟨hT1.mp hhT, mul_mem (mul_mem hwC hhC) (inv_mem hwC)⟩
    · rintro ⟨hhT, hhC⟩
      refine Subgroup.mem_inf.mpr ⟨hT1.mpr hhT, ?_⟩
      have e : h = A.w⁻¹ * (A.w * h * A.w⁻¹) * A.w := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hwC) hhC) hwC
  set T' : Subgroup X := ⁅T₀, zpowers A.w⁆ with hT'
  have hT'T₀ : T' ≤ T₀ := SL23.comm_le_of_le_normalizer (Subgroup.zpowers_le.mpr hwT₀)
  have hT'C : T' ≤ C := hT'T₀.trans inf_le_right
  have hT'2 : IsPGroup 2 T' := hT₀2.to_le hT'T₀
  have hwT' : A.w ∈ normalizer (T' : Set X) :=
    mem_normalizer_commutator hwT₀ (Subgroup.le_normalizer (Subgroup.mem_zpowers A.w))
  have hT'c : ⁅T', zpowers A.w⁆ = T' := commutator_commutator_eq_of_three hT₀2 A.w_three hwT₀
  have hT'bot : T' = ⊥ := by
    by_contra hne
    obtain ⟨-, -, a, ha, b, hb, hab'⟩ := A.T_le T' hT'C hT'2 hwT' hT'c hne
    exact hab' (hab a (hT'T₀ ha).1 b (hT'T₀ hb).1)
  have hwc0 : ∀ t ∈ T₀, A.w * t = t * A.w := by
    intro t ht
    have h1 : ⁅t, A.w⁆ ∈ T' := Subgroup.commutator_mem_commutator ht (Subgroup.mem_zpowers A.w)
    rw [hT'bot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hu : ¬ 2 ∣ orderOf A.w := by
    obtain ⟨k, hk⟩ := A.w_three
    rw [hk]
    intro h
    have : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hxw : x * A.w = A.w * x := (mem_centralizer_singleton_iff.mp hwC).symm
  have key := centralizes_of_centralizes_fixed hT (x := x) (u := A.w)
    ⟨1, by rw [hx, pow_one]⟩ hu hxw hxT hwT
    (fun t ht hxt => hwc0 t ⟨ht, mem_centralizer_singleton_iff.mpr hxt.symm⟩)
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr (fun t ht b hb => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc : Commute t A.w := (key t ht).symm
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hc.zpow_right n).eq

theorem dich {N : Subgroup X} (hN2 : IsPGroup 2 N) (hNC : N ≤ centralizer ({x} : Set X))
    (hCN : centralizer ({x} : Set X) ≤ normalizer (N : Set X)) :
    oPrimeResidualOf 2 V ≤ N ∨ V ≤ centralizer (N : Set X) := by
  by_cases hR : oPrimeResidualOf 2 V ≤ N
  · exact Or.inl hR
  refine Or.inr ?_
  have hVN : V ≤ normalizer (N : Set X) := A.hVC.trans hCN
  have hcm := A.central_mod hVN hR
  have hNO : ∀ z ∈ N, z ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X)) → z = 1 := by
    intro z hzN hzO
    obtain ⟨k, hk⟩ := SL23.exists_pow_eq_one_of_mem hN2 hzN
    exact eq_one_of_mem_pPrimeCoreOf_of_two_pow hzO hk
  have hH : (centralizer (N : Set X)).comap V.subtype = ⊤ := by
    refine A.E.gen3 ?_ ?_
    · intro g hg
      have hgO : (g : X) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X)) := (A.ker_iff g).mp hg
      show (g : X) ∈ centralizer (N : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hnC : n ∈ centralizer ({x} : Set X) := hNC hn
      have hgC : (g : X) ∈ centralizer ({x} : Set X) := A.hVC g.2
      have h1 : ⁅n, (g : X)⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X)) := by
        rw [commutatorElement_def]
        exact mul_mem (pPrimeCoreOf_conj_mem hnC hgO) (inv_mem hgO)
      have h2 : ⁅n, (g : X)⁆ ∈ N := SL23.comm_mem_of_mem_normalizer hn (hCN hgC)
      exact commutatorElement_eq_one_iff_mul_comm.mp (hNO _ h2 h1)
    · intro g hg
      obtain ⟨k, hk⟩ := hg
      have hv3 : ∃ j : ℕ, orderOf (g : X) = 3 ^ j := by
        rw [Subgroup.orderOf_coe]
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
        exact ⟨j, hj⟩
      have hvN : (g : X) ∈ normalizer (N : Set X) := hVN g.2
      set T : Subgroup X := ⁅N, zpowers (g : X)⁆ with hT
      have hTN : T ≤ N := SL23.comm_le_of_le_normalizer (Subgroup.zpowers_le.mpr hvN)
      have hTC : T ≤ centralizer ({x} : Set X) := hTN.trans hNC
      have hTT : ⁅T, zpowers (g : X)⁆ = T := commutator_commutator_eq_of_three hN2 hv3 hvN
      have hTV : T ≤ V := le_of_commutator_eq_of_isSubnormal A.hVC A.hsub g.2 hTC hTT
      have hle : ⁅T, zpowers (g : X)⁆ ≤ ⊥ := by
        refine Subgroup.commutator_le.mpr (fun t ht b hb => ?_)
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have h1 : ⁅t, (g : X)⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X)) :=
          hcm t ⟨hTN ht, hTV ht⟩ (g : X) g.2
        have h2 : ⁅t, (g : X)⁆ ∈ N := SL23.comm_mem_of_mem_normalizer (hTN ht) hvN
        have h3 : Commute t (g : X) := commutatorElement_eq_one_iff_mul_comm.mp (hNO _ h2 h1)
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (h3.zpow_right n).eq
      rw [hTT] at hle
      show (g : X) ∈ centralizer (N : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 : ⁅n, (g : X)⁆ ∈ T := Subgroup.commutator_mem_commutator hn (Subgroup.mem_zpowers _)
      have h2 := hle h1
      rw [Subgroup.mem_bot] at h2
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
  intro v hv
  have : (⟨v, hv⟩ : ↥V) ∈ (centralizer (N : Set X)).comap V.subtype := by rw [hH]; trivial
  exact this

end Pre

end SolvComp

theorem solvAPI_of_isSolvTwoCompSL23In {X : Type} [Group X] [Finite X] {x : X} {V : Subgroup X}
    (hV : IsSolvTwoCompSL23In (centralizer ({x} : Set X)) V) : Nonempty (SolvAPI x V) := by
  obtain ⟨π, hsurj, hodd, hker, hQ⟩ := SolvComp.exists_ext hV
  let E : SL23.Ext ↥V := ⟨π, hsurj, hodd⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥V) := inferInstance
  obtain ⟨w, hwN, hw3, hw1, hwc⟩ := E.exists_w S
  let A : SolvComp.Pre x V :=
    { E := E
      hVC := hV.1
      hsub := SolvComp.isSubnormal_of_solv hV
      hOV := SolvComp.pPrimeCoreOf_le_of_solv hV
      ker_iff := hker
      Q_le := hQ
      P' := S
      P'_two := S.isPGroup'
      P'_card := E.card_sylow S
      w' := w
      w'_norm := hwN
      w'_three := hw3
      w'_ne := hw1
      w'_cube := hwc }
  exact ⟨{ P := A.P
           w := A.w
           hVC := A.hVC
           V_subnormal := A.hsub
           O_le_V := A.hOV
           gen := A.gen
           P_le := A.P_le
           P_two := A.P_two
           P_sylow := A.P_sylow
           P_nonab := A.P_nonab
           w_mem := A.w_mem
           w_three := A.w_three
           w_norm := A.w_norm
           P_comm := A.P_comm
           w3 := A.w3
           P_le_R := A.P_le_R
           R_gen := A.R_gen
           T_le := A.T_le
           abelian := fun hx T hT hab hwT hxT => A.abelian hx hT hab hwT hxT
           dich := fun N hN2 hNC hCN => A.dich hN2 hNC hCN
           central_mod := fun N hVN hRN => A.central_mod hVN hRN
           R_le_pPrimePCore := A.R_le_pPrimePCore }⟩

end CFSG.GH74.GLS.Balance
