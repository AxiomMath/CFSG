module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Crit
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L34
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.PSL3Four (S_le_R nonempty_equiv_of_stated)
local notation "S42" => CFSG.ComponentClassification.PSL3Four.S

theorem ivk93m12_factorization_20160 : (20160 : ℕ).factorization 2 = 6 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem ivk93m12_l34 :
    Ivk93M12Empty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro J _ _ hJ y D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hJcard : Nat.card J = 20160 := by
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hst
    have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF4,
      show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  obtain ⟨T⟩ : Nonempty (Sylow 2 J) := inferInstance
  have hT : Nat.card ↥(T : Subgroup J) = 64 := by
    rw [Sylow.card_eq_multiplicity T, hJcard, ivk93m12_factorization_20160]
    norm_num
  have h64 : 64 ∣ Nat.card ↥(centralizer ({y} : Set J)) := hT ▸ D.card_sylow_dvd_cent T
  obtain ⟨θ⟩ := nonempty_equiv_of_stated J hst
  have hcard := GHInv.card_centralizer_eq_centralizerIn S42 θ y
  have hx2 : orderOf ((θ y : ↥S42) : Equiv.Perm (Fin 42)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact D.orderOf_eq_two
  have hxR := S_le_R (θ y).2
  have key : ∀ N : ℕ, Nat.card ↥(S42 ⊓ centralizer ({((θ y : ↥S42) : Equiv.Perm (Fin 42))} :
      Set (Equiv.Perm (Fin 42)))) = N → Nat.card ↥(centralizer ({y} : Set J)) = N :=
    fun N h => hcard.trans h
  have hC : Nat.card ↥(centralizer ({y} : Set J)) = 64 := by
    rcases l34_inv_cases hxR hx2 with ⟨c, hc', hce, hc⟩ | ⟨c, hc', hce, hc⟩ |
        ⟨c, hc', hce, hc⟩ | ⟨c, hc', hce, hc⟩
    · exact key 64 hc
    · have h := key 168 hc
      rw [h] at h64
      omega
    · have h := key 60 hc
      rw [h] at h64
      omega
    · have h := key 72 hc
      rw [h] at h64
      omega
  refine D.false_of_cent_card_eq hC ?_
  intro n m hn hm
  obtain ⟨k, rfl⟩ := hm
  rcases hn with rfl | rfl | rfl | rfl <;> omega

end CFSG.GH74.GLS.IVK.Proofs2
