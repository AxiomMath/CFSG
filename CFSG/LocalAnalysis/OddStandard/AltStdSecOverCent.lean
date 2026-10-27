module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapSetting

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem card_centralizer_eq_two_mul_factorial (h : Setting G L n) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q)
    (hu2 : u ^ 2 = 1) (e : L ≃* alternatingGroup (Fin n)) :
    Nat.card (centralizer ({z} : Set G)) = 2 * n.factorial := by
  have hcent := centralizer_eq_swapComplement h d hQ2 hu huL
  have hdisj := zpowers_inf_swapComplement h d hQ2 hu huL hu2
  have hbij := rhoSwap_bijective h d hQ2 hu huL hu2 e
  have hSle : L ⊔ zpowers u ≤ centralizer ({z} : Set G) := by
    rw [hcent]
    exact le_sup_right
  have hnorm : L ⊔ zpowers u ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    refine le_trans ?_
      (Subgroup.centralizer_le_normalizer (s := ((zpowers z : Subgroup G) : Set G)))
    intro s hs
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have hcomm : Commute z s := (mem_centralizer_singleton_iff.1 (hSle hs)).symm
    exact (Commute.zpow_left hcomm k).eq
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (zpowers z) (L ⊔ zpowers u) hnorm (disjoint_iff.2 hdisj)
  have hS : Nat.card (L ⊔ zpowers u : Subgroup G) = n.factorial := by
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
  rw [hcent, hcard, hS, Nat.card_zpowers, d.order]

end CFSG.OddStandard.AltStdSec
