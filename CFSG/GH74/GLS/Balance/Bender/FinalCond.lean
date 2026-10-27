module

public import CFSG.GH74.GLS.Balance.Bender.L52
public import CFSG.GH74.GLS.Balance.Bender.AuxCoprime
public import CFSG.GH74.GLS.Balance.Bender.AuxSimple
public import CFSG.GH74.GLS.Balance.Bender.L53
public import CFSG.GH74.GLS.Balance.Bender.L54
public import CFSG.GH74.GLS.Balance.Bender.L55
public import CFSG.GH74.GLS.Balance.Bender.L56
public import CFSG.GH74.GLS.Balance.Bender.T59
public import CFSG.GH74.GLS.Balance.Bender.Main511

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

theorem benderBalance_of (h52i : BenderL52i 2) (h56 : BenderL56 2) (h511 : BenderT511 2) :
    BenderBalance := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A _ _ Z N x hx hxZ hNZ hNn hNp hZ
  set P : Subgroup A := Subgroup.zpowers x with hP
  have hP2 : IsPGroup 2 ↥P :=
    IsPGroup.of_card (n := 1) (by rw [hP, Nat.card_zpowers, hx]; norm_num)
  have hPn : P ≤ normalizer (Z : Set A) := (Subgroup.zpowers_le).2 hxZ
  have hcentP : centralizer (P : Set A) = centralizer ({x} : Set A) := by
    rw [hP, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  set C' : Subgroup A := centralizer ({x} : Set A) ⊓ Z with hC'
  have hC'e : C' = Z ⊓ centralizer (P : Set A) := by
    rw [hC', hcentP, inf_comm]
  set W : Subgroup A := pPrimeCoreOf 2 C' with hW
  have hWC' : W ≤ C' := Subgroup.map_subtype_le _
  have hWn : (W.subgroupOf C').Normal := by
    have e : W.subgroupOf C' = pPrimeCore 2 ↥C' :=
      Subgroup.comap_map_eq_self_of_injective C'.subtype_injective _
    rw [e]
    exact pPrimeCore_normal
  have hWp : IsPStar 2 ↥W := by
    refine h52i ↥W ?_
    have h1 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥C')) := pPrimeCore_coprime_card
    have h2 : Nat.card ((pPrimeCore 2 ↥C').map C'.subtype) = Nat.card (pPrimeCore 2 ↥C') :=
      Subgroup.card_map_of_injective C'.subtype_injective
    exact h2.symm ▸ h1
  have hWO : W ≤ OpStar 2 C' := le_opStar hWC' hWn hWp
  have hN : N ≤ OpStar 2 Z := le_opStar hNZ hNn hNp
  have hZle : Z ≤ OpStar 2 Z := by
    refine hZ.trans (sup_le hN (hWO.trans ?_))
    rw [hC'e]
    exact h511 A Z P hP2 hPn
  have hZeq : OpStar 2 Z = Z := le_antisymm (opStar_le 2 Z) hZle
  have h := isPStar_opStar h56 Z
  rwa [hZeq] at h

theorem benderT511_of_q42iii (p : ℕ) [Fact p.Prime] (hq42 : BenderQ42iii p) : BenderT511 p :=
  have h52i : BenderL52i p := bender_l52i p
  have h52ii : BenderL52ii p := bender_l52ii p
  have h52iii : BenderL52iii p := bender_l52iii p
  have h52iv : BenderL52iv p := bender_l52iv p
  have h53 : BenderL53 p := bender_l53 h52i h52ii h52iii hq42
  have h54 : BenderL54 p := bender_l54 h53
  have h55 : BenderL55 p := bender_l55 h52ii h52iv h54 hq42 bender_q43iii bender_q326
  have h56 : BenderL56 p := bender_l56 h55
  have h59 : BenderT59 p := bender_t59 h52iii h53 h56
  bender_t511 h52i h52ii h53 h54 h55 h56 h59

theorem benderBalance_of_q42iii (hq42 : BenderQ42iii 2) : BenderBalance :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  benderBalance_of (bender_l52i 2)
    (bender_l56 (bender_l55 (bender_l52ii 2) (bender_l52iv 2)
      (bender_l54 (bender_l53 (bender_l52i 2) (bender_l52ii 2) (bender_l52iii 2) hq42))
      hq42 bender_q43iii bender_q326))
    (benderT511_of_q42iii 2 hq42)

end CFSG.GH74.GLS.Balance
