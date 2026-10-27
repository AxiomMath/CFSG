module

public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2081
public import Certificates.Certificate14985
public import Certificates.Certificate2102
public import Certificates.Certificate3166
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2100
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate14980
public import Certificates.Certificate16041
public import Certificates.Certificate13607
public import Certificates.Certificate13608
public import Certificates.Certificate13609
import CFSG.RankThree.PartOne.KS.HNFiveLocal
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFiveOrders
import CFSG.RankThree.PartOne.Q1327S.HNCenter

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint
open CFSG.RankThree.PartOne.KS.HNFive CFSG.Monster.B.Pinned
open CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank
open scoped Pointwise

variable {G : Type*} [Group G]

private theorem card_center_sup {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G}
    {M : Matrix (Fin 4) (Fin 4) (ZMod 5)} {XU : GL (Fin 4) (ZMod 5)}
    {cx : Fin 4 → ℕ} {BU : Fin k → GL (Fin 4) (ZMod 5)} {cr : Fin k → Fin 4 → ℕ}
    (hR : Rel q z x r M XU cx BU cr) [Finite G] (hX : XU ≠ 1) :
    Nat.card (Subgroup.center ↥(QG q ⊔ Subgroup.zpowers x)) = 5 := by
  set P := QG q ⊔ Subgroup.zpowers x
  have hzP : z ∈ P := Subgroup.mem_sup_left hR.z_mem
  have hz : (⟨z, hzP⟩ : P) ∈ Subgroup.center P :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hR.H_commute_z (Rel.P_le_H y.2)).eq
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.card_map_of_injective P.subtype_injective]
    refine CFSG.RankThree.PartOne.Q1327S.card_central_le hR hX (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨y, hy, rfl⟩ w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨w, hw⟩).symm
  · calc 5 = Nat.card (Subgroup.zpowers (⟨z, hzP⟩ : P)) := by
          rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hR.orderOf_z]
      _ ≤ _ := Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hz)

section RelHN


private theorem exists_rel_HN {L : Type} [Group L]
    (e : L ≃* NativeSporadic.Carrier .HN) :
    ∃ (q : Fin 4 → L) (z x : L) (r : Fin 3 → L),
      Rel q z x r Mm XU cx BU cr := by
  let e' : L ≃* J := (e : L ≃* NativeSporadic.HN).trans HNTwoRank.hnEquivJ
  refine ⟨fun j => e'.symm ⟨Rg (iQ j), Rg_mem _⟩, e'.symm ⟨Rg iZ, Rg_mem _⟩,
    e'.symm ⟨Rg iX, Rg_mem _⟩, fun j => e'.symm ⟨Rg (iR j), Rg_mem _⟩, ?_⟩
  apply Rel.of_injective (J.subtype.comp (e' : L →* J)) (Subtype.val_injective.comp e'.injective)
  simpa using hnFive_rel

end RelHN

section ExponentHN


theorem exists_exponent_five_HN {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .HN) :
    ∃ F : Subgroup L, Nat.card F = 5 ^ 5 ∧ ∀ g ∈ F, g ^ 5 = 1 := by
  obtain ⟨q, z, x, r, hR⟩ := exists_rel_HN e
  exact ⟨QG q, hR.card_Q, fun g hg => hR.pow_five_of_mem hg⟩

end ExponentHN

section CenterSylowHN


theorem card_center_sylow_HN {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .HN) :
    ∀ Q : Sylow 5 L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = 5 := by
  obtain ⟨q, z, x, r, hR⟩ := exists_rel_HN e
  have h5L : (Nat.card L).factorization 5 = 6 := by
    rw [Nat.card_congr (e : L ≃* NativeSporadic.HN).toEquiv]
    exact CFSG.RankThree.PartOne.KS.factorization_card_HN_five
  intro Q
  obtain ⟨S, hS⟩ := hR.P_sylow XU_ne_one h5L
  let φ := Sylow.equiv S Q
  rw [← Subgroup.map_center_eq φ, Subgroup.card_map_of_injective φ.injective, hS]
  exact card_center_sup hR XU_ne_one

end CenterSylowHN

section FiveCentral


theorem card_centralizer_dvd_HN_of_five_central {L : Type} [Group L]
    (e : L ≃* NativeSporadic.Carrier .HN) {z : L} (hz : orderOf z = 5)
    (h56 : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 14 * 3 * 5 ^ 6 := by
  have e0 : L ≃* NativeSporadic.HN := e
  have e' : L ≃* JH := e0.trans CFSG.Sporadic.HNSchreier.hnEquivJ
  let w : JH := e' z
  have hw : orderOf w = 5 := by
    change orderOf (e' z) = 5
    rw [MulEquiv.orderOf_eq, hz]
  have hcard0 : Nat.card (Subgroup.centralizer ({e' z} : Set JH)) =
      Nat.card (Subgroup.centralizer ({z} : Set L)) :=
    @CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_mulEquiv
      L _ ↥JH inferInstance e' z
  have hcard : Nat.card (Subgroup.centralizer ({w} : Set JH)) =
      Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    simpa only [w] using hcard0
  have h56' : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({w} : Set JH)) := by
    rw [hcard]; exact h56
  by_cases hconj : ∃ k : ℕ, IsConj w (fJ ^ k)
  · obtain ⟨k, hk⟩ := hconj
    obtain ⟨c, hc⟩ := isConj_iff.1 hk
    have hk5 : orderOf (fJ ^ k) = 5 := by
      rw [← hc, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.orderOf_conj_eq, hw]
    have hcent : Subgroup.centralizer ({fJ ^ k} : Set JH) =
        Subgroup.centralizer ({fJ} : Set JH) :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq
        (by rw [hk5, CFSG.Sporadic.HNOddCore.orderOf_fJ])
        (by rw [CFSG.Sporadic.HNOddCore.orderOf_fJ]; norm_num)
    have hwk : Nat.card (Subgroup.centralizer ({w} : Set JH)) =
        Nat.card (Subgroup.centralizer ({fJ ^ k} : Set JH)) := by
      rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj c w,
        hc]
    have h630 : Nat.card (Subgroup.centralizer ({w} : Set JH)) = 630000 := by
      rw [hwk, hcent]
      exact (CFSG.Sporadic.HNOddCore.ctuc_hn_five_centralizer_perfect_factor).2.2.2.2.1
    have hdiv : 5 ^ 6 ∣ (630000 : ℕ) := by rw [← h630]; exact h56'
    norm_num at hdiv
  · push Not at hconj
    have hdvd : Nat.card (Subgroup.centralizer ({w} : Set JH)) ∣
        2 ^ 14 * 3 * 5 ^ 6 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.hnFiveOrders_holds w hw hconj
    rwa [hcard] at hdvd

end FiveCentral

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
