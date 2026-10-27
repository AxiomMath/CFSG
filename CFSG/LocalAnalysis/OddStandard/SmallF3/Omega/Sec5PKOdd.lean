module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Pk

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}

theorem sec5pk_oddCoreIn_cent_le (hD : Asc82FactQCentOrd6) (h : Sec5Ctx G t L S z)
    {K₁ K₂ : Subgroup G} (hk : Sec510Pk G t L S z K₁ K₂) :
    oddCoreIn (L ⊓ centralizer ({z} : Set G)) ≤ oddCoreIn L := by
  let X : Subgroup G := L ⊓ centralizer ({z} : Set G)
  let U : Subgroup G := oddCoreIn X
  have hQ₁X : twoCoreIn K₁ ≤ twoCoreIn X :=
    sec5pk_twoCoreIn_le_of_subnormal hk.pocket₁.2.1 hk.pocket₁.2.2.1
  have hQ₂X : twoCoreIn K₂ ≤ twoCoreIn X :=
    sec5pk_twoCoreIn_le_of_subnormal hk.pocket₂.2.1 hk.pocket₂.2.2.1
  have hcomm := sec5pk_comm_oddCoreIn_twoCoreIn X
  have hQ₁c : twoCoreIn K₁ ≤ centralizer (U : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcomm u hu q (hQ₁X hq)
  have hQ₂c : twoCoreIn K₂ ≤ centralizer (U : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcomm u hu q (hQ₂X hq)
  have hUcent : U ≤ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le hQ₁c hQ₂c)
  have hUX : U ≤ X := (oddCoreIn_normal X).1
  have hUL : U ≤ L := hUX.trans inf_le_left
  have hUnorm : U ≤ normalizer (L : Set G) := hUL.trans (Subgroup.le_normalizer (H := L))
  have hdvd : (centralizer (L : Set G)).relIndex U ∣ 8 :=
    (hD G L z h.toSec5Setting.isOm6Z2 h.pocket (twoCoreIn K₁) (twoCoreIn K₂)
      hk.q.le₁ hk.q.le₂ hk.q.iso₁ hk.q.iso₂ hk.q.comm hk.q.card hk.q.center
      hk.q.not_central U hUnorm hUcent).1
  have hrel : (centralizer (L : Set G)).relIndex U = 1 := by
    have hodd : Odd ((centralizer (L : Set G)).relIndex U) :=
      (odd_card_oddCoreIn X).of_dvd_nat
        (Subgroup.relIndex_dvd_card (centralizer (L : Set G)) U)
    have hdvd' : (centralizer (L : Set G)).relIndex U ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact hdvd
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hk0 : k = 0 := by
      by_contra hkne
      have hodd' : Odd (2 ^ k) := by rw [← hk']; exact hodd
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
      rw [pow_succ] at hodd'
      exact (Nat.not_even_iff_odd.mpr hodd') ⟨2 ^ j, by ring⟩
    rw [hk', hk0]
    norm_num
  have hUcentL : U ≤ centralizer (L : Set G) := Subgroup.relIndex_eq_one.mp hrel
  have hN : (U.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUL]
    intro u l hu hl
    have hc : l * u = u * l := (Subgroup.mem_centralizer_iff.mp (hUcentL hu)) l hl
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hu
  exact le_oddCoreIn_of_normal hUL hN (odd_card_oddCoreIn X)

theorem sec5pk_oddCoreIn_pocket_le (hD : Asc82FactQCentOrd6) (h : Sec5Ctx G t L S z)
    {K₁ K₂ K : Subgroup G} (hk : Sec510Pk G t L S z K₁ K₂) (hK : K = K₁ ∨ K = K₂) :
    oddCoreIn K ≤ oddCoreIn L := by
  rcases hK with rfl | rfl
  · exact (sec5pk_oddCoreIn_le_of_subnormal hk.pocket₁.2.1 hk.pocket₁.2.2.1).trans
      (sec5pk_oddCoreIn_cent_le hD h hk)
  · exact (sec5pk_oddCoreIn_le_of_subnormal hk.pocket₂.2.1 hk.pocket₂.2.2.1).trans
      (sec5pk_oddCoreIn_cent_le hD h hk)

end CFSG.OddStandard.SmallF3.Omega
