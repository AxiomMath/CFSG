module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.NT44.RigidCenterInclusion
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec5

theorem two_pow_dvd_card_sylow_zStar_kz_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {J W : Subgroup G} {n : ℕ}
    (hJ : J ∈ RigidSet fullQ x)
    (hcenter : 2 ^ n ∣ Nat.card (Subgroup.center fullQ))
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ x))) :
    2 ^ n ∣ Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZK : zStar J ≤ J := fun _ h => (Subgroup.mem_inf.mp h).1
  have hcenter' : 2 ^ n ∣ Nat.card (Subgroup.center (HatT J)) := by
    obtain ⟨e⟩ := hJ.2
    have hcard : Nat.card (Subgroup.center (HatT J)) =
        Nat.card (Subgroup.center fullQ) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rwa [hcard]
  have : Finite (HatT J) :=
    Finite.of_surjective (hatMk J) (hatMk_surjective J)
  have hZeq : (zStar J).subgroupOf J =
      (Subgroup.center (HatT J)).comap (hatMk J) := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center k
  have hcardZ : Nat.card (zStar J) =
      Nat.card (hatMk J).ker * Nat.card (Subgroup.center (HatT J)) := by
    calc
      Nat.card (zStar J) = Nat.card ((zStar J).subgroupOf J) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv).symm
      _ = Nat.card ((Subgroup.center (HatT J)).comap (hatMk J)) := by rw [hZeq]
      _ = Nat.card (hatMk J).ker * Nat.card (Subgroup.center (HatT J)) :=
        CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (hatMk J)
          (hatMk_surjective J) (Subgroup.center (HatT J))
  have hdivZ : 2 ^ n ∣ Nat.card (zStar J) := by
    rw [hcardZ]
    exact dvd_mul_of_dvd_right hcenter' _
  have hdivP : 2 ^ n ∣ Nat.card (zStar (Kz fullQ x)) :=
    hdivZ.trans (Subgroup.card_dvd_of_le (zStar_le_zStar_kz_of_mem_rigidSet hJ))
  obtain ⟨Q, hQ⟩ := hW.exists_sylow_eq_subgroupOf
  have hcardQ : 2 ^ n ∣ Nat.card Q :=
    Q.pow_dvd_card_of_pow_dvd_card (n := n) hdivP
  have hQcard : Nat.card Q = Nat.card W := by
    have h1 : Nat.card Q = Nat.card (W.subgroupOf (zStar (Kz fullQ x))) := by
      rw [hQ]
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW.le).toEquiv]
  rwa [hQcard] at hcardQ

end CFSG.GH74.GLS.NT44

end
