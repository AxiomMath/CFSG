module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

@[expose] def OddCentre : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    Odd (Nat.card ↥(center ↥L))

@[expose] def CentreDvdThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    Nat.card ↥(center ↥L) ∣ 3

theorem oddCentre_of_centreDvdThree (h : CentreDvdThree) : OddCentre :=
  fun G _ _ L hS hL => Odd.of_dvd_nat (by decide) (h G L hS hL)

@[expose] def OutTwo : Prop :=
  ∀ (Q : Type) [Group Q], HRG23 Q → (innerAut Q).index = 2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure LFactsA (s : Setting3 G L) : Prop where
  card_A : Nat.card ↥s.fr.A = 32
  comm_A : ∀ a ∈ s.fr.A, ∀ b ∈ s.fr.A, ⁅a, b⁆ ∈ s.fr.Z
  sq_A : ∀ a ∈ s.fr.A, a ^ 2 ∈ s.fr.Z
  nonab_A : ∃ a ∈ s.fr.A, ∃ b ∈ s.fr.A, a * b ≠ b * a
  z_mem : s.fr.z ∈ s.fr.A
  z_order : orderOf s.fr.z = 2
  cen_A : cen s.fr.A = s.fr.Z
  cen_S : cen s.fr.S = s.fr.Z

end CFSG.OddStandard.HigherRank.YamadaG23
