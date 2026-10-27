module

public import CFSG.Quasithin.H13.A6S1372L76N3a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76W

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1376NThreeC3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    2 ^ 5 < Nat.card ↥(pCoreOf 2 (L ⊔ T)) →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H → S.L1 ≤ K →
      ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1

@[expose] def Lem1376NThreeBlock_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    Nat.card ↥(pCoreOf 2 (L ⊔ T)) ≤ 2 ^ 5 →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H → S.L1 ≤ K →
      ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem not_isHatA6_of_natSL32_F4 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    ¬ IsHatA6 L := by
  intro hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := S.two_le_pRank_L1_of_hat hhat
  obtain ⟨F, _, _, hF, hR⟩ := id hSL
  obtain ⟨E⟩ := S.exists_quotEquiv_of_realizes_F4 hNS h13315 h1356two hH hK
    (FFModel.nat_faithful _) hR
  have hker : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥K) := by
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥K)).exists_card_eq
    rw [hj]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have : Finite (GL (Fin 3) F) :=
    Finite.of_injective (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) Units.val_injective
  have : Finite (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam := by
    show Finite ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)
    infer_instance
  have hK3 : CFSG.Open.pRank 3 K ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) hker,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) E]
    rw [pow_one] at hF
    exact A6L76N3.pRank_three_le_one hF _
  have h3 : CFSG.Open.pRank 3 S.L1 ≤ CFSG.Open.pRank 3 K :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hL1K
  omega

end Setting4

theorem lem1376NThree_of_F4 (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (hC : Lem1376NThreeC3_F4) (hB : Lem1376NThreeBlock_F4) :
    Lem1376NThree_F4 := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK hL1K hSL
  have hhat := S.not_isHatA6_of_natSL32_F4 hNS h13315 h1356two hH hK hL1K hSL
  by_cases hQ : 2 ^ 5 < Nat.card ↥(pCoreOf 2 (L ⊔ T))
  · exact hC G T L V S hNS hNU hhat hQ H hH hab K hK hL1K hSL
  · exact hB G T L V S hNS hNU hhat (not_lt.1 hQ) H hH hab K hK hL1K hSL

end CFSG.Quasithin.H13.A6
