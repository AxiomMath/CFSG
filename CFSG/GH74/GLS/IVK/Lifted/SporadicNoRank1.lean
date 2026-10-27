module

public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Main CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.Uniqueness.SU.SU13.TA

theorem sporadic_no_rank1 : SporadicNoRank1 := by
  intro G _ _ z S n _ hn hsp K hK
  obtain ⟨hKC, K', hK'c, -, hKmap, -⟩ := hK
  have hcov := hsp.cover
  have hq : CFSG.IsQuasisimple (CentralizerBar z) := hcov.1
  have hK'top : K' = ⊤ := by
    rcases TwoThin.eq_top_or_le_center_of_subnormal hq hK'c.2 with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hK'c.1.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hc : (b' : CentralizerBar z) * a' = a' * b' :=
        Subgroup.mem_center_iff.mp (h a'.2) (b' : CentralizerBar z)
      have hc' : a' * b' = b' * a' := Subtype.ext hc.symm
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc']
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(Cen z)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hrank : CFSG.pRank 2 (CentralizerBar z) = CFSG.pRank 2 ↥(K.subgroupOf (Cen z)) :=
    pRank_two_quot_eq_of_map_eq_top _ hodd _ (hKmap.trans hK'top)
  have hrankK : CFSG.pRank 2 ↥(K.subgroupOf (Cen z)) = CFSG.pRank 2 ↥K :=
    pRank_two_congr (Subgroup.subgroupOfEquivOfLe hKC)
  have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt (CentralizerBar z) n :=
    ⟨hq, (inferInstance : Finite (CentralizerBar z)), hcov.2.1, hcov.2.2⟩
  obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hT
  have h4 : 4 ≤ CFSG.pRank 2 ↥K := by
    rw [← hrankK, ← hrank]
    exact four_le_pRank_of_twoCover hπ hn
  intro h1
  omega

end CFSG.GH74.GLS.IVK.Lifted
