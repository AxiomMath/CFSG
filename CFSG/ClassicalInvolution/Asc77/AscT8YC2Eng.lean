module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabHub
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.StronglyEmbedded.UniqueCosetBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem alphaOf_eq_bot_of_frattiniE [IsSimpleGroup G] {K : Subgroup G} {z t : G}
    (hz : IsUniqueInvolution K z)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    (hedge : ∀ {M : Subgroup G}, M ∈ omegaNbr Ω K → ∀ {s : G}, IsUniqueInvolution M s →
      Subgroup.centralizer ({z * s} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    (htop : T8.H274 Ω K z = ⊤)
    (hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G))))) :
    alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have hH : T8.H274 Ω K z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
      hedge hM hs')
  rw [htop, top_le_iff] at hH
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end T8YY

end CFSG.ClassicalInvolution.Asc77
