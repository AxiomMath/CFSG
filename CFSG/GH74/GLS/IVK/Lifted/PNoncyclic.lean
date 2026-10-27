module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleNotTwoGroupQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6

theorem p_noncyclic : P_noncyclic := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ z S K₁ K₂ h K hK hcyc
  have hKc : K = K₁ ∨ K = K₂ := by simpa using hK
  have hKC := h.comp_isPCompIn hKc
  have hQs := TwoThin.isQuasisimple_hat hKC
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 h.sylow
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hKC.1 hsub
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1 hSK
  have hPcyc : IsCyclic (P : Subgroup ↥K) := by
    have e := Subgroup.equivMapOfInjective (P : Subgroup ↥K) K.subtype K.subtype_injective
    rw [hP] at e
    exact (e.isCyclic).2 hcyc
  let Pbar : Sylow 2 (Hat K) := P.mapSurjective (hatMk_surjective K)
  have hPbarcyc : IsCyclic (Pbar : Subgroup (Hat K)) := by
    have : (Pbar : Subgroup (Hat K)) = (P : Subgroup ↥K).map (hatMk K) :=
      Sylow.coe_mapSurjective (hatMk_surjective K) P
    rw [this]
    exact isCyclic_of_surjective ((hatMk K).subgroupMap (P : Subgroup ↥K))
      ((hatMk K).subgroupMap_surjective (P : Subgroup ↥K))
  obtain ⟨-, -, -, ⟨-, -, hidx, -⟩, -⟩ := cyclic_sylow_normal_odd_complement Pbar hPbarcyc
  have hgw : CFSG.GorensteinWalter.IsQuasisimple (Hat K) := by
    obtain ⟨hperf, hsimple, -⟩ := hQs
    have hnt : Nontrivial (Hat K) := by
      have : Nontrivial (Hat K ⧸ Subgroup.center (Hat K)) := hsimple.toNontrivial
      exact (QuotientGroup.mk_surjective (s := Subgroup.center (Hat K))).nontrivial
    exact ⟨hnt, (Group.isPerfect_def).1 hperf, hsimple⟩
  apply CFSG.GorensteinWalter.quasisimple_not_quotient_isTwoGroup hgw
  obtain ⟨k, hk⟩ := Pbar.isPGroup'.exists_card_eq
  apply IsPGroup.of_card (n := k)
  show (pPrimeCore 2 (Hat K)).index = 2 ^ k
  rw [hidx]
  exact hk

end CFSG.GH74.GLS.IVK.Lifted
