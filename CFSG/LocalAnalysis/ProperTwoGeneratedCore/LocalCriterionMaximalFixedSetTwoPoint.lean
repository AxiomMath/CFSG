module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetSelection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetTripleTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetCounting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetDoubleTransitivity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem subgroup_sylow_containing_ambient_sylow_is_ambient
    (p : ℕ) (B : Subgroup G) (Q : Sylow p B) (R : Sylow p G)
    (hRQ : (R : Subgroup G) ≤ (Q : Subgroup B).map B.subtype) :
    ∃ S : Sylow p G, (S : Subgroup G) = (Q : Subgroup B).map B.subtype := by
  exact ⟨R, (R.is_maximal' (Q.isPGroup'.map B.subtype) hRQ).symm⟩

theorem no_large_pair_sylow_of_two_point_ambient_sylows
    {H P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hPfixed : Nat.card (pointFixedSet H P) = 2)
    (hambient : ∀ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) = 2)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (Q : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)) :
    Nat.card (pointFixedSet H
    ((Q : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).subtype)) ≤ 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let B := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let QG := (Q : Subgroup B).map B.subtype
  by_contra hlarge
  change ¬ Nat.card (pointFixedSet H QG) ≤ 2 at hlarge
  have hQp : IsPGroup p QG := Q.isPGroup'.map B.subtype
  obtain ⟨r, hr, _, _, hrQ, hrmotion⟩ := pair_specified_sylow_flip
    h T hzT hzcenter a b hab p hp Q
  obtain ⟨M, _, hM, hMfixed, hMmax, t, ht, htM, htmotion⟩ :=
    exists_maximal_full_motion H QG z p hQp (by omega) r hr hrQ hrmotion
  obtain ⟨gamma, hgammaM, htgamma⟩ := local_involution_point_maximal_prime_fixed_point
    H z h T hzT hzcenter p hp M hM t ht htM hMfixed htmotion hMmax
  let C := rightCosetStabilizer H gamma
  have hMC : M ≤ C := (mem_pointFixedSet_iff H M gamma).mp hgammaM
  have hMi : IsPGroup p (M.subgroupOf C) := hM.of_injective
    (Subgroup.subgroupOfEquivOfLe hMC).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hMC).injective
  obtain ⟨R, hMR⟩ := hMi.exists_le_sylow
  let RG := (R : Subgroup C).map C.subtype
  have hMRG : M ≤ RG := by
    have hh := Subgroup.map_mono (f := C.subtype) hMR
    rwa [Subgroup.map_subgroupOf_eq_of_le hMC] at hh
  obtain ⟨Rambient, hRambient⟩ := point_sylow_is_ambient_of_two_fixed_points
    H P p hp hodd hP hPfixed gamma R
  change (Rambient : Subgroup G) = RG at hRambient
  have hRtwo : Nat.card (pointFixedSet H RG) = 2 := by
    rw [← hRambient]
    exact hambient Rambient
  have hRGgamma : gamma ∈ pointFixedSet H RG :=
    (mem_pointFixedSet_iff H RG gamma).mpr (Subgroup.map_subtype_le _)
  have hRcard : 1 < (pointFixedSet H RG).ncard := by
    change 1 < Nat.card (pointFixedSet H RG)
    omega
  obtain ⟨delta, hdeltaR, hdeltagamma⟩ := Set.exists_ne_of_one_lt_ncard hRcard gamma
  have hMpair : M ≤ rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H delta :=
    le_inf hMC (hMRG.trans ((mem_pointFixedSet_iff H RG delta).mp hdeltaR))
  have hRpair : RG ≤ rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H delta :=
    le_inf (Subgroup.map_subtype_le _) ((mem_pointFixedSet_iff H RG delta).mp hdeltaR)
  obtain ⟨S, hSthird⟩ := class_fixed_motion_pair_sylow_fixes_third
    h T hzT hzcenter ht gamma delta (Ne.symm hdeltagamma) htgamma p hp hM hMpair htM
    htmotion.ge
  let D := rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H delta
  let SG := (S : Subgroup D).map D.subtype
  have hindex : ¬ p ∣ D.index := by
    exact fun hdvd => Rambient.not_dvd_index
      (hdvd.trans (Subgroup.index_dvd_of_le (by rw [hRambient]; exact hRpair)))
  have hSp : IsPGroup p SG := S.isPGroup'.map D.subtype
  have hSindex : ¬ p ∣ SG.index := by
    rw [(S : Subgroup D).index_map_of_injective D.subtype_injective, Subgroup.range_subtype]
    exact hp.not_dvd_mul S.not_dvd_index hindex
  let Sambient := hSp.toSylow hSindex
  have hStwo : Nat.card (pointFixedSet H SG) = 2 := hambient Sambient
  have hSGD : SG ≤ D := Subgroup.map_subtype_le _
  have hgammaS : gamma ∈ pointFixedSet H SG :=
    (mem_pointFixedSet_iff H SG gamma).mpr (hSGD.trans inf_le_left)
  have hdeltaS : delta ∈ pointFixedSet H SG :=
    (mem_pointFixedSet_iff H SG delta).mpr (hSGD.trans inf_le_right)
  have hthirdS : pointRightCosetMul H delta t ∈ pointFixedSet H SG :=
    (mem_pointFixedSet_iff H SG _).mpr hSthird
  have hSpair := pointFixedSet_eq_pair_of_card_le_two H SG gamma delta
    (Ne.symm hdeltagamma) hgammaS hdeltaS hStwo.le
  have hthirdNeGamma : pointRightCosetMul H delta t ≠ gamma := by
    intro heq
    exact hdeltagamma (pointRightCosetMul_injective H t (heq.trans htgamma.symm))
  have hu := ((involution_point_unique_containment_action h.distinguished_mem
    h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨_, _, huniq⟩ := hu t ht
  have hthirdNeDelta : pointRightCosetMul H delta t ≠ delta := by
    intro heq
    exact hdeltagamma ((huniq delta heq).trans (huniq gamma htgamma).symm)
  rw [hSpair] at hthirdS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hthirdNeGamma,
    hthirdNeDelta, or_self] at hthirdS

theorem maximal_two_fixed_points_doubly_transitive
    {H P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P) (hPH : P ≤ H)
    (hPfixed : Nat.card (pointFixedSet H P) = 2)
    (hmax : IsMaximalTwoPointPrime H p P) :
    ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d := by
  classical
  obtain ⟨R, hR⟩ := maximal_two_fixed_points_is_ambient_sylow H P p hp hodd hP hPfixed hmax
  have hambient : ∀ S : Sylow p G, Nat.card (pointFixedSet H (S : Subgroup G)) = 2 := by
    intro S
    rw [ambient_sylow_pointFixedSet_card_eq H p hp R S, hR]
    exact hPfixed
  have hbase : rightCosetMk H 1 ∈ pointFixedSet H P := by
    apply (mem_pointFixedSet_iff H P _).mpr
    rwa [rightCosetStabilizer_base]
  have hcard : 1 < (pointFixedSet H P).ncard := by
    change 1 < Nat.card (pointFixedSet H P)
    omega
  obtain ⟨beta, hbetaP, hbeta⟩ := Set.exists_ne_of_one_lt_ncard hcard (rightCosetMk H 1)
  have hPpair : pointFixedSet H P = {rightCosetMk H 1, beta} :=
    pointFixedSet_eq_pair_of_card_le_two H P _ beta (Ne.symm hbeta) hbase hbetaP hPfixed.le
  apply point_right_doubly_transitive_of_base_pair_sylows H p hp R
    (by simpa only [hR] using hPH) beta (by simpa only [hR] using hPpair)
  intro b hb
  let B := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
  let Q : Sylow p B := Classical.choice inferInstance
  let QG := (Q : Subgroup B).map B.subtype
  have hQGB : QG ≤ B := Subgroup.map_subtype_le _
  have haQ : rightCosetMk H 1 ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG _).mpr (hQGB.trans inf_le_left)
  have hbQ : b ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG b).mpr (hQGB.trans inf_le_right)
  have hQle := no_large_pair_sylow_of_two_point_ambient_sylows
    h T hzT hzcenter p hp hodd hP hPfixed hambient _ b (Ne.symm hb) Q
  have hQtwo : Nat.card (pointFixedSet H QG) = 2 := le_antisymm hQle
    (two_le_pointFixedSet_card_of_pair H QG _ b (Ne.symm hb) haQ hbQ)
  obtain ⟨S, hQS⟩ := (Q.isPGroup'.map B.subtype).exists_le_sylow
  obtain ⟨hFixS, _⟩ := odd_prime_overgroup_two_fixed_points H QG (S : Subgroup G)
    p hp hodd (Q.isPGroup'.map B.subtype) S.isPGroup' hQS hQtwo
  have hSB : (S : Subgroup G) ≤ B := le_inf
    ((mem_pointFixedSet_iff H _ _).mp (hFixS.symm ▸ haQ))
    ((mem_pointFixedSet_iff H _ b).mp (hFixS.symm ▸ hbQ))
  refine ⟨S, ?_⟩
  simpa only [B, rightCosetStabilizer_base] using hSB

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
