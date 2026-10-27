module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.KappaResidualLocalNormalizer
import CFSG.FeitThompson.Local.KappaResidualContainedOppositeSigmaCore
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.OddOrder.ConjugateAffineIntersection

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem dvd_natCard_hall_of_mem_kappaPrimes [Finite G] {M K : Subgroup G}
    (hK : IsHallPiSubgroupOf (kappaPrimes M) K M) {p : ℕ} (hp : p ∈ kappaPrimes M) :
    p ∣ Nat.card ↥K := by
  obtain ⟨hpp, hpM, -⟩ := mem_kappaPrimes_iff.1 hp
  rcases (Nat.Prime.dvd_mul hpp).1 (natCard_mul_relIndex hK.le ▸ hpM) with h | h
  · exact h
  · exact absurd hp ((isHallPiSubgroup_iff.1 hK.2).2 p
      (Nat.mem_primeFactors.2 ⟨hpp, h, Subgroup.index_ne_zero_of_finite⟩))

theorem natCard_dvd_natCard_of_isPiSubgroup [Finite G] {π : Set ℕ} {U M V : Subgroup G}
    (hU : IsHallPiSubgroupOf π U M) (hVM : V ≤ M) (hV : IsPiSubgroup π V) :
    Nat.card ↥V ∣ Nat.card ↥U := by
  have hidx : U.relIndex M ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  have hcop : Nat.Coprime (Nat.card ↥V) (U.relIndex M) := by
    refine (Nat.disjoint_primeFactors Nat.card_pos.ne' hidx).1
      (Finset.disjoint_left.2 fun p hp hp' => ?_)
    exact (isHallPiSubgroup_iff.1 hU.2).2 p hp' (isPiSubgroup_iff.1 hV p hp)
  exact hcop.dvd_of_dvd_mul_right
    (natCard_mul_relIndex hU.le ▸ Subgroup.card_dvd_of_le hVM)

theorem kappa_residual_prime_overgroup_intersection [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_containing_complement_fitting.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (hG : IsFTAmbient G) {r : ℕ} {M K U A Mstar R H : Subgroup G}
    (hP : IsKappaResidualPartner r M K U A Mstar R H) :
    Group.IsNilpotent ↥(sigmaCore H) ∧ sigmaCore H ⊓ M = U ∧ H ⊓ M = U ⊔ K ∧
      ¬ normalizer (U : Set G) ⊓ H ≤ M := by
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsetup : Prep08.IsKappaResidualSetup M K U A Mstar R H r :=
    { isCoatom_M := hP.config.isCoatom
      kappa_nonempty := hP.config.kappaPrimes_nonempty
      isHall_K := ⟨hP.config.isHallKappa.1, hP.config.isHallKappa.2⟩
      isHall_U := ⟨hP.config.isHallCompl.1, hP.config.isHallCompl.2⟩
      semidirect_M := hP.config.isInternalSemidirectProduct
      semidirect_UK := hP.config.isInternalSemidirectProduct_complement
      isMulCommutative_U := hP.isMulCommutative_U
      centralizer_U := hP.centralizer_eq_bot
      U_ne_bot := hP.U_ne_bot
      A_eq := hP.A_eq
      isCoatom_Mstar := hP.isCoatom_Mstar
      exists_prime_order_le_K := hP.exists_prime_order_normalizer_le
      prime_r := hP.prime_r
      r_dvd := hP.dvd_natCard_U
      isSylow_R := (Prep08.isSylowOf_iff_natCard hP.prime_r hP.isSylowSubgroupOf_R.le).2
        hP.isSylowSubgroupOf_R.2
      isCoatom_H := hP.isCoatom_H
      normalizer_R_le := hP.normalizer_R_le }
  obtain ⟨hKprime, hUKH, hnc, -, hkH, hqσH⟩ := h₄ G hG08 M K U A Mstar R H r hsetup
  set q : ℕ := Nat.card ↥K with hqdef
  have : Fact q.Prime := ⟨hKprime⟩
  have hKH : K ≤ H := le_sup_right.trans hUKH
  have hqH : q ∣ Nat.card ↥H := hqdef ▸ Subgroup.card_dvd_of_le hKH
  have hnil : Group.IsNilpotent ↥(sigmaCore H) := by
    obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥H))
    have hS : _root_.CFSG.FeitThompson.IsSylowIn q H ((S : Subgroup ↥H).map H.subtype) := ⟨S, rfl⟩
    have hqσ : q ∉ sigmaPrimes H := hqσH q hKprime dvd_rfl
    have hqκ : q ∉ kappaPrimes H := by rw [hkH]; exact Set.notMem_empty q
    exact (FNI_outside_sigma_kappa_sylow_core_nilpotent h₁ h₂ h₅ G hG04 q H _
      hP.isCoatom_H hKprime hqH (by rintro (h | h); exacts [hqσ h, hqκ h]) hS).2.2
  have hUSH : U ≤ sigmaCore H :=
    FTS_kappa_residual_contained_opposite_sigma_core h₃ h₄ G hG r M K U A Mstar R H hP
  have hsep : sigmaPrimes M ∩ sigmaPrimes H = ∅ :=
    h₆ G hG09 M H hP.config.isCoatom hP.isCoatom_H fun g h => hnc g h
  have hV : sigmaCore H ⊓ M = U := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hUSH hP.config.isHallCompl.le) ?_).symm
    refine Nat.le_of_dvd Nat.card_pos
      (natCard_dvd_natCard_of_isPiSubgroup hP.config.isHallCompl inf_le_right ?_)
    refine isPiSubgroup_iff.2 fun p hp => ?_
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 hp
    have hpH : p ∈ sigmaPrimes H :=
      isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore H) p (Nat.mem_primeFactors.2
        ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    refine ⟨hpp, fun hpM => ?_, fun hpκ => ?_⟩
    · exact Set.eq_empty_iff_forall_notMem.1 hsep p ⟨hpM, hpH⟩
    · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hKprime).1
        (dvd_natCard_hall_of_mem_kappaPrimes hP.config.isHallKappa hpκ)
      exact hqσH q hKprime dvd_rfl (hpq ▸ hpH)
  have hHM : H ⊓ M = U ⊔ K := by
    have hloc :=
      (FTS_kappa_residual_local_normalizer h₁ h₂ h₅ G hG M K U hP.config hP.U_ne_bot).2
    refine le_antisymm (fun x hx => ?_)
      (le_inf hUKH hP.config.isInternalSemidirectProduct.right_le)
    obtain ⟨hxH, hxM⟩ := Subgroup.mem_inf.1 hx
    have hxN : x ∈ normalizer (U : Set G) := by
      rw [← hV]
      exact mem_normalizer_inf (le_normalizer_sigmaCore H hxH) (Subgroup.le_normalizer hxM)
    rw [← hloc]
    exact Subgroup.mem_inf.2 ⟨hxN, hxM⟩
  refine ⟨hnil, hV, hHM, ?_⟩
  intro hle
  by_cases hUeq : U = sigmaCore H
  ·
    have hHle : H ≤ M := fun x hx => hle (Subgroup.mem_inf.2
      ⟨by rw [hUeq]; exact le_normalizer_sigmaCore H hx, hx⟩)
    have hHeq : H = M := by
      rcases lt_or_eq_of_le hHle with hlt | heq
      · exact absurd (hP.isCoatom_H.2 M hlt) hP.config.isCoatom.1
      · exact heq
    exact hnc 1 (by rw [hHeq]; simp [Prep08.conjSubgroup])
  ·
    have hlt : U.subgroupOf (sigmaCore H) < ⊤ :=
      lt_of_le_of_ne le_top fun h =>
        hUeq (le_antisymm hUSH (Subgroup.subgroupOf_eq_top.1 h))
    have := hnil
    obtain ⟨y, hy, hy'⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥(sigmaCore H)) _ hlt)
    have hyG : (y : G) ∈ normalizer (U : Set G) := (mem_normalizer_subgroupOf_iff hUSH y).1 hy
    have hyH : (y : G) ∈ H := sigmaCore_le H y.2
    have hyM : (y : G) ∉ M := fun hm =>
      hy' ((Subgroup.mem_subgroupOf).2 (by rw [← hV]; exact Subgroup.mem_inf.2 ⟨y.2, hm⟩))
    exact hyM (hle (Subgroup.mem_inf.2 ⟨hyG, hyH⟩))

theorem FTS_kappa_residual_prime_overgroup_intersection
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_containing_complement_fitting.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_intersection.{u} := by
  intro G _ _ hG r M K U A Mstar R H hP
  exact kappa_residual_prime_overgroup_intersection h₁ h₂ h₃ h₄ h₅ h₆ hG hP

end

end CFSG.FeitThompson.Proofs
