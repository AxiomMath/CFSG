module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NoSigmaKappaPrimesRankTwoPrimes
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

theorem isElementaryAbelian_of_nonempty_mulEquiv_pi {Y : Type*} [Group Y] {p : ℕ}
    {A : Subgroup Y} (h : Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p)))) :
    IsElementaryAbelian p A := by
  obtain ⟨f⟩ := h
  refine isElementaryAbelian_iff.2
    ⟨⟨⟨fun a b => f.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
  have hp : (⟨x, hx⟩ : ↥A) ^ p = 1 :=
    f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
  exact congrArg Subtype.val hp

theorem isCyclic_of_isMulCommutative_of_isZGroup {Y : Type*} [Group Y] [Finite Y]
    (hab : IsMulCommutative Y) (hz : IsZGroup Y) : IsCyclic Y :=
  have _i := hab
  have _i := hz
  have _i : Group.IsNilpotent Y := CommGroup.isNilpotent
  inferInstance

theorem isCyclic_and_isPiSubgroup_tauTwoPrimes
    (h₁ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₂ : Statements.FTS_outside_sigma_plane_structure.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsOddOrderMinimalSimple G)
    {M X : Subgroup G} (hM : IsCoatom M) (hXM : X ≤ M)
    (hX : IsPiSubgroup (sigmaPrimes M ∪ kappaPrimes M)ᶜ X)
    (hC : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) :
    IsCyclic ↥X ∧ IsPiSubgroup (tauTwoPrimes M) X := by
  have _i := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  have hτ : ↑(Nat.card ↥X).primeFactors ⊆ tauTwoPrimes M :=
    primeFactors_subset_tauTwoPrimes_of_isPiSubgroup hna hodd hsolv hM hXM hX hC
  have hXτ : IsPiSubgroup (tauTwoPrimes M) X := isPiSubgroup_iff.2 fun q hq => hτ hq
  refine ⟨?_, hXτ⟩
  have _i : Group.IsSolvable ↥M := hsolv M hM.1
  have hXσ : IsPiSubgroup (sigmaPrimes M)ᶜ (X.subgroupOf M) := isPiSubgroup_iff.2 fun q hq => by
    rw [natCard_subgroupOf_of_le hXM] at hq
    exact notMem_sigmaPrimes_of_mem_tauTwoPrimes (isPiSubgroup_iff.1 hXτ q hq)
  obtain ⟨E', hE', hXE'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hXσ
  have hEM : E'.map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hEsub : (E'.map M.subtype).subgroupOf M = E' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective E'
  have hXE : X ≤ E'.map M.subtype := by
    have h := Subgroup.map_mono (f := M.subtype) hXE'
    rwa [Subgroup.map_subgroupOf_eq_of_le hXM] at h
  have hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (E'.map M.subtype) := by
    obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl (sigmaCore_le M) hEM
      (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM)
      (by rw [hEsub]; exact hE') (hEM.trans (le_normalizer_sigmaCore M))
    exact ⟨hsup, le_normalizer_sigmaCore M, disjoint_iff.2 hinf⟩
  have hEtop : E'.map M.subtype ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have _i : Group.IsSolvable ↥(E'.map M.subtype) := hsolv _ hEtop
  have hXτE : IsPiSubgroup (tauTwoPrimes M) (X.subgroupOf (E'.map M.subtype)) :=
    isPiSubgroup_iff.2 fun q hq => by
      rw [natCard_subgroupOf_of_le hXE] at hq
      exact isPiSubgroup_iff.1 hXτ q hq
  obtain ⟨E₂', hE₂', hXE₂'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hXτE
  have hXE₂ : X ≤ E₂'.map (E'.map M.subtype).subtype := by
    have h := Subgroup.map_mono (f := (E'.map M.subtype).subtype) hXE₂'
    rwa [Subgroup.map_subgroupOf_eq_of_le hXE] at h
  have hE₂sub : (E₂'.map (E'.map M.subtype).subtype).subgroupOf (E'.map M.subtype) = E₂' :=
    Subgroup.comap_map_eq_self_of_injective (E'.map M.subtype).subtype_injective E₂'
  have hE₂ab : IsMulCommutative ↥(E₂'.map (E'.map M.subtype).subtype) :=
    @h₁ G _ (Fintype.ofFinite G) hG M hM (E'.map M.subtype) hsemi
      (E₂'.map (E'.map M.subtype).subtype)
      (isHallPiSubgroupOf_iff.2 ⟨Subgroup.map_subtype_le _, by
        rw [hE₂sub]; exact hE₂'.isHallPiSubgroup⟩)
  have _i := hE₂ab
  have hXab : IsMulCommutative ↥X :=
    ⟨⟨fun a b => Subtype.ext (setLike_mul_comm
      (s := E₂'.map (E'.map M.subtype).subtype) (hXE₂ a.2) (hXE₂ b.2))⟩⟩
  have hsylow : ∀ q : ℕ, q.Prime → ∀ P : Sylow q ↥X, IsCyclic ↥(P : Subgroup ↥X) := by
    intro q hq P
    by_contra hnc
    have _i := Fact.mk hq
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have _i : Subsingleton ↥(P : Subgroup ↥X) := (Nat.card_eq_one_iff_unique.1 hk).1
      exact hnc isCyclic_of_subsingleton
    have hqX : q ∣ Nat.card ↥X :=
      (hk ▸ dvd_pow_self q hk0).trans (Subgroup.card_subgroup_dvd_card _)
    have hqτ : q ∈ tauTwoPrimes M := hτ (Nat.mem_primeFactors.2 ⟨hq, hqX, Nat.card_pos.ne'⟩)
    have hqodd : Odd q := hodd.of_dvd_nat
      (hqX.trans ((Subgroup.card_dvd_of_le hXM).trans (Subgroup.card_subgroup_dvd_card M)))
    obtain ⟨A, -, -, hAiso⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hq hqodd
      P.isPGroup' (⊤ : Subgroup ↥(P : Subgroup ↥X))
      (fun _ => hnc (isCyclic_of_surjective (⊤ : Subgroup ↥(P : Subgroup ↥X)).subtype
        fun x => ⟨⟨x, trivial⟩, rfl⟩))
    have hBX : (A.map (P : Subgroup ↥X).subtype).map X.subtype ≤ X := Subgroup.map_subtype_le _
    have hBcard : Nat.card ↥((A.map (P : Subgroup ↥X).subtype).map X.subtype) = q ^ 2 := by
      rw [Subgroup.card_subtype, Subgroup.card_subtype]
      obtain ⟨f⟩ := hAiso
      rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
    have hplane : CFSG.FeitThompson.Prep08.IsPlaneAt q
        ((A.map (P : Subgroup ↥X).subtype).map X.subtype) :=
      ⟨((isElementaryAbelian_of_nonempty_mulEquiv_pi hAiso).map _).map _, hBcard⟩
    have hG' : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
      ⟨hG.isSimpleGroup, hna, hodd, hsolv⟩
    have hCB := (h₂ G hG' M ((A.map (P : Subgroup ↥X).subtype).map X.subtype) q hM hq
      (notMem_sigmaPrimes_of_mem_tauTwoPrimes hqτ) (hBX.trans hXM) hplane).2.1
    refine hC (le_bot_iff.1 ?_)
    calc sigmaCore M ⊓ centralizer (X : Set G)
        ≤ sigmaCore M ⊓ centralizer
            (((A.map (P : Subgroup ↥X).subtype).map X.subtype : Subgroup G) : Set G) :=
          inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hBX))
      _ = ⊥ := hCB
  exact isCyclic_of_isMulCommutative_of_isZGroup hXab ((isZGroup_iff ↥X).2 hsylow)

theorem FBG_outside_sigma_kappa_core_fixer_cyclic
    (h₁ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₂ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FBG_outside_sigma_kappa_core_fixer_cyclic.{u} := by
  intro G _ _ hG M hM X hXM hX hC
  exact isCyclic_and_isPiSubgroup_tauTwoPrimes h₁ h₂ hG hM hXM hX hC

end

end CFSG.FeitThompson.Proofs
