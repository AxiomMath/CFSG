module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.ExceptionalPrimeFixedConfiguration
import CFSG.FeitThompson.Local.SigmaCoreComplementFixedInDerived
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.CommonFixedOddActionFittingBound
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
public import Mathlib.Tactic.Monotonicity.Lemmas

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem eq_and_eq_of_mul_eq_mul_of_inf_eq_bot {S U : Subgroup G} (hSU : S ⊓ U = ⊥)
    {s s' u u' : G} (hs : s ∈ S) (hs' : s' ∈ S) (hu : u ∈ U) (hu' : u' ∈ U)
    (h : s * u = s' * u') : s = s' ∧ u = u' := by
  have h2 : s'⁻¹ * s = u' * u⁻¹ := by
    have h3 : s' * (u' * u⁻¹) = s := by
      have h4 : s' * u' * u⁻¹ = s := by rw [← h]; group
      rw [← h4]; group
    rw [← h3]; group
  have ht : s'⁻¹ * s ∈ S ⊓ U :=
    ⟨S.mul_mem (S.inv_mem hs') hs, h2 ▸ U.mul_mem hu' (U.inv_mem hu)⟩
  rw [hSU, mem_bot] at ht
  have hss : s = s' := (inv_mul_eq_one.1 ht).symm
  refine ⟨hss, ?_⟩
  rw [hss] at h
  exact mul_left_cancel h

theorem inf_centralizer_singleton_sup_eq {S U : Subgroup G} {k : G} (hSU : S ⊓ U = ⊥)
    (hkS : k ∈ normalizer (S : Set G)) (hkU : k ∈ normalizer (U : Set G))
    (hUS : U ≤ normalizer (S : Set G)) (hfree : U ⊓ centralizer ({k} : Set G) = ⊥) :
    (S ⊔ U) ⊓ centralizer ({k} : Set G) = S ⊓ centralizer ({k} : Set G) := by
  refine le_antisymm ?_ (inf_le_inf_right _ le_sup_left)
  rintro x ⟨hxSU, hxc⟩
  have hcoe : x ∈ ((S ⊔ U : Subgroup G) : Set G) := hxSU
  rw [Subgroup.coe_mul_of_right_le_normalizer_left S U hUS] at hcoe
  obtain ⟨s, hs, u, hu, rfl⟩ := hcoe
  have hs0 : s ∈ S := hs
  have hu0 : u ∈ U := hu
  have hcomm : s * u * k = k * (s * u) := Subgroup.mem_centralizer_singleton_iff.1 hxc
  have hs' : k * s * k⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hkS s).1 hs0
  have hu' : k * u * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hkU u).1 hu0
  have hprod : s * u = (k * s * k⁻¹) * (k * u * k⁻¹) := by
    have hrw : (k * s * k⁻¹) * (k * u * k⁻¹) = k * (s * u) * k⁻¹ := by group
    rw [hrw, ← hcomm]
    group
  obtain ⟨-, hueq⟩ := eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hSU hs0 hs' hu0 hu' hprod
  have hu1 : u = 1 := by
    have hmem : u ∈ U ⊓ centralizer ({k} : Set G) := by
      refine ⟨hu0, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : k * u * k⁻¹ = u := hueq.symm
      calc u * k = (k * u * k⁻¹) * k := by rw [h1]
        _ = k * u := by group
    rw [hfree, mem_bot] at hmem
    exact hmem
  have hxeq : s * u = s := by rw [hu1, mul_one]
  exact ⟨by change s * u ∈ S; rw [hxeq]; exact hs0, hxc⟩

theorem isHallPiOf_of_isHallPiSubgroup_subgroupOf [Finite G] {π : Set ℕ} {K M : Subgroup G}
    (hKM : K ≤ M) (h : IsHallPiSubgroup π (K.subgroupOf M)) :
    CFSG.FeitThompson.Prep03.IsHallPiOf π K M := by
  refine ⟨hKM, fun r hr => ?_, fun r hr => h.notMem_of_mem_primeFactors_index r hr⟩
  refine isPiSubgroup_iff.1 h.isPiSubgroup r ?_
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]

theorem isSemidirect_of_isInternalSemidirectProduct {X Y W : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct X Y W) :
    CFSG.FeitThompson.Prep03.IsSemidirect X Y W :=
  ⟨h.left_le, h.right_le, h.le_normalizer, h.sup_eq, h.inf_eq_bot⟩

theorem inf_centralizer_commutator_le_commutator_commutator [Finite G] {M K : Subgroup G}
    (hMsolv : Group.IsSolvable ↥M) (hKM : K ≤ M)
    (hsup : (⁅M, M⁆ : Subgroup G) ⊔ K = M) (hinf : (⁅M, M⁆ : Subgroup G) ⊓ K = ⊥)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥(⁅M, M⁆ : Subgroup G))) :
    (⁅M, M⁆ : Subgroup G) ⊓ centralizer (K : Set G)
      ≤ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
  have hM'M : (⁅M, M⁆ : Subgroup G) ≤ M := by
    rw [← map_subtype_commutator M]; exact Subgroup.map_subtype_le _
  have hM''M : ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ M :=
    le_trans (Subgroup.commutator_le_self _) hM'M
  have hHeq : _root_.commutator ↥M = (⁅M, M⁆ : Subgroup G).subgroupOf M :=
    commutator_eq_subgroupOf_commutator M
  have hcardK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hcardH : Nat.card ↥((⁅M, M⁆ : Subgroup G).subgroupOf M)
      = Nat.card ↥(⁅M, M⁆ : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv
  have hsup' : (⁅M, M⁆ : Subgroup G).subgroupOf M ⊔ K.subgroupOf M = ⊤ :=
    CFSG.FeitThompson.Proofs.sup_subgroupOf_eq_top_of_sup_eq hM'M hKM hsup
  have hinf' : (⁅M, M⁆ : Subgroup G).subgroupOf M ⊓ K.subgroupOf M = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hinf]
    simp
  have hnormal : ((⁅M, M⁆ : Subgroup G).subgroupOf M).Normal := hHeq ▸ inferInstance
  have hsolvH : Group.IsSolvable ↥((⁅M, M⁆ : Subgroup G).subgroupOf M) := by
    have := hMsolv; infer_instance
  have hHK : (⁅M, M⁆ : Subgroup G).subgroupOf M
      = ⁅(⁅M, M⁆ : Subgroup G).subgroupOf M, K.subgroupOf M⁆ :=
    eq_commutator_of_isSolvable_of_le_commutator _ _ hsup' hinf' (by rw [hHeq])
  have key := CFSG.FeitThompson.Proofs.inf_centralizer_le_commutator_self_of_eq_commutator
    (H := (⁅M, M⁆ : Subgroup G).subgroupOf M) (K := K.subgroupOf M)
    (by rw [hcardK, hcardH]; exact hcop) hHK
  have hmap := Subgroup.map_mono (f := M.subtype) key
  rwa [← subgroupOf_inf_centralizer hKM, Subgroup.map_subgroupOf_eq_of_le
    (le_trans inf_le_left hM'M), commutator_subgroupOf hM'M hM'M,
    Subgroup.map_subgroupOf_eq_of_le hM''M] at hmap

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FBG_kappa_fixed_subgroup_derived_and_hall
    (h₁ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u}) :
    Statements.FBG_kappa_fixed_subgroup_derived_and_hall.{u} := by
  intro G _ _ hG M K hM hKbot hKM hKhall
  have : Fintype G := Fintype.ofFinite G
  have hsimple := hG.isSimpleGroup
  have hamb : IsAmbient G :=
    ⟨hG.odd_natCard, hsimple, hG.not_isMulCommutative, hG.isSolvable⟩
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable M hM.1
  have hHall : IsHallPiOf (kappaPrimes M) K M :=
    isHallPiOf_of_isHallPiSubgroup_subgroupOf hKM hKhall
  have hκ : (kappaPrimes M).Nonempty := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
      (fun h => hKbot (Subgroup.card_eq_one.1 h))
    exact ⟨p, hHall.2.1 p (Nat.mem_primeFactors.2 ⟨hp, hpd, Nat.card_pos.ne'⟩)⟩
  set A : Subgroup G := centralizerWithin (sigmaCore M) K with hAdef
  have hsetup : IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := hamb, isCoatom := hM, kappa_nonempty := hκ, isHall_K := hHall,
      A_eq := rfl, Z_eq := rfl }
  obtain ⟨-, U, E₁, hUab, hUhall, hdec, hdecE, -, -, -, -, hXcent, hAne, hfree⟩ :=
    h₃ G hamb M K hM hκ hHall
  obtain ⟨Mstar, -, -, -, -, -, -, hdirect, hZcyc, -⟩ := h₂ G M K A _ hsetup
  have hAcyc : IsCyclic ↥A := Subgroup.isCyclic_of_le hdirect.2.1
  obtain ⟨hmain, -, hM'eq⟩ := FNI_kappa_derived_complement h₂ h₃ G M K A _ hsetup
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have hAM : A ≤ M := le_trans inf_le_left hSM
  have hSle : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G) :=
    sigmaCore_le_commutator hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hM
  have hcentS : ∀ k ∈ K, k ≠ 1 → sigmaCore M ⊓ centralizer ({k} : Set G) = A := by
    intro k hk hk1
    have hz := hXcent (zpowers k) (Subgroup.zpowers_le_of_mem hk)
      (fun h => hk1 (Subgroup.zpowers_eq_bot.1 h))
    rw [show cent (sigmaCore M) ((zpowers k : Subgroup G) : Set G)
        = sigmaCore M ⊓ centralizer ((zpowers k : Subgroup G) : Set G) from rfl,
      centralizer_coe_zpowers] at hz
    exact hz
  have hM'U : (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ U := hM'eq U hdec hdecE
  have hSU : sigmaCore M ⊓ U = ⊥ :=
    le_bot_iff.1 (le_trans (inf_le_inf_left _ (le_sup_left : U ≤ U ⊔ K)) hdec.2.2.2.2.le)
  have hUnS : U ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    le_trans (le_trans (le_sup_left : U ≤ U ⊔ K) hdec.2.1) hdec.2.2.1
  have hcentM' : ∀ k ∈ K, k ≠ 1 → centralizerWithinElem (⁅M, M⁆ : Subgroup G) k = A := by
    intro k hk hk1
    have hkS : k ∈ normalizer ((sigmaCore M : Subgroup G) : Set G) := hdec.2.2.1 (hKM hk)
    have hkU : k ∈ normalizer ((U : Subgroup G) : Set G) :=
      hdecE.2.2.1 (Subgroup.mem_sup_right hk)
    have hfk : U ⊓ centralizer ({k} : Set G) = ⊥ := hfree k hk hk1
    change (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({k} : Set G) = A
    rw [hM'U, inf_centralizer_singleton_sup_eq hSU hkS hkU hUnS hfk]
    exact hcentS k hk hk1
  have hM'card : Nat.card ↥(⁅M, M⁆ : Subgroup G) = K.relIndex M :=
    natCard_commutator_eq_relIndex hKM hmain
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥(⁅M, M⁆ : Subgroup G)) := by
    by_contra hc
    obtain ⟨p, hp, hpK, hpM'⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
    refine hHall.2.2 p (Nat.mem_primeFactors.2 ⟨hp, hM'card ▸ hpM', ?_⟩)
      (hHall.2.1 p (Nat.mem_primeFactors.2 ⟨hp, hpK, Nat.card_pos.ne'⟩))
    rw [← hM'card]
    exact Nat.card_pos.ne'
  have hAM'' : A ≤ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ :=
    le_trans (inf_le_inf_right _ hSle)
      (inf_centralizer_commutator_le_commutator_commutator hMsolv hKM
        hmain.2.2.2.1 hmain.2.2.2.2 hcop)
  have hAH : A ≤ CFSG.FeitThompson.hallCoreIn M := by
    by_cases hnil : Group.IsNilpotent ↥(sigmaCore M)
    ·
      rw [(hallCoreIn_eq_sigmaCore_iff_isNilpotent hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable hM).2 hnil]
      exact inf_le_left
    ·
      obtain ⟨-, hstruct, -⟩ := h₁ G hG M hM hnil
      obtain ⟨hsd, -, -⟩ := hstruct K hKM hKhall
      obtain ⟨-, -, hAprime, -⟩ :=
        h₄ G M K A _ hsetup (isSemidirect_of_isInternalSemidirectProduct hsd)
      have hHallS : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) :=
        IsHallSubgroup.isHallPiSubgroup
          (isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard
            hG.isSolvable hM)
      have hcpfs := isCommonPrimeFixedSetup_subgroupOf hG.odd_natCard hMsolv hKbot hsd hnil
        hAprime (Z := A) rfl rfl hcentS hHallS hSle
      have hle := hcpfs.Z_le_pCoreIn.trans hcpfs.pCoreIn_le_hallCore
      have hmapped := Subgroup.map_mono (f := M.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hAM, ← CFSG.FeitThompson.hallCoreIn_eq] at hmapped
  exact ⟨hAne, hAcyc, le_inf hAH hAM'', hcentM'⟩

end CFSG.FeitThompson.Proofs

end
