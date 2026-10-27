module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.KappaResidualComplementNormalizerEscape
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

theorem isHallPiSubgroup_bot_of_eq_empty {X : Type*} [Group X] {π : Set ℕ} (hπ : π = ∅) :
    IsHallPiSubgroup π (⊥ : Subgroup X) :=
  ⟨isPiSubgroup_bot π, by simp [hπ]⟩

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FBG_kappa_complement_structure
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_intersection.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_kappa_complement_structure.{u} := by
  intro G _ _ hG M hM
  have hsimple := hG.isSimpleGroup
  have hsolv : Group.IsSolvable ↥M := hG.isSolvable M hM.1
  rcases Set.eq_empty_or_nonempty (kappaPrimes M) with hκ | hκ
  ·
    have := hsimple.toNontrivial
    have hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M :=
      ⟨sigmaCore_le M, (isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative
        hG.odd_natCard hG.isSolvable hM).isHallPiSubgroup⟩
    have hder := sigmaCore_le_commutator hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hM
    obtain ⟨U, hUM, -, hsd⟩ :=
      exists_sigmaComplement hG.not_isMulCommutative hM hsolv hHall hder
    refine ⟨⊥, U, bot_le, inferInstance, ?_, hUM, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact isHallPiSubgroup_bot_of_eq_empty hκ
    · rw [sup_bot_eq]; exact hsd
    · exact ⟨rfl, by rw [sup_bot_eq]; exact Subgroup.le_normalizer, disjoint_bot_right⟩
    · exact fun k hk hk1 => absurd (Subgroup.mem_bot.1 hk) hk1
    · exact fun h => absurd rfl h
  ·
    have _fin : Fintype G := Fintype.ofFinite G
    have hamb : IsAmbient G :=
      ⟨hG.odd_natCard, hsimple, hG.not_isMulCommutative, hG.isSolvable⟩
    obtain ⟨K', hK'⟩ := exists_isHallSubgroup (X := ↥M) (kappaPrimes M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le _
    have hKsub : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hKhall : IsHallSubgroup (kappaPrimes M) (K.subgroupOf M) := hKsub ▸ hK'
    have hKpi : IsHallPiOf (kappaPrimes M) K M :=
      isHallPiOf_of_isHallSubgroup_subgroupOf hKM hKhall
    obtain ⟨-, U, -, hUcomm, hUhall, hsemi1, hsemi2, -, -, -, -, hcent, hcentne, hfree⟩ :=
      h₂ G hamb M K hM hκ hKpi
    have hsd1 : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K) :=
      isInternalSemidirectProduct_of_isSemidirect hsemi1
    have hsd2 : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K :=
      isInternalSemidirectProduct_of_isSemidirect hsemi2
    have hsetup : IsKappaSetup G M K (cent (sigmaCore M) (K : Set G))
        (K ⊔ cent (sigmaCore M) (K : Set G)) :=
      { ambient := hamb
        isCoatom := hM
        kappa_nonempty := hκ
        isHall_K := hKpi
        A_eq := rfl
        Z_eq := rfl }
    obtain ⟨-, -, -, -, -, -, -, hdir, hcyc, -⟩ := h₁ G M K _ _ hsetup
    have hKcyc : IsCyclic ↥K := Subgroup.isCyclic_of_le hdir.1
    have hUhall' : IsHallPiSubgroupOf
        {r : ℕ | r.Prime ∧ r ∉ sigmaPrimes M ∧ r ∉ kappaPrimes M} U M := by
      refine isHallPiSubgroupOf_of_isHallPiOf hUhall ?_
      refine fun r hr => ⟨fun h => ⟨hr, fun hs => h (Or.inl hs), fun hk => h (Or.inr hk)⟩, ?_⟩
      rintro h (hs | hk)
      · exact h.2.1 hs
      · exact h.2.2 hk
    have hcfg : IsKappaResidualConfig M K U :=
      { isCoatom := hM
        kappaPrimes_nonempty := hκ
        isHallKappa := ⟨hKM, hKhall.isHallPiSubgroup⟩
        isHallCompl := hUhall'
        isInternalSemidirectProduct := hsd1
        isInternalSemidirectProduct_complement := hsd2 }
    have hesc := FTS_kappa_residual_normalizer_escape h₁ h₃ G
      ⟨hsimple, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩ M K U hcfg hUcomm hfree
    have hcenteq : ∀ k ∈ K, k ≠ 1 →
        centralizerWithinElem (sigmaCore M) k = centralizerWithin (sigmaCore M) K := by
      intro k hk hk1
      have h := hcent (Subgroup.zpowers k) (Subgroup.zpowers_le.2 hk)
        (Subgroup.zpowers_ne_bot.2 hk1)
      have hc : Subgroup.centralizer ((Subgroup.zpowers k : Subgroup G) : Set G)
          = Subgroup.centralizer ({k} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      change sigmaCore M ⊓ Subgroup.centralizer ({k} : Set G)
        = sigmaCore M ⊓ Subgroup.centralizer (K : Set G)
      rw [← hc]
      exact h
    exact ⟨K, U, hKM, hKcyc, hKhall.isHallPiSubgroup, hUhall'.le, hsd1, hsd2, hfree,
      fun _ => ⟨hUcomm, hesc, hcenteq, hcentne⟩⟩

end

end CFSG.FeitThompson.Proofs
