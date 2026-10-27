module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AuxiliaryOppositeTauTwoRankOne
import CFSG.FeitThompson.Local.HallKappaSubgroupTI

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem isInternalSemidirectProduct_of_isSemidirect {X Y Z : Subgroup G}
    (h : CFSG.FeitThompson.Prep03.IsSemidirect X Y Z) :
    FreeCore.IsInternalSemidirectProduct X Y Z :=
  ⟨h.2.2.2.1, h.2.2.1, disjoint_iff.2 h.2.2.2.2⟩

theorem notMem_betaPrimes_and_notMem_betaPrimes_subgroup [Finite G]
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H)
    {M T : Subgroup G} (hT : IsCoatom T) {p : ℕ}
    (hp : p ∈ tauTwoPrimes T) (hpM : p ∈ sigmaPrimes M) :
    p ∉ betaPrimes G ∧ p ∉ betaPrimes ↥M := by
  have h1 : p ∉ betaPrimes G :=
    notMem_betaPrimes_of_mem_tauTwoPrimes h₃ ⟨hodd, hsimple, hna, hsolv⟩ hT hp
  exact ⟨h1, fun hmem => h1 ((mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hpM).1 hmem)⟩

theorem isInternalSemidirectProduct_sigmaCore_of_sigmaPrimes_ne_betaPrimes [Finite G]
    (h₁ : Statements.FBG_kappa_nontrivial_complement_structure.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H)
    {M : Subgroup G} (hM : IsCoatom M) (hκ : (kappaPrimes M).Nonempty)
    (hne : sigmaPrimes M ≠ betaPrimes ↥M) {K : Subgroup G}
    (hK : CFSG.FeitThompson.IsHallPiSubgroupOf (kappaPrimes M) K M) :
    FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K := by
  have : Fintype G := Fintype.ofFinite G
  have hKH := isHallPiOf_of_isHallPiSubgroupOf hK
  obtain ⟨-, U, E₁, hUab, hUhall, hsemiM, hsemiUK, -⟩ :=
    h₂ G ⟨hodd, hsimple, hna, hsolv⟩ M K hM hκ hKH
  have hU : U = ⊥ := by
    by_contra hU
    exact hne (h₁ G ⟨hodd, hsimple, hna, hsolv⟩ M K U
      ⟨hM, hκ, hK.1, hK.2, hUhall.1, hU, isInternalSemidirectProduct_of_isSemidirect hsemiM,
        isInternalSemidirectProduct_of_isSemidirect hsemiUK⟩).2.1
  rw [hU, bot_sup_eq] at hsemiM
  exact isInternalSemidirectProduct_of_isSemidirect hsemiM

theorem FTS_kappa_positive_multiple_core_trivial_residual
    (h₁ : Statements.FBG_kappa_nontrivial_complement_structure.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : Statements.FTS_signalizer_unique_supporting_maximum.{u}) :
    Statements.FTS_kappa_positive_multiple_core_trivial_residual.{u} := by
  intro G _ _ hG x hx hk M hM T hT hTu hκ
  have hx1 : x ≠ 1 := by
    obtain ⟨-, -, -, hx1⟩ := CFSG.FeitThompson.mem_sigmaSupport.1 hx
    exact hx1
  have hMc : IsCoatom M := (CFSG.FeitThompson.mem_sigmaSupportingMaximals.1 hM).1
  have hxS : x ∈ sigmaCore M := (CFSG.FeitThompson.mem_sigmaSupportingMaximals.1 hM).2
  have hTc : IsCoatom T := CFSG.FeitThompson.mem_maximalSubgroups.1 hT
  have hpos : 0 < orderOf x := orderOf_pos x
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hpmem⟩ := Nat.nonempty_primeFactors.2 (show 1 < orderOf x by omega)
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpdvd : p ∣ orderOf x := Nat.dvd_of_mem_primeFactors hpmem
  have hcard : orderOf x ∣ Nat.card ↥(sigmaCore M) := by
    simpa using orderOf_dvd_natCard (⟨x, hxS⟩ : ↥(sigmaCore M))
  have hpσ : p ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hpdvd.trans hcard, Nat.card_pos.ne'⟩)
  have h4 := (h₄ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
    x hx hk).2 T hTc hTu.le
  have hpτ : p ∈ tauTwoPrimes T := h4.2.2.1 p hp hpdvd
  obtain ⟨hpβG, hpβM⟩ := notMem_betaPrimes_and_notMem_betaPrimes_subgroup h₃ hG.odd_natCard
    hG.isSimpleGroup hG.not_isMulCommutative hG.isSolvable hTc hpτ hpσ
  have hneβ : sigmaPrimes M ≠ betaPrimes ↥M := fun heq => hpβM (heq ▸ hpσ)
  refine ⟨⟨p, hpmem, hpσ, hpτ, hpβG, hpβM⟩, hneβ, fun K hK => ?_⟩
  exact isInternalSemidirectProduct_sigmaCore_of_sigmaPrimes_ne_betaPrimes h₁ h₂ hG.odd_natCard
    hG.isSimpleGroup hG.not_isMulCommutative hG.isSolvable hMc hκ hneβ hK

end

end CFSG.FeitThompson.Proofs
