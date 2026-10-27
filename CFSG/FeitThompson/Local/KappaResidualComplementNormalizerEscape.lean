module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem isHallPiOf_of_isHallPiSubgroupOf {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {K M : Subgroup G} (h : IsHallPiSubgroupOf π K M) : IsHallPiOf π K M :=
  ⟨h.le, fun _ hr => isPiSubgroup_iff.1 h.isPiSubgroup _ hr,
    fun _ hr => h.2.notMem_of_mem_primeFactors_index _ hr⟩

theorem FTS_kappa_residual_normalizer_escape
    (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FTS_kappa_residual_prime_overgroup_intersection.{u}) :
    Statements.FTS_kappa_residual_normalizer_escape.{u} := by
  intro G _ _ hG M K U hcfg hUab hfree
  have hsimple := hG.isSimpleGroup
  have hMtop : M ≠ ⊤ := hcfg.isCoatom.1
  rcases eq_or_ne U ⊥ with hU | hU
  · subst hU
    rw [Subgroup.normalizer_eq_top]
    exact fun h => hMtop (top_le_iff.1 h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥U)
    (fun h => hU (Subgroup.card_eq_one.1 h))
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r ↥U))
  set R : Subgroup G := (P : Subgroup ↥U).map U.subtype with hRdef
  have hRcard : Nat.card ↥R = r ^ (Nat.card ↥U).factorization r := by
    rw [hRdef, Subgroup.card_subtype]
    exact P.card_eq_multiplicity
  have hRU : R ≤ U := Subgroup.map_subtype_le _
  have hUM : U ≤ M := hcfg.isHallCompl.le
  have hpos : 0 < (Nat.card ↥U).factorization r :=
    hr.factorization_pos_of_dvd Nat.card_pos.ne' hrdvd
  have hRbot : ⊥ < R := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    rw [h, Subgroup.card_bot] at hRcard
    exact absurd hRcard.symm (Nat.one_lt_pow hpos.ne' hr.one_lt).ne'
  have hRtop : R < ⊤ := lt_of_le_of_lt (hRU.trans hUM) (lt_top_iff_ne_top.2 hMtop)
  obtain ⟨H, hHcoatom, hNH⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_lt_top_of_isSimpleGroup hRbot hRtop).ne
  have : Fintype G := Fintype.ofFinite G
  have hsetup : IsKappaSetup G M K (sigmaCore M ⊓ centralizer (K : Set G))
      (K ⊔ (sigmaCore M ⊓ centralizer (K : Set G))) :=
    { ambient := ⟨hG.odd_natCard, hsimple, hG.not_isMulCommutative, hG.isSolvable⟩
      isCoatom := hcfg.isCoatom
      kappa_nonempty := hcfg.kappaPrimes_nonempty
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf hcfg.isHallKappa
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨Mstar, ⟨hMstarCoatom, hX⟩, -⟩ := h₁ G M K _ _ hsetup
  have hpartner : IsKappaResidualPartner r M K U (sigmaCore M ⊓ centralizer (K : Set G))
      Mstar R H :=
    { config := hcfg
      isMulCommutative_U := hUab
      centralizer_eq_bot := hfree
      U_ne_bot := hU
      A_eq := rfl
      isCoatom_Mstar := hMstarCoatom
      exists_prime_order_normalizer_le := hX
      prime_r := hr
      dvd_natCard_U := hrdvd
      isSylowSubgroupOf_R := ⟨hRU, hRcard⟩
      isCoatom_H := hHcoatom
      normalizer_R_le := hNH }
  exact fun hle => (h₂ G hG r M K U _ Mstar R H hpartner).2.2.2 (inf_le_left.trans hle)

end

end CFSG.FeitThompson.Proofs
