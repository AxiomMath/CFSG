module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.PlaneCentralizingSubgroupUniqueCentralizer
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G]

theorem factorization_natCard_eq_of_isHallPiIn {π : Set ℕ} {N X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (h : CFSG.FeitThompson.Prep06.IsHallPiIn π N X) (hpπ : p ∈ π) :
    (Nat.card ↥X).factorization p = (Nat.card ↥N).factorization p := by
  have hne : N.relIndex X ≠ 0 := fun h0 => by
    simpa [h0] using (natCard_mul_relIndex h.1).trans_ne (Nat.card_pos (α := ↥X)).ne'
  have hp0 : ¬ p ∣ N.relIndex X := fun hdvd =>
    h.2.2 p (Nat.mem_primeFactors.2 ⟨hp, hdvd, hne⟩) hpπ
  rw [← natCard_mul_relIndex h.1, Nat.factorization_mul Nat.card_pos.ne' hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp0, add_zero]

theorem natCard_sigmaCore_mul_natCard_of_isSplitting {M E : Subgroup G} (hEM : E ≤ M)
    (hsup : sigmaCore M ⊔ E = M) (hinf : sigmaCore M ⊓ E = ⊥) :
    Nat.card ↥(sigmaCore M) * Nat.card ↥E = Nat.card ↥M := by
  have hs : ((sigmaCore M).subgroupOf M) ⊔ (E.subgroupOf M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (sigmaCore_le M) hEM, hsup, subgroupOf_self]
  have h := natCard_mul_natCard_inf_of_normal_of_sup_eq_top hs
  have hbot : (E.subgroupOf M) ⊓ ((sigmaCore M).subgroupOf M) = ⊥ := by
    have h' : (E ⊓ sigmaCore M).subgroupOf M = E.subgroupOf M ⊓ (sigmaCore M).subgroupOf M :=
      map_subtype_inj.mp rfl
    rw [← h', inf_comm, hinf, bot_subgroupOf]
  rw [hbot] at h
  simp only [Subgroup.card_bot, mul_one] at h
  rw [natCard_subgroupOf_eq_natCard_inf, natCard_subgroupOf_eq_natCard_inf,
    inf_eq_left.2 (sigmaCore_le M), inf_eq_left.2 hEM] at h
  exact h.symm

theorem factorization_natCard_eq_of_notMem_sigmaPrimes {M E : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hpσ : p ∉ sigmaPrimes M) (hEM : E ≤ M)
    (hsup : sigmaCore M ⊔ E = M) (hinf : sigmaCore M ⊓ E = ⊥) :
    (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
    hpσ (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  rw [← natCard_sigmaCore_mul_natCard_of_isSplitting hEM hsup hinf,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpS, zero_add]

theorem exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow {M P : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hPM : P ≤ M) (hP : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hrank : elementaryAbelianPRank p ↥M = 2) :
    ∃ A : Subgroup G, A ≤ P ∧ IsElementaryAbelian p A ∧ Nat.card ↥A = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hcomm, hexp, hcard⟩ :=
    (mem_elementaryAbelianRanks_iff_exists_subgroup (X := ↥M) hp).1
      (hrank ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks (X := ↥M) hp.one_lt)
  set A₀ : Subgroup G := H.map M.subtype with hA₀
  have hA₀M : A₀ ≤ M := map_subtype_le _
  have hA₀card : Nat.card ↥A₀ = p ^ 2 := by rw [hA₀, Subgroup.card_subtype]; exact hcard
  have hA₀ea : IsElementaryAbelian p A₀ := (isElementaryAbelian_iff.2 ⟨hcomm, hexp⟩).map M.subtype
  have hPsub : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [natCard_subgroupOf_eq_natCard_inf, inf_eq_left.2 hPM]; exact hP
  have hmap : Subgroup.map M.subtype (Sylow.ofCard (P.subgroupOf M) hPsub : Subgroup ↥M) = P := by
    rw [Sylow.coe_ofCard, map_subgroupOf_eq_of_le hPM]
  obtain ⟨m, -, hle⟩ := exists_mem_map_conj_le_sylow hA₀M
    (IsPGroup.of_card (n := 2) (by
      rw [natCard_subgroupOf_eq_natCard_inf, inf_eq_left.2 hA₀M, hA₀card]))
    (Sylow.ofCard (P.subgroupOf M) hPsub)
  refine ⟨A₀.map (MulAut.conj m : G →* G), hmap ▸ hle, hA₀ea.map _, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
  exact hA₀card

theorem centralizer_le_and_isUniqueMaximalOvergroup_of_le_hall_tauTwo
    (h₁ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    {G : Type u} [Group G] [Finite G] (hG : CFSG.FeitThompson.IsOddSimpleMinimal G)
    {M E E₂ X : Subgroup G} (hM : IsCoatom M) (hEM : E ≤ M)
    (hsup : sigmaCore M ⊔ E = M) (hinf : sigmaCore M ⊓ E = ⊥) (hE₂E : E₂ ≤ E)
    (hE₂ab : IsMulCommutative ↥E₂) (hE₂ : CFSG.FeitThompson.Prep06.IsHallPiIn (tauTwoPrimes M) E₂ E)
    (hXE₂ : X ≤ E₂) (hX : X ≠ ⊥) (hcent : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) :
    centralizer (X : Set G) ≤ M ∧ IsUniqueMaximalOvergroup (centralizer (X : Set G)) M := by
  obtain ⟨p, hp, hpX⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card ↥X) fun h => hX (Subgroup.card_eq_one.1 h)
  have hpτ : p ∈ tauTwoPrimes M := hE₂.2.1 p (Nat.mem_primeFactors.2
    ⟨hp, hpX.trans (Subgroup.card_dvd_of_le hXE₂), Nat.card_pos.ne'⟩)
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tauTwoPrimes hpτ
  have hrank : elementaryAbelianPRank p ↥M = 2 :=
    elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ
  have hfac : (Nat.card ↥M).factorization p = (Nat.card ↥E₂).factorization p := by
    rw [factorization_natCard_eq_of_notMem_sigmaPrimes hp hpσ hEM hsup hinf,
      factorization_natCard_eq_of_isHallPiIn hp hE₂ hpτ]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥E₂))
  have hPE₂ : (Q : Subgroup ↥E₂).map E₂.subtype ≤ E₂ := map_subtype_le _
  have hPcard : Nat.card ↥((Q : Subgroup ↥E₂).map E₂.subtype)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Subgroup.card_subtype, Q.card_eq_multiplicity, hfac]
  obtain ⟨A, hAP, hAea, hAcard⟩ := exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow hp
    (hPE₂.trans (hE₂E.trans hEM)) hPcard hrank
  have hAE₂ : A ≤ E₂ := hAP.trans hPE₂
  have hXA : ⁅X, A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.2 fun x hx =>
      mem_centralizer_iff.2 fun a ha => setLike_mul_comm (s := E₂) (hAE₂ ha) (hXE₂ hx)
  obtain ⟨hle, huniq⟩ := centralizer_le_and_unique_coatom_of_isPlaneAt h₁ hG hM hp hpσ
    (hAE₂.trans (hE₂E.trans hEM)) ⟨hAea, hAcard⟩ (hXE₂.trans (hE₂E.trans hEM)) hX hXA hcent
  exact ⟨hle, hM, hle, fun N hN hCN => huniq N hN hCN⟩

theorem FTS_abelian_rank_two_hall_centralizer_uniqueness
    (h₁ : Statements.FNI_outside_sigma_plane_core_disjoint.{u}) :
    Statements.FTS_abelian_rank_two_hall_centralizer_uniqueness.{u} := by
  intro G _ _ hG M E E₂ hM hEM hsup hinf hE₂E hE₂ab hE₂ X hXE₂ hX hcent
  exact centralizer_le_and_isUniqueMaximalOvergroup_of_le_hall_tauTwo h₁
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩ hM hEM hsup hinf hE₂E hE₂ab hE₂ hXE₂ hX hcent

end

end CFSG.FeitThompson.Proofs
