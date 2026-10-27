module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.MetacyclicOddGroupUniqueTorsionPlane
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
public import CFSG.FeitThompson.Local.HallCutoffPrimeTorsionNormal
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem elementaryAbelianPRank_eq_of_isSylowSubgroupOf [Finite G] {p : ℕ} (hp : p.Prime)
    {M P : Subgroup G} (hP : IsSylowIn p M P) :
    elementaryAbelianPRank p ↥P = elementaryAbelianPRank p ↥M := by
  have := Fact.mk hp
  obtain ⟨S, rfl⟩ := hP
  have h1 : elementaryAbelianPRank p ↥(S : Subgroup ↥M) = elementaryAbelianPRank p ↥M :=
    elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp S.card_eq_multiplicity
  have h2 : elementaryAbelianPRank p ↥((S : Subgroup ↥M).map M.subtype)
      = elementaryAbelianPRank p ↥(S : Subgroup ↥M) :=
    (elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
      ((S : Subgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective)).symm
  rw [h2, h1]

theorem exists_isElementaryAbelianPlane_le [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (h : 2 ≤ elementaryAbelianPRank p ↥P) :
    ∃ B : Subgroup G, B ≤ P ∧ IsElementaryAbelianPlane p B := by
  obtain ⟨H, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1 ((le_elementaryAbelianPRank_iff hp.one_lt).1 h)
  exact ⟨H.map P.subtype, map_subtype_le _,
    ⟨(H.equivMapOfInjective P.subtype P.subtype_injective).symm.trans e⟩⟩

theorem isSylowSubgroupOf_ne_bot [Finite G] {p : ℕ} (hp : p.Prime) {M P : Subgroup G}
    (hP : IsSylowIn p M P) (hpM : p ∣ Nat.card ↥M) : P ≠ ⊥ := by
  have := Fact.mk hp
  obtain ⟨S, rfl⟩ := hP
  have hcard : Nat.card ↥((S : Subgroup ↥M).map M.subtype)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Subgroup.card_subtype, S.card_eq_multiplicity]
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have hv : 0 < (Nat.card ↥M).factorization p := hp.factorization_pos_of_dvd Nat.card_pos.ne' hpM
  exact hp.one_lt.ne' (Nat.dvd_one.1 (hcard ▸ dvd_pow_self p hv.ne'))

theorem isPGroup_of_isSylowSubgroupOf {p : ℕ} {M P : Subgroup G} (hP : IsSylowIn p M P) :
    IsPGroup p ↥P := by
  obtain ⟨S, rfl⟩ := hP
  exact S.isPGroup'.map M.subtype

theorem exists_sylow_isCyclic_of_isSylowSubgroupOf {p : ℕ} {M P : Subgroup G}
    (hP : IsSylowIn p M P) (hcyc : IsCyclic ↥P) :
    ∃ S : Sylow p ↥M, IsCyclic ↥((S : Subgroup ↥M).map M.subtype) := by
  obtain ⟨S, rfl⟩ := hP
  exact ⟨S, hcyc⟩

theorem zpowers_eq_of_natCard_eq_prime {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : Nat.card ↥A = p) {e : G} (he : e ∈ A) (he1 : e ≠ 1) : zpowers e = A := by
  have := Fact.mk hp
  have hle : zpowers e ≤ A := zpowers_le.2 he
  have hne : (⟨e, he⟩ : ↥A) ≠ 1 := by simpa [Subtype.ext_iff] using he1
  refine le_antisymm hle fun x hx => ?_
  obtain ⟨k, hk⟩ := mem_zpowers_of_prime_card (G := ↥A) hA hne (g' := (⟨x, hx⟩ : ↥A))
  exact ⟨k, by simpa [Subtype.ext_iff] using congrArg (Subgroup.subtype A) hk⟩

theorem natCard_powEqOneSubgroup_of_isCyclic [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    [IsMulCommutative ↥P] (hcyc : IsCyclic ↥P) (hPp : IsPGroup p ↥P) (hPbot : P ≠ ⊥) :
    Nat.card ↥(powEqOneSubgroup p P) = p := by
  have := hcyc
  have : Nontrivial ↥P := P.nontrivial_iff_ne_bot.2 hPbot
  obtain ⟨K, hKcard, hKmem⟩ := exists_natCard_eq_prime_forall_pow_eq_one_mem hp hPp
  have hmap : K.map P.subtype = powEqOneSubgroup p P := by
    refine le_antisymm ?_ ?_
    · rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      refine mem_powEqOneSubgroup_of_pow_eq_one y.2 ?_
      have h1 : (⟨y, hy⟩ : ↥K) ^ Nat.card ↥K = 1 := pow_card_eq_one'
      rw [hKcard] at h1
      have hy' : y ^ p = 1 := by simpa [Subtype.ext_iff] using congrArg (Subgroup.subtype K) h1
      simpa [Subtype.ext_iff] using congrArg (Subgroup.subtype P) hy'
    · intro x hx
      obtain ⟨hxP, hxp⟩ := mem_powEqOneSubgroup.1 hx
      have h2 : (⟨x, hxP⟩ : ↥P) ^ p = 1 := Subtype.ext (by simpa using hxp)
      exact Subgroup.mem_map.2 ⟨⟨x, hxP⟩, hKmem _ h2, rfl⟩
  rw [← hmap, Subgroup.card_subtype, hKcard]

theorem coe_powEqOneSubgroup_eq {p : ℕ} {P : Subgroup G} [IsMulCommutative ↥P] :
    ((powEqOneSubgroup p P : Subgroup G) : Set G) = {x ∈ (P : Set G) | x ^ p = 1} := by
  ext x; simp [mem_powEqOneSubgroup]

theorem isElementaryAbelianSubgroup_powEqOneSubgroup {p : ℕ} {P : Subgroup G}
    [IsMulCommutative ↥P] : IsElementaryAbelianSubgroup p (powEqOneSubgroup p P) :=
  ⟨fun _ hx _ hy =>
    setLike_mul_comm (s := P) (powEqOneSubgroup_le hx) (powEqOneSubgroup_le hy),
   fun _ hx => pow_eq_one_of_mem_powEqOneSubgroup hx⟩

theorem isNilpotent_sigmaCore_of_line [Finite G] {p : ℕ} (hp : p.Prime)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) {M A : Subgroup G} (hM : IsCoatom M)
    (hAM : A ≤ M) (hAcard : Nat.card ↥A = p)
    (hC : sigmaCore M ⊓ centralizer (A : Set G) = ⊥) :
    Group.IsNilpotent ↥(sigmaCore M) := by
  have := Fact.mk hp
  have : Group.IsSolvable ↥(sigmaCore M) :=
    hsolv _ (fun h => hM.1 (top_le_iff.1 (h ▸ sigmaCore_le M)))
  have hcyc : IsCyclic ↥A := isCyclic_of_prime_card hAcard
  have hcomm : IsMulCommutative ↥A := inferInstance
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    exact hp.one_lt.ne' hAcard.symm
  refine isNilpotent_of_isSolvable_of_le_normalizer ?_ hAbot
    (hAM.trans (le_normalizer_sigmaCore M)) ?_
  · exact le_bot_iff.1 (hC ▸ inf_le_inf_left _ (Subgroup.le_centralizer A))
  · intro e he he1
    have hz : zpowers e = A := zpowers_eq_of_natCard_eq_prime hp hAcard he he1
    have hcz : centralizer ({e} : Set G) = centralizer (A : Set G) := by
      rw [← hz, zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcz]
    exact hC

theorem sylow_outside_sigma_kappa [Finite G]
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : IsOddSimpleMinimal G) {p : ℕ} {M P : Subgroup G} (hM : IsCoatom M) (hp : p.Prime)
    (hpM : p ∣ Nat.card ↥M) (hpσ : p ∉ sigmaPrimes M) (hpκ : p ∉ kappaPrimes M)
    (hP : IsSylowIn p M P) :
    IsMulCommutative ↥P ∧
      (∃ A : Subgroup G, (A : Set G) = {x ∈ (P : Set G) | x ^ p = 1} ∧
        IsElementaryAbelianSubgroup p A ∧ (Nat.card ↥A = p ∨ Nat.card ↥A = p ^ 2) ∧
        sigmaCore M ⊓ centralizer (A : Set G) = ⊥) ∧
      Group.IsNilpotent ↥(sigmaCore M) := by
  have hG08 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hPM : P ≤ M := hP.le
  rcases le_or_gt 2 (elementaryAbelianPRank p ↥P) with hge | hlt
  ·
    obtain ⟨B, hBP, hB⟩ := exists_isElementaryAbelianPlane_le hp hge
    have hplane : IsOutsideSigmaPlane p M B := ⟨hM, hp, hpσ, hBP.trans hPM, hB⟩
    obtain ⟨-, -, hsyl, -⟩ := h₂ G hG p M B hplane
    obtain ⟨hPcomm, hBeq⟩ := hsyl P hP
    obtain ⟨hnil, hCB, -⟩ := h₃ G hG08 M B p hM hp hpσ (hBP.trans hPM)
      ⟨isElementaryAbelian_iff_isElementaryAbelianSubgroup.2 hB.isElementaryAbelianSubgroup,
        hB.natCard'⟩
    exact ⟨hPcomm, ⟨B, (hBeq hBP).1, hB.isElementaryAbelianSubgroup, Or.inr hB.natCard', hCB⟩, hnil⟩
  ·
    have hodd : Odd p := Odd.of_dvd_nat hG.odd_natCard (hpM.trans M.card_subgroup_dvd_card)
    have hPp : IsPGroup p ↥P := isPGroup_of_isSylowSubgroupOf hP
    have hcyc : IsCyclic ↥P := isCyclic_of_elementaryAbelianPRank_le_one hp hodd hPp (by omega)
    have hPcomm : IsMulCommutative ↥P := inferInstance
    have hPbot : P ≠ ⊥ := isSylowSubgroupOf_ne_bot hp hP hpM
    set A : Subgroup G := powEqOneSubgroup p P with hAdef
    have hAcard : Nat.card ↥A = p := natCard_powEqOneSubgroup_of_isCyclic hp hcyc hPp hPbot
    have hAM : A ≤ M := (powEqOneSubgroup_le (p := p) (Q := P)).trans hPM
    have hCA : sigmaCore M ⊓ centralizer (A : Set G) = ⊥ := by
      by_contra hne
      exact hpκ ((mem_kappaPrimes_iff_inf_centralizer_ne_bot hp hpσ
        (exists_sylow_isCyclic_of_isSylowSubgroupOf hP hcyc) hAM hAcard).2 hne)
    exact ⟨hPcomm, ⟨A, coe_powEqOneSubgroup_eq, isElementaryAbelianSubgroup_powEqOneSubgroup,
      Or.inl hAcard, hCA⟩,
      isNilpotent_sigmaCore_of_line hp hG.isSolvable_of_ne_top hM hAM hAcard hCA⟩

theorem FNI_outside_sigma_kappa_sylow_core_nilpotent
    (_h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FNI_outside_sigma_kappa_sylow_core_nilpotent.{u} := by
  intro G _ _ hG p M P hM hp hpM hpσκ hP
  exact sylow_outside_sigma_kappa h₂ h₃ hG hM hp hpM
    (fun h => hpσκ (Set.mem_union_left _ h)) (fun h => hpσκ (Set.mem_union_right _ h)) hP

end

end CFSG.FeitThompson.Proofs
