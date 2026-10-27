module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Foundations.DistinctPrimeCoresCommute
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
public import Mathlib.Tactic.Monotonicity.Lemmas

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G] {p : ℕ}

theorem normalizer_le_normalizer_of_eq_pTorsion {A Q : Subgroup G}
    (hA : (A : Set G) = {x ∈ (Q : Set G) | x ^ p = 1}) :
    normalizer (Q : Set G) ≤ normalizer (A : Set G) := by
  have hmem : ∀ x : G, x ∈ A ↔ x ∈ Q ∧ x ^ p = 1 := fun x => by
    rw [← SetLike.mem_coe, hA]; exact Iff.rfl
  intro g hg
  rw [mem_normalizer_iff] at hg ⊢
  intro h
  have hiff : (g * h * g⁻¹) ^ p = 1 ↔ h ^ p = 1 := by
    rw [show (g * h * g⁻¹) ^ p = g * h ^ p * g⁻¹ from conj_pow]
    refine ⟨fun hx => ?_, fun hx => by rw [hx]; group⟩
    rw [show h ^ p = g⁻¹ * (g * h ^ p * g⁻¹) * g from by group, hx]; group
  rw [hmem, hmem, hg h, hiff]

theorem mul_comm_of_natCard_eq_pow_factorization [Finite G] (hp : p.Prime) {F Q : Subgroup G}
    (hnil : Group.IsNilpotent ↥F) (hQF : Q ≤ F)
    (hQcard : Nat.card ↥Q = p ^ (Nat.card ↥F).factorization p) (hQab : IsMulCommutative ↥Q) :
    ∀ x ∈ F, ∀ y ∈ Q, x * y = y * x := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have := hnil
  have hcardQ' : Nat.card ↥(Q.subgroupOf F) = p ^ (Nat.card ↥F).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQF).toEquiv, hQcard]
  have hQ'normal : (Q.subgroupOf F).Normal := normal_of_natCard_eq_pow_factorization hcardQ'
  have hQ'ab : IsMulCommutative ↥(Q.subgroupOf F) :=
    isMulCommutative_subgroupOf_of_isMulCommutative hQab
  have hpeq : pCore p ↥F = Q.subgroupOf F :=
    le_antisymm
      (Subgroup.map_le_iff_le_comap.1
        (le_of_isPGroup_le_nilpotent hnil hQF hQcard (map_subtype_le _)
          ((isPGroup_pCore hp ↥F).map F.subtype)))
      (le_pCore hp hQ'normal (IsPGroup.of_card hcardQ'))
  have hcent : centralizer ((Q.subgroupOf F : Subgroup ↥F) : Set ↥F) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← fittingRaw_eq_top_of_isNilpotent ↥F, fittingRaw_eq_iSup_pCore]
    refine iSup₂_le fun q hq => ?_
    have hq' : q.Prime := hq
    rcases eq_or_ne q p with rfl | hqp
    · rw [hpeq]; exact Subgroup.le_centralizer _
    · refine (pCore_le_centralizer_pCore hp hq' (Ne.symm hqp) ↥F).trans ?_
      rw [hpeq]
  intro x hx y hy
  have hxc : (⟨x, hx⟩ : ↥F) ∈ centralizer ((Q.subgroupOf F : Subgroup ↥F) : Set ↥F) := by
    rw [hcent]; exact mem_top _
  exact (congrArg Subtype.val
    (mem_centralizer_iff.1 hxc ⟨y, hQF hy⟩ (by simpa [mem_subgroupOf] using hy))).symm

theorem FBG_abelian_ambient_tau_two_fitting
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_abelian_ambient_tau_two_fitting.{u} := by
  intro G _ _ hG M p A E P hsetup
  have hsimple := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G := ⟨hodd, hsimple, hna, hsolv⟩
  obtain ⟨hM, hp, hpσ, hAM, hplane, hEM, hsd, hAE, hPab, ⟨S, hS⟩, hAP⟩ := hsetup
  have hfp : Fact p.Prime := ⟨hp⟩
  have hplane' : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A := hplane
  have hAcard : Nat.card ↥A = p ^ 2 := hplane'.natCard'
  have hAp : IsPGroup p ↥A := IsPGroup.of_card hAcard
  have hA0 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    have := Nat.one_lt_pow (n := 2) two_ne_zero hp.one_lt
    omega
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hM, hp, hpσ, hAM, hplane⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsd⟩
  obtain ⟨hEN, -, hCA_E, -, -⟩ := h₂ G hGosm p M A E hosp hsc hAE
  have hAEnormal : (A.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hAE).2 hEN
  have hAN : A ≤ normalizer (A : Set G) := le_normalizer
  have hANnormal : (A.subgroupOf (normalizer (A : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAN).2 le_rfl
  have hSab : IsMulCommutative ↥((S : Subgroup G)) := by rw [hS]; exact hPab
  have hFE : mixedFitting E = mixedFitting (centralizer (A : Set G)) := by
    rw [mixedFitting_eq, mixedFitting_eq]
    exact map_fittingRaw_eq_map_fittingRaw_centralizer hp S hSab hAE hAEnormal hAp hCA_E
  have hFN : mixedFitting (normalizer (A : Set G)) = mixedFitting (centralizer (A : Set G)) := by
    rw [mixedFitting_eq, mixedFitting_eq]
    exact map_fittingRaw_eq_map_fittingRaw_centralizer hp S hSab hAN hANnormal hAp
      (centralizer_le_normalizer _)
  have hFNE : mixedFitting (normalizer (A : Set G)) = mixedFitting E := hFN.trans hFE.symm
  obtain ⟨-, hrank, -⟩ := FNI_sigma_complement_prime_data h₁ G hGosm M E hsc
  have hrankE : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥E ≤ 2 := by
    intro q hq
    by_cases hqd : q ∣ Nat.card ↥E
    · obtain ⟨heq, hle⟩ := hrank q ⟨hq, hqd⟩
      omega
    · have := (elementaryAbelianPRank_eq_zero_iff (X := ↥E) hq).2 hqd
      omega
  have hNtop : normalizer (A : Set G) ≠ ⊤ :=
    ne_of_lt (normalizer_lt_top_of_isPGroup hna hp hA0 hAp)
  have hNsolv : Group.IsSolvable ↥(normalizer (A : Set G)) := hsolv _ hNtop
  have hNodd : Odd (Nat.card ↥(normalizer (A : Set G))) := odd_natCard_subgroup hodd _
  have hrankN : ∀ q : ℕ, q.Prime →
      elementaryAbelianPRank q ↥(fittingRaw ↥(normalizer (A : Set G))) ≤ 2 := by
    intro q hq
    have h1 : elementaryAbelianPRank q ↥(fittingRaw ↥(normalizer (A : Set G)))
        = elementaryAbelianPRank q ↥(mixedFitting (normalizer (A : Set G))) := by
      rw [mixedFitting_eq]
      exact elementaryAbelianPRank_eq_of_mulEquiv hq.one_lt
        ((fittingRaw _).equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective)
    have h2 : mixedFitting (normalizer (A : Set G)) ≤ E := by
      rw [hFNE]; exact mixedFitting_le E
    calc elementaryAbelianPRank q ↥(fittingRaw ↥(normalizer (A : Set G)))
        = elementaryAbelianPRank q ↥(mixedFitting (normalizer (A : Set G))) := h1
      _ ≤ elementaryAbelianPRank q ↥E := elementaryAbelianPRank_le_of_le hq.one_lt h2
      _ ≤ 2 := hrankE q hq
  have hcommN : ⁅normalizer (A : Set G), normalizer (A : Set G)⁆ ≤ mixedFitting E := by
    have hkey := commutator_le_fittingRaw (G := ↥(normalizer (A : Set G))) hNodd hrankN
    calc ⁅normalizer (A : Set G), normalizer (A : Set G)⁆
        = (_root_.commutator ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype :=
          (Subgroup.map_subtype_commutator _).symm
      _ ≤ (fittingRaw ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype :=
          map_mono hkey
      _ = mixedFitting (normalizer (A : Set G)) := (mixedFitting_eq _).symm
      _ = mixedFitting E := hFNE
  have hPC : P ≤ centralizer (A : Set G) :=
    (Subgroup.le_centralizer P).trans (centralizer_le (SetLike.coe_subset_coe.2 hAP))
  have hPE : P ≤ E := hPC.trans hCA_E
  have hPM : P ≤ M := hPE.trans hEM
  have hPcardG : Nat.card ↥P = p ^ (Nat.card G).factorization p := by
    rw [← hS]; exact S.card_eq_multiplicity
  have hPsylM : _root_.CFSG.FeitThompson.IsSylowIn p M P :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hPM).2
      (natCard_eq_pow_factorization_of_le hp hPM hPcardG)
  obtain ⟨-, -, hsyl, -⟩ := h₃ G hGosm p M A hosp
  obtain ⟨hAtors, -⟩ := (hsyl P hPsylM).2 hAP
  have hNPN : normalizer (P : Set G) ≤ normalizer (A : Set G) :=
    normalizer_le_normalizer_of_eq_pTorsion hAtors
  have hP0 : P ≠ ⊥ := fun h => hA0 (le_bot_iff.1 (h ▸ hAP))
  have hPNP : P ≤ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ := by
    let _ : Fintype G := Fintype.ofFinite G
    refine h₄ G ⟨hodd, hsimple, hna, hsolv⟩ p hp P hP0 ⟨le_top, ?_⟩
    rw [Subgroup.card_top]
    exact hPcardG
  have hcommP : ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤ mixedFitting E :=
    (commutator_mono hNPN hNPN).trans hcommN
  have hFnil : Group.IsNilpotent ↥(mixedFitting E) := by
    rw [mixedFitting_eq]; exact isNilpotent_map_fittingRaw E
  have hPF : P ≤ mixedFitting E := hPNP.trans hcommP
  have hcomm := mul_comm_of_natCard_eq_pow_factorization hp hFnil hPF
    (natCard_eq_pow_factorization_of_le hp hPF hPcardG) hPab
  refine ⟨hPNP, hcommP, ?_, ?_, hFNE, ?_⟩
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  · exact (centralizer_le (SetLike.coe_subset_coe.2 hAP)).trans hCA_E
  · rw [centreIn_eq]
    refine le_inf hPF fun y hy => ?_
    rw [mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy

end

end CFSG.FeitThompson.Proofs
