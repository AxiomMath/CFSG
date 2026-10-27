module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NoncentralInvariantSylowFixedPointFreePlane
import CFSG.FeitThompson.Local.ExceptionalPlaneFixedFreeLines
import CFSG.FeitThompson.Local.OutsideSigmaFixedFreeLineCommutator
import CFSG.FeitThompson.Local.FixedFreePlaneGeneratedByCommutators
import CFSG.FeitThompson.Representations.ZeroFixedSpacePrimeComplementCentralizes
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Foundations.NonabelianPGroupInvariantCentralDerived
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup

universe u

variable {G : Type*} [Group G] {p : ℕ}

theorem inf_eq_bot_of_natCard_eq_prime_of_ne [Finite G] (hp : p.Prime) {A₁ A₂ : Subgroup G}
    (h1 : Nat.card ↥A₁ = p) (h2 : Nat.card ↥A₂ = p) (hne : A₁ ≠ A₂) : A₁ ⊓ A₂ = ⊥ := by
  have hdvd : Nat.card ↥(A₁ ⊓ A₂) ∣ p := h1 ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact Subgroup.card_eq_one.1 h
  · have hI1 : A₁ ⊓ A₂ = A₁ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h1])
    have hI2 : A₁ ⊓ A₂ = A₂ :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, h2])
    exact absurd (hI1.symm.trans hI2) hne

theorem sup_eq_of_natCard_eq_prime_sq [Finite G] (hp : p.Prime) {A A₁ A₂ : Subgroup G}
    (hA : Nat.card ↥A = p ^ 2) (hle1 : A₁ ≤ A) (hle2 : A₂ ≤ A)
    (h1 : Nat.card ↥A₁ = p) (h2 : Nat.card ↥A₂ = p) (hne : A₁ ≠ A₂) : A₁ ⊔ A₂ = A := by
  have hsupA : A₁ ⊔ A₂ ≤ A := sup_le hle1 hle2
  have hdvd : Nat.card ↥(A₁ ⊔ A₂) ∣ p ^ 2 := hA ▸ Subgroup.card_dvd_of_le hsupA
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rcases Nat.lt_or_ge k 2 with hklt | hkge
  · exfalso
    have hcard_le : Nat.card ↥(A₁ ⊔ A₂) ≤ p := by
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    have hsup1 : A₁ = A₁ ⊔ A₂ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h1]; exact hcard_le)
    have h2le : A₂ ≤ A₁ := hsup1 ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge h2le (by rw [h1, h2])).symm
  · have hk2' : k = 2 := le_antisymm hk2 hkge
    exact Subgroup.eq_of_le_of_card_ge hsupA (by rw [hk, hk2']; exact le_of_eq hA)

theorem le_sup_commutator_of_lines [Finite G] (hp : p.Prime)
    {V A A₁ A₂ : Subgroup G} (hVab : IsMulCommutative ↥V)
    (hAV : A ≤ normalizer (V : Set G)) (hAab : IsMulCommutative ↥A)
    (h1 : A₁ ≤ A) (h2 : A₂ ≤ A) (hc1 : Nat.card ↥A₁ = p) (hc2 : Nat.card ↥A₂ = p)
    (hsup : A₁ ⊔ A₂ = A) (hinf : A₁ ⊓ A₂ = ⊥)
    (hpV : ¬ p ∣ Nat.card ↥V) (hfix : V ⊓ centralizer (A : Set G) = ⊥) :
    V ≤ ⁅V, A₁⁆ ⊔ ⁅V, A₂⁆ := by
  let _ : CommGroup ↥V := @IsMulCommutative.instCommGroup _ _ hVab
  set ρ : ↥A →* MulAut ↥V := conjAction hAV with hρ
  have hB1card : Nat.card ↥(A₁.subgroupOf A) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv, hc1]
  have hB2card : Nat.card ↥(A₂.subgroupOf A) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2).toEquiv, hc2]
  have hBsup : A₁.subgroupOf A ⊔ A₂.subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h1 h2, hsup, Subgroup.subgroupOf_self]
  have hBinf : A₁.subgroupOf A ⊓ A₂.subgroupOf A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : G) ∈ A₁ ⊓ A₂ := ⟨mem_subgroupOf.1 hx.1, mem_subgroupOf.1 hx.2⟩
    rw [hinf, Subgroup.mem_bot] at hxG
    exact Subgroup.mem_bot.2 (Subtype.ext hxG)
  have hcomm : ∀ x ∈ A₁.subgroupOf A, ∀ y ∈ A₂.subgroupOf A, Commute x y :=
    fun x _ y _ => hAab.is_comm.comm x y
  have hfix' : ∀ v : ↥V, (∀ a : ↥A, ρ a v = v) → v = 1 := by
    intro v hv
    have hvc : (v : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro g hg
      have h := hv ⟨g, hg⟩
      have h2 : g * (v : G) * g⁻¹ = (v : G) := by
        have hco := congrArg (fun z : ↥V => (z : G)) h
        rwa [hρ, coe_conjAction_apply] at hco
      calc g * (v : G) = (g * (v : G) * g⁻¹) * g := by group
        _ = (v : G) * g := by rw [h2]
    have hmem : (v : G) ∈ V ⊓ centralizer (A : Set G) := ⟨v.2, hvc⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have key := sup_closure_inv_mul_smul_eq_top_of_card_eq_prime ρ hp hB1card hB2card hBsup hBinf
    hcomm hpV hfix'
  have hclos : ∀ Ai : Subgroup G, Ai ≤ A →
      Subgroup.map V.subtype
          (Subgroup.closure {x : ↥V | ∃ a ∈ Ai.subgroupOf A, ∃ w : ↥V, w⁻¹ * ρ a w = x})
        ≤ ⁅V, Ai⁆ := by
    intro Ai _
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨a, ha, w, rfl⟩
    change ((w⁻¹ * ρ a w : ↥V) : G) ∈ ⁅V, Ai⁆
    have ha' : ((a : ↥A) : G) ∈ Ai := mem_subgroupOf.1 ha
    have hmem := Subgroup.commutator_mem_commutator (H₁ := V) (H₂ := Ai)
      (V.inv_mem w.2) ha'
    rw [commutatorElement_def] at hmem
    have heq : ((w⁻¹ * ρ a w : ↥V) : G)
        = ((w : ↥V) : G)⁻¹ * ((a : ↥A) : G) * (((w : ↥V) : G)⁻¹)⁻¹ * ((a : ↥A) : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ, coe_conjAction_apply]
      group
    rw [heq]
    exact hmem
  have hmapsup : Subgroup.map V.subtype
      ((Subgroup.closure {x : ↥V | ∃ a ∈ A₁.subgroupOf A, ∃ w : ↥V, w⁻¹ * ρ a w = x})
        ⊔ Subgroup.closure {x : ↥V | ∃ a ∈ A₂.subgroupOf A, ∃ w : ↥V, w⁻¹ * ρ a w = x})
      ≤ ⁅V, A₁⁆ ⊔ ⁅V, A₂⁆ := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (hclos A₁ h1) (hclos A₂ h2)
  rw [key] at hmapsup
  calc V = Subgroup.map V.subtype ⊤ := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ ≤ _ := hmapsup

theorem FTS_exceptional_plane_centralizes_outside_sylow
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_plane_centralizes_outside_sylow.{u} := by
  intro G _ _ hG p M A₀ A P hc q hq hqp hqσ Q hQM hAQ
  by_contra hQA
  have := Fact.mk hq
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hp : p.Prime := hc.prime
  have hCQA : Q ⊓ centralizer (A : Set G) = ⊥ :=
    FTS_exceptional_noncentral_sylow_fixed_free h₂ h₄ G hG p M A₀ A P hc q hq hqp hqσ Q hQM hAQ hQA
  have hQpg : IsPGroup q ↥Q := IsPGroup.of_card hQM.2
  have hQbot : Q ≠ ⊥ := by
    intro h
    rw [h] at hQA
    exact hQA (by simp)
  have hQnt : Nontrivial ↥Q := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQbot
    exact ⟨⟨x, 1, hx1⟩⟩
  set V : Subgroup G := Q ⊓ centralizer (Q : Set G) with hVdef
  have hVQ : V ≤ Q := by rw [hVdef]; exact inf_le_left
  have hVab : IsMulCommutative ↥V := by
    rw [hVdef]; exact isMulCommutative_inf_centralizer_self Q
  have hAV : A ≤ normalizer (V : Set G) := by
    rw [hVdef]; exact le_normalizer_inf_centralizer_self_of_le_normalizer hAQ
  have hNQV : normalizer (Q : Set G) ≤ normalizer (V : Set G) := by
    rw [hVdef]; exact le_normalizer_inf_centralizer_self_of_le_normalizer le_rfl
  have hVne : V ≠ ⊥ := by
    have hnt : Nontrivial ↥(Subgroup.center ↥Q) := IsPGroup.center_nontrivial hQpg
    rw [hVdef, ← map_subtype_center_eq_inf_centralizer, Ne, Subgroup.map_eq_bot_iff,
      Subgroup.ker_subtype, le_bot_iff]
    intro hbot
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥Q))
    exact hz (Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot _ z.2))
  obtain ⟨-, -, A₁, A₂, h1A, h2A, hne12, hc1, hc2, hfree1, hfree2⟩ :=
    FTS_exceptional_plane_fixed_free_lines h₁ h₃ h₄ G hG p M A₀ A P hc
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hAab : IsMulCommutative ↥A := hc.isElementaryAbelianPlane.isMulCommutative
  have hsup12 : A₁ ⊔ A₂ = A := sup_eq_of_natCard_eq_prime_sq hp hAcard h1A h2A hc1 hc2 hne12
  have hinf12 : A₁ ⊓ A₂ = ⊥ := inf_eq_bot_of_natCard_eq_prime_of_ne hp hc1 hc2 hne12
  have hVdvd : Nat.card ↥V ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hVQ
  have hpV : ¬ p ∣ Nat.card ↥V := by
    intro hdvd
    have hpQ : p ∣ Nat.card ↥Q := hdvd.trans hVdvd
    rw [hQM.2] at hpQ
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hpQ)).symm
  have hVπ : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥V → s ∉ sigmaPrimes M := by
    intro s hs hsdvd
    have hsQ : s ∣ Nat.card ↥Q := hsdvd.trans hVdvd
    rw [hQM.2] at hsQ
    have hsq : s = q := (Nat.prime_dvd_prime_iff_eq hs hq).1 (hs.dvd_of_dvd_pow hsQ)
    rw [hsq]; exact hqσ
  have hVfix : V ⊓ centralizer (A : Set G) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_right _ hVQ).trans (le_of_eq hCQA))
  have hVle : V ≤ ⁅V, A₁⁆ ⊔ ⁅V, A₂⁆ :=
    le_sup_commutator_of_lines hp hVab hAV hAab h1A h2A hc1 hc2 hsup12 hinf12 hpV hVfix
  have hAiV : ∀ Ai : Subgroup G, Ai ≤ A → ⁅V, Ai⁆ ≤ V := fun Ai hi =>
    commutator_le_left_of_le_normalizer (hi.trans hAV)
  have hVeq : ⁅V, A₁⁆ ⊔ ⁅V, A₂⁆ = V :=
    le_antisymm (sup_le (hAiV A₁ h1A) (hAiV A₂ h2A)) hVle
  have hGmin : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hVM : V ≤ M := hVQ.trans hQM.1
  have hnorm : ∀ Ai : Subgroup G, Ai ≤ A → Nat.card ↥Ai = p →
      sigmaCore M ⊓ centralizer (Ai : Set G) = ⊥ →
      M ≤ normalizer ((⁅V, Ai⁆ : Subgroup G) : Set G) := by
    intro Ai hi hci hfi
    exact (FTS_outside_sigma_fixed_free_line_commutator h₁ h₂ h₄ G hGmin M V Ai p hc.isCoatom hp
      hc.notMem_sigmaPrimes hVM hVab hVπ hpV
      (le_inf (hi.trans hAV) (hi.trans (hc.le_of_A.trans hc.le_of_P))) hci hfi).2.2
  have hMV : M ≤ normalizer (V : Set G) := by
    have hsupnorm := le_normalizer_sup (hnorm A₁ h1A hc1 hfree1) (hnorm A₂ h2A hc2 hfree2)
    rwa [hVeq] at hsupnorm
  have hNV : normalizer (V : Set G) = M := normalizer_eq_of_isCoatom hc.isCoatom hVne hVM hMV
  have hNQM : normalizer (Q : Set G) ≤ M := le_trans hNQV (le_of_eq hNV)
  have hqM : q ∣ Nat.card ↥M :=
    (prime_dvd_natCard_of_isPGroup_of_ne_bot hq hQpg hQbot).trans (Subgroup.card_dvd_of_le hQM.1)
  exact hqσ ((mem_sigmaPrimes_iff_exists_subgroup hq).2 ⟨hqM, Q, hQM.1, hQM.2, hNQM⟩)

end

end CFSG.FeitThompson.Proofs
