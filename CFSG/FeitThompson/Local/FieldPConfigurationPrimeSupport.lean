module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Local.SylowCorePrimeSupportDetection
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.TwoCoreMixedSaturationMeasure
import CFSG.FeitThompson.Representations.TwoTISaturationsFourRegionAverage
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G]

theorem hallCoreIn_eq_hallCoreOf (M : Subgroup G) :
    CFSG.FeitThompson.hallCoreIn M = hallCoreOf M := by
  rw [CFSG.FeitThompson.hallCoreIn_eq, hallCoreOf_eq]

theorem sat_sharp_eq_conjugatesOfSet (Y : Subgroup G) :
    CFSG.FeitThompson.sat (CFSG.FeitThompson.sharp Y) = Group.conjugatesOfSet ((Y : Set G) \ {1}) := by
  rw [conjugatesOfSet_eq_iUnion_image_conj_inv, CFSG.FeitThompson.sat_eq, CFSG.FeitThompson.sharp_eq]
  rfl

theorem inf_centralizer_singleton_eq_bot_of_forall_invariant {U P : Subgroup G}
    (hUab : IsMulCommutative ↥U) (hUP : U ≤ normalizer (P : Set G))
    (hirr : ∀ V : Subgroup G, V ≤ P → U ≤ normalizer (V : Set G) → V = ⊥ ∨ V = P)
    (hfaith : U ⊓ centralizer (P : Set G) = ⊥)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    P ⊓ centralizer ({u} : Set G) = ⊥ := by
  set V : Subgroup G := P ⊓ centralizer ({u} : Set G) with hV
  have hcommU : ∀ x ∈ U, ∀ y ∈ U, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hUab.is_comm.comm (⟨x, hx⟩ : ↥U) (⟨y, hy⟩ : ↥U))
  have hstep : ∀ v ∈ U, ∀ x ∈ V, v * x * v⁻¹ ∈ V := by
    intro v hv x hx
    have cv : Commute v u := hcommU v hv u hu
    have cx : Commute x u := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hUP hv) x).1 hx.1,
      Subgroup.mem_centralizer_singleton_iff.2 ((cv.mul_left cx).mul_left cv.inv_left)⟩
  have hnorm : U ≤ normalizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hstep v hv x hx, fun hx => ?_⟩
    have h2 := hstep v⁻¹ (U.inv_mem hv) _ hx
    have he : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
    rwa [he] at h2
  rcases hirr V inf_le_left hnorm with h | h
  · exact h
  · exfalso
    have huc : u ∈ U ⊓ centralizer (P : Set G) := by
      refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have hxV : x ∈ V := by rw [h]; exact hx
      exact Subgroup.mem_centralizer_singleton_iff.1 hxV.2
    rw [hfaith] at huc
    exact hu1 (Subgroup.mem_bot.1 huc)

theorem natCard_hallCoreOf_eq_pow_factorization [Finite G] {S U W₁ : Subgroup G} {p : ℕ}
    (hp : p.Prime)
    (hsemi₁ : FreeCore.IsInternalSemidirectProduct S (hallCoreOf S) (U ⊔ W₁))
    (hsemi₂ : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hcop : Nat.Coprime (Nat.card ↥(hallCoreOf S)) (Nat.card ↥U * Nat.card ↥W₁))
    (hcardH : Nat.card ↥(hallCoreOf S) = p ^ Nat.card ↥W₁) :
    Nat.card ↥(hallCoreOf S) = p ^ (Nat.card ↥S).factorization p := by
  have hq0 : Nat.card ↥W₁ ≠ 0 := Nat.card_pos.ne'
  have hpH : p ∣ Nat.card ↥(hallCoreOf S) := hcardH ▸ dvd_pow_self p hq0
  have hnd : ¬ p ∣ Nat.card ↥U * Nat.card ↥W₁ :=
    hp.coprime_iff_not_dvd.1 (Nat.Coprime.coprime_dvd_left hpH hcop)
  have hcards : Nat.card ↥S = p ^ Nat.card ↥W₁ * (Nat.card ↥U * Nat.card ↥W₁) := by
    rw [hsemi₁.natCard_eq_mul, hsemi₂.natCard_eq_mul, hcardH]
  rw [hcardH, hcards, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne')
    (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'), Finsupp.add_apply,
    hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]
  simp

theorem isSylowCorePrimeSetup_of_pConfiguration [Finite G] {S U W₁ W₂ : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hcardPG : Nat.card ↥(hallCoreOf S) = p ^ (Nat.card G).factorization p)
    (hHne : hallCoreOf S ≠ ⊥) (hUne : U ≠ ⊥)
    (hc : IsWitnessedPConfiguration S U W₁ W₂)
    (hnormP : normalizer ((hallCoreOf S : Subgroup G) : Set G) = S)
    (hTIH : IsTIWithNormalizer ((hallCoreOf S : Set G) \ {1}) S)
    (hcU : ∀ v ∈ U, v ≠ 1 → hallCoreOf S ⊓ centralizer ({v} : Set G) = ⊥) :
    IsSylowCorePrimeSetup p S (hallCoreOf S) U W₁ W₂ (⁅S, S⁆ : Subgroup G) := by
  have hSP : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hSJ : S ≤ normalizer ((⁅S, S⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left S S
  exact {
    prime := hp
    card_P := hcardPG
    ne_bot_P := hHne
    ne_bot_U := hUne
    ne_bot_B := hc.ne_bot_W₁
    normal_P := hc.normal_subgroupOf_hallCore
    coe_mul_coe_eq_J := by
      calc (hallCoreOf S : Set G) * (U : Set G)
          = ((hallCoreOf S ⊔ U : Subgroup G) : Set G) :=
            (Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hc.le_M_E.trans hSP)).symm
        _ = ((⁅S, S⁆ : Subgroup G) : Set G) := by rw [hallCoreOf_eq, hc.sup_hallCore_E]
    inf_P_U := disjoint_iff.1 hc.disjoint_hallCore_E
    normal_J := normal_subgroupOf_commutator_self S
    coe_mul_coe_eq_S := by
      calc ((⁅S, S⁆ : Subgroup G) : Set G) * (W₁ : Set G)
          = ((⁅S, S⁆ ⊔ W₁ : Subgroup G) : Set G) :=
            (Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hc.le_M_W₁.trans hSJ)).symm
        _ = (S : Set G) := by rw [hc.sup_commutator_W₁]
    inf_J_B := disjoint_iff.1 hc.disjoint_commutator_W₁
    coprime_card := Nat.coprime_comm.1 hc.coprime_natCard_W₁_natCard_commutator
    inf_centralizer_U := hcU
    le_A_P := hc.le_hallCore_W₂
    inf_centralizer_B := hc.inf_centralizer_eq_W₂
    normalizer_P := hnormP
    ti_punctured := fun x hx => hTIH.disjoint_image_conj_inv hx }

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FBG_field_p_configuration_prime_support
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FBG_field_p_configuration_prime_support.{u} := by
  intro G _ _ hG S U W₁ W₂ p hS hc hp2 hp hirr g hgP hgW
  have hG' : Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨-, -, -, -, -, -, hUne, hUab, hsemi₁, hsemi₂, hcop, -,
    -, hcardH, -, -, hHne, -, -, -, -, -, hTIH, -⟩ :=
    h₂ G hG' S U W₁ W₂ hS hc p (Nat.card ↥W₁) hp2.symm rfl
  have hfaith : centralizerIn U (hallCoreOf S) = ⊥ :=
    (FNI_type_p_inner_action_faithful.{u} h₁ h₂ G hG' S U W₁ W₂ hS hc).1
  have hSP : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hnormP : normalizer ((hallCoreOf S : Subgroup G) : Set G) = S := by
    rw [← normalizer_sdiff_one (hallCoreOf S)]; exact hTIH.normalizer_eq
  have hcardPG : Nat.card ↥(hallCoreOf S) = p ^ (Nat.card G).factorization p :=
    natCard_eq_pow_factorization_of_normalizer_le hp
      (natCard_hallCoreOf_eq_pow_factorization hp hsemi₁ hsemi₂ hcop hcardH) (le_of_eq hnormP)
  have hcU : ∀ v ∈ U, v ≠ 1 → hallCoreOf S ⊓ centralizer ({v} : Set G) = ⊥ := fun v hv hv1 =>
    inf_centralizer_singleton_eq_bot_of_forall_invariant hUab (hc.le_M_E.trans hSP)
      (by simpa [hallCoreIn_eq_hallCoreOf] using hirr.2) hfaith hv hv1
  have hsetup := isSylowCorePrimeSetup_of_pConfiguration hp hcardPG hHne hUne hc hnormP hTIH hcU
  by_contra hcoprime
  have hdvd : p ∣ orderOf g := by
    by_contra hnd
    exact hcoprime (Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hnd))
  rcases hsetup.mem_conjugatesOfSet_punctured_union hdvd with h | h
  · exact hgP (by rwa [sat_sharp_eq_conjugatesOfSet, hallCoreIn_eq_hallCoreOf])
  · exact hgW (by rwa [sat_sharp_eq_conjugatesOfSet, sup_comm W₁ W₂])

end

end CFSG.FeitThompson.Proofs
