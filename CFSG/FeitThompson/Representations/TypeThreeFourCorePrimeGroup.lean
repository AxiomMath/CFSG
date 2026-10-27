module

public import CFSG.FeitThompson.Local.TypeIIIIVChiefData
import CFSG.FeitThompson.Local.CoreCentralizerTypeIIIOrIVDerived
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.FrobeniusWielandtFixedPointOrder
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.CentralRankThreeConstrainedTransitivity
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.OddOrder.ChiefFactorFixedLineDimension
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise Prep06
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.ChiefFactorFixedLine

universe u

variable {G : Type*} [Group G]

theorem range_comp_top_subtype {X Y : Type*} [Group X] [Group Y] (f : X →* Y) :
    (f.comp (⊤ : Subgroup X).subtype).range = f.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨(x : X), rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨⟨x, mem_top x⟩, rfl⟩

theorem natCard_eq_natCard_centralizer_mul_pow [Finite G] {H U W : Subgroup G}
    (hAn : (U ⊔ W : Subgroup G) ≤ normalizer (H : Set G))
    (hsolvH : Group.IsSolvable ↥H) (hsolvA : Group.IsSolvable ↥(U ⊔ W : Subgroup G))
    (hcop : (Nat.card ↥(U ⊔ W : Subgroup G)).Coprime (Nat.card ↥H))
    (hWU : W ≤ normalizer (U : Set G)) (hdisj : Disjoint U W)
    (hfree : ∀ w ∈ W, w ≠ 1 → U ⊓ centralizer {w} = ⊥)
    (hCA : H ⊓ centralizer ((U ⊔ W : Subgroup G) : Set G) = ⊥) :
    Nat.card ↥H = Nat.card ↥(H ⊓ centralizer (U : Set G)) *
      Nat.card ↥(H ⊓ centralizer (W : Set G)) ^ Nat.card ↥W := by
  have := hsolvH
  have := hsolvA
  have hUA : U ≤ (U ⊔ W : Subgroup G) := le_sup_left
  have hWA : W ≤ (U ⊔ W : Subgroup G) := le_sup_right
  set ρ : ↥(U ⊔ W : Subgroup G) →* MulAut ↥H := conjOnNormalized H hAn with hρ
  have hC : ∀ w ∈ W.subgroupOf (U ⊔ W : Subgroup G), w ≠ 1 →
      U.subgroupOf (U ⊔ W : Subgroup G) ⊓ centralizer {w} = ⊥ := by
    intro w hw hw1
    rw [Subgroup.mem_subgroupOf] at hw
    rw [show w = (⟨(w : G), w.2⟩ : ↥(U ⊔ W : Subgroup G)) from rfl,
      centralizer_subgroupOf w.2, hfree (w : G) hw (fun h => hw1 (Subtype.ext h)),
      bot_subgroupOf]
  have key := natCard_mul_natCard_fixedPoints_range_pow_natCard_eq ρ hcop
    (normal_subgroupOf_sup hWU) (isComplement'_subgroupOf_sup hWU hdisj) hC
  have hfixU : Nat.card ↥(FixedPoints.subgroup
      ↥((ρ.comp (U.subgroupOf (U ⊔ W : Subgroup G)).subtype).range) ↥H)
      = Nat.card ↥(H ⊓ centralizer (U : Set G)) := by
    rw [← map_subtype_fixedPoints_conjOnNormalized_subgroupOf hAn hUA]
    exact (card_map_of_injective H.subtype_injective).symm
  have hfixW : Nat.card ↥(FixedPoints.subgroup
      ↥((ρ.comp (W.subgroupOf (U ⊔ W : Subgroup G)).subtype).range) ↥H)
      = Nat.card ↥(H ⊓ centralizer (W : Set G)) := by
    rw [← map_subtype_fixedPoints_conjOnNormalized_subgroupOf hAn hWA]
    exact (card_map_of_injective H.subtype_injective).symm
  have hmapA : map H.subtype (FixedPoints.subgroup ↥ρ.range ↥H)
      = H ⊓ centralizer ((U ⊔ W : Subgroup G) : Set G) := by
    have h := map_subtype_fixedPoints_conjOnNormalized hAn (⊤ : Subgroup ↥(U ⊔ W : Subgroup G))
    rwa [range_comp_top_subtype, map_subtype_top'] at h
  have hfixA : FixedPoints.subgroup ↥ρ.range ↥H = ⊥ := by
    have h : map H.subtype (FixedPoints.subgroup ↥ρ.range ↥H) = ⊥ := by rw [hmapA, hCA]
    rw [Subgroup.map_eq_bot_iff, H.ker_subtype] at h
    exact le_bot_iff.1 h
  rw [hfixA, hfixU, hfixW, Subgroup.card_bot, one_pow, mul_one, natCard_subgroupOf hWA] at key
  exact key

theorem natCard_sup_dvd_mul [Finite G] {P U : Subgroup G} (hn : U ≤ normalizer (P : Set G)) :
    Nat.card ↥(P ⊔ U : Subgroup G) ∣ Nat.card ↥P * Nat.card ↥U := by
  have hcoe : ((P ⊔ U : Subgroup G) : Set G) = (P : Set G) * (U : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P U hn
  have h := natCard_mul_mul_natCard_inf P U
  rw [← hcoe] at h
  exact ⟨Nat.card ↥(P ⊓ U), h.symm⟩

theorem FPF_type_iii_iv_core_is_prime_group
    (h₁ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₂ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_core_is_prime_group.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  have hG5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set q : ℕ := Nat.card ↥W₁ with hqdef
  obtain ⟨hpprime, -, -, -, -, -, -, hsemiA, hcopA, hfpf, hcentW, -, -, -,
      ⟨H₀, hH₀CU, hlayer⟩, hall⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₂ G hG5 M U W₁ W₂ hM htype hc p q rfl rfl
  obtain ⟨-, hinfW₂, -⟩ := hall H₀ hH₀CU hlayer
  have : Fact p.Prime := ⟨hpprime⟩
  have hsolvM : Group.IsSolvable ↥M := hG.solvable M hM.1
  set Hg : Subgroup G := hallCoreOf M with hHg
  have hHgle : Hg ≤ M := hallCoreOf_le M
  have hUle : U ≤ M := hc.le_M_E
  have hW₁le : W₁ ≤ M := hc.le_M_W₁
  have hAle : (U ⊔ W₁ : Subgroup G) ≤ M := sup_le hUle hW₁le
  have hMnH : M ≤ normalizer (Hg : Set G) := by
    rw [hHg, hallCoreOf_eq]; exact le_normalizer_map_subtype_hallCore M
  have hfree : ∀ w ∈ W₁, w ≠ 1 → U ⊓ centralizer {w} = ⊥ := by
    intro w hw hw1
    have h := hfpf w hw hw1
    rwa [centralizerIn_eq,
      centralizer_coe_eq_centralizer_singleton (rfl : zpowers w = zpowers w)] at h
  have hsupHU : Hg ⊔ U = (⁅M, M⁆ : Subgroup G) := by
    rw [hHg, hallCoreOf_eq]; exact hc.sup_hallCore_E
  have hCA : Hg ⊓ centralizer ((U ⊔ W₁ : Subgroup G) : Set G) = ⊥ := by
    refine le_bot_iff.1 ?_
    calc Hg ⊓ centralizer ((U ⊔ W₁ : Subgroup G) : Set G)
        ≤ (Hg ⊓ centralizer (U : Set G)) ⊓ (Hg ⊓ centralizer (W₁ : Set G)) := by
          refine le_inf (inf_le_inf_left _ ?_) (inf_le_inf_left _ ?_)
          · exact centralizer_le (by exact_mod_cast (le_sup_left : U ≤ U ⊔ W₁))
          · exact centralizer_le (by exact_mod_cast (le_sup_right : W₁ ≤ U ⊔ W₁))
      _ ≤ H₀ ⊓ W₂ := inf_le_inf hH₀CU (le_of_eq hcentW)
      _ = ⊥ := hinfW₂
  have hnilH : Group.IsNilpotent ↥Hg := by
    rw [hHg, hallCoreOf_eq]
    exact (Group.isNilpotent_congr
      (Subgroup.equivMapOfInjective _ _ M.subtype_injective)).1 hallCore_isNilpotent
  set Pg : Subgroup G := map Hg.subtype (sylowPiPart {p} ↥Hg) with hPg
  set Rg : Subgroup G := map Hg.subtype (sylowPiPart ({p}ᶜ) ↥Hg) with hRg
  have hPgle : Pg ≤ Hg := map_subtype_le _
  have hRgle : Rg ≤ Hg := map_subtype_le _
  have hMnP : M ≤ normalizer (Pg : Set G) :=
    le_normalizer_map_subtype_of_characteristic _ hMnH
  have hMnR : M ≤ normalizer (Rg : Set G) :=
    le_normalizer_map_subtype_of_characteristic _ hMnH
  have hsupPR : Pg ⊔ Rg = Hg := by
    rw [hPg, hRg, ← Subgroup.map_sup, sylowPiPart_sup_compl, map_subtype_top']
  have hcardP : Nat.card ↥Pg = Nat.card ↥(sylowPiPart {p} ↥Hg) :=
    card_map_of_injective Hg.subtype_injective
  have hcardR : Nat.card ↥Rg = Nat.card ↥(sylowPiPart ({p}ᶜ) ↥Hg) :=
    card_map_of_injective Hg.subtype_injective
  have hcopRP : (Nat.card ↥Rg).Coprime (Nat.card ↥Pg) := by
    rw [hcardP, hcardR]; exact (coprime_natCard_sylowPiPart {p} ↥Hg).symm
  have hpnotR : ¬ p ∣ Nat.card ↥Rg := by
    intro hdvd
    have hmem : p ∈ (Nat.card ↥(sylowPiPart ({p}ᶜ) ↥Hg)).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hpprime, hcardR ▸ hdvd, Nat.card_pos.ne'⟩
    exact (isPiSubgroup_iff.1 (isPiSubgroup_sylowPiPart ({p}ᶜ) ↥Hg) p hmem) rfl
  have hsolvR : Group.IsSolvable ↥Rg := isSolvable_of_le_of_isSolvable (hRgle.trans hHgle) hsolvM
  have hsolvA : Group.IsSolvable ↥(U ⊔ W₁ : Subgroup G) :=
    isSolvable_of_le_of_isSolvable hAle hsolvM
  have hcopAR : (Nat.card ↥(U ⊔ W₁ : Subgroup G)).Coprime (Nat.card ↥Rg) :=
    hcopA.symm.coprime_dvd_right (card_dvd_of_le hRgle)
  have hRW₂ : Rg ⊓ W₂ = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard
      ((Nat.Prime.coprime_iff_not_dvd hpprime).2 hpnotR).symm)
  have hRcentW : Rg ⊓ centralizer (W₁ : Set G) = ⊥ := by
    refine le_bot_iff.1 ?_
    calc Rg ⊓ centralizer (W₁ : Set G) ≤ Rg ⊓ (Hg ⊓ centralizer (W₁ : Set G)) :=
          le_inf inf_le_left (le_inf (inf_le_left.trans hRgle) inf_le_right)
      _ ≤ Rg ⊓ W₂ := inf_le_inf_left _ (le_of_eq hcentW)
      _ = ⊥ := hRW₂
  have hRcentU : Rg ≤ centralizer (U : Set G) := by
    have hkey := natCard_eq_natCard_centralizer_mul_pow (H := Rg) (U := U) (W := W₁)
      (hAle.trans hMnR) hsolvR hsolvA hcopAR hc.le_normalizer_E hsemiA.disjoint hfree
      (le_bot_iff.1 ((inf_le_inf_right _ hRgle).trans hCA.le))
    rw [hRcentW, Subgroup.card_bot, one_pow, mul_one] at hkey
    exact (Subgroup.eq_of_le_of_card_ge (H := Rg ⊓ centralizer (U : Set G)) (K := Rg)
      inf_le_left hkey.le) ▸ inf_le_right
  have hRcentP : Rg ≤ centralizer (Pg : Set G) := by
    have h : (⁅Rg, Pg⁆ : Subgroup G) = ⊥ := by
      rw [hRg, hPg, ← Subgroup.map_commutator, Subgroup.commutator_comm,
        commutator_sylowPiPart_compl, Subgroup.map_bot]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  set S : Subgroup G := Pg ⊔ U with hS
  have hRcentS : Rg ≤ centralizer (S : Set G) := fun x hx =>
    mem_centralizer_sup (hRcentP hx) (hRcentU hx)
  have hKeq : Rg ⊔ S = (⁅M, M⁆ : Subgroup G) := by
    rw [hS, ← sup_assoc, sup_comm Rg Pg, hsupPR, hsupHU]
  have hSK : S ≤ (⁅M, M⁆ : Subgroup G) := hKeq ▸ le_sup_right
  have hRK : Rg ≤ (⁅M, M⁆ : Subgroup G) := hKeq ▸ le_sup_left
  have hKnS : (⁅M, M⁆ : Subgroup G) ≤ normalizer (S : Set G) := by
    rw [← hKeq]
    exact sup_le (hRcentS.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hK' : (⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ : Subgroup G) ≤ S ⊔ ⁅Rg, Rg⁆ :=
    commutator_le_sup_commutator_of_sup hSK hRK (by rw [sup_comm]; exact hKeq) hKnS
  have hHK' : Hg ≤ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
    obtain ⟨hKF, hHCF, -, -⟩ := h₁ G hG M U W₁ W₂ hM htype hc
    rw [hKF, ← hHCF, hHg, hallCoreOf_eq, hallCoreIn_eq]
    exact le_sup_left
  have hcopRU : (Nat.card ↥Rg).Coprime (Nat.card ↥U) :=
    (Nat.Coprime.coprime_dvd_left (card_dvd_of_le hRgle) hcopA).coprime_dvd_right
      (card_dvd_of_le (le_sup_left : U ≤ U ⊔ W₁))
  have hcopRS : (Nat.card ↥Rg).Coprime (Nat.card ↥S) :=
    Nat.Coprime.coprime_dvd_right (natCard_sup_dvd_mul (hUle.trans hMnP))
      (Nat.Coprime.mul_right hcopRP hcopRU)
  have hdisjSR : Disjoint S Rg := (Subgroup.disjoint_of_coprime_natCard hcopRS).symm
  have hRle : Rg ≤ ⁅Rg, Rg⁆ := by
    have h := hRgle.trans (hHK'.trans hK')
    calc Rg ≤ Rg ⊓ (S ⊔ ⁅Rg, Rg⁆) := le_inf le_rfl h
      _ = ⁅Rg, Rg⁆ := inf_sup_eq_of_disjoint_of_le_normalizer hdisjSR
          (Subgroup.commutator_le_self Rg)
          ((Subgroup.commutator_le_self Rg).trans
            (hRcentS.trans (Subgroup.centralizer_le_normalizer _)))
  have hRbot : Rg = ⊥ := by
    have := hsolvR
    exact eq_bot_of_isSolvable_of_le_commutator_self Rg hRle
  have hHP : Hg = Pg := by rw [← hsupPR, hRbot, sup_bot_eq]
  have hPgroup : IsPGroup p ↥Hg := by
    rw [hHP, hPg]
    refine (isPiSubgroup_singleton_iff hpprime _).1 (isPiSubgroup_iff.2 fun r hr => ?_)
    rw [hcardP] at hr
    exact isPiSubgroup_iff.1 (isPiSubgroup_sylowPiPart {p} ↥Hg) r hr
  obtain ⟨a, ha⟩ := hPgroup.exists_card_eq
  have hW₂H : W₂ ≤ Hg := by rw [hHg, hallCoreOf_eq]; exact hc.le_hallCore_W₂
  refine ⟨a, ?_, ?_⟩
  ·
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      have hdvd : p ∣ Nat.card ↥Hg := hpdef ▸ card_dvd_of_le hW₂H
      rw [ha, h, pow_zero] at hdvd
      exact hpprime.one_lt.ne' (Nat.dvd_one.1 hdvd)
    · exact h
  · rw [show hallCoreIn M = Hg from by rw [hHg, hallCoreOf_eq, hallCoreIn_eq], ha]

end

end CFSG.FeitThompson.Proofs
