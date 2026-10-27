module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.TypeIFrobeniusCoherentFamily
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.Representations.FreeCentralSectionTISylowRestriction

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem not_isTypeI_of_isTypeII_or_isTypeIII [Finite G]
    (hclass : ∀ M : Subgroup G, IsCoatom M → ∃! i : Fin 5, localTypes M i)
    {M : Subgroup G} (hM : IsCoatom M) (h : IsTypeII M ∨ IsTypeIII M) : ¬ IsTypeI M := by
  intro h1
  obtain ⟨i, -, huniq⟩ := hclass M hM
  have h0 : (0 : Fin 5) = i := huniq 0 (by simpa using h1)
  rcases h with h | h
  · have := huniq 1 (by simpa using h); simp [← h0] at this
  · have := huniq 2 (by simpa using h); simp [← h0] at this

theorem exists_prime_dvd_natCard_hallCoreIn_and_orderOf [Finite G] {L : Subgroup G}
    (hD : IsDadeData L ((Prep03.hallCoreIn L : Set G) \ {1}) Prep03.sigR)
    {x : G} (hx : x ∈ Prep03.hallDadeSupport L) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card ↥(Prep03.hallCoreIn L) ∧ r ∣ orderOf x := by
  obtain ⟨a, ha, hxa⟩ := mem_totalDadeSupport_iff.1 hx
  obtain ⟨y, hy, hconj⟩ := mem_dadeSupport_iff.1 hxa
  set u : G := y * a⁻¹ with hudef
  have hu : u ∈ Prep03.sigR a := mem_dadeCoset_iff.1 hy
  have hcomm : Commute u a := (((hD.le_centralizer ha) hu) a rfl).symm
  have hcop : Nat.Coprime (orderOf u) (orderOf a) := by
    refine Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hu) ?_
    refine Nat.Coprime.coprime_dvd_right ?_ (hD.coprime_card ha ha)
    exact Subgroup.orderOf_dvd_natCard _ ⟨hD.mem_of_mem ha, mem_centralizer_singleton_iff.2 rfl⟩
  have hy' : y = u * a := by rw [hudef]; group
  have hord : orderOf a ∣ orderOf x := by
    have h2 : orderOf y = orderOf u * orderOf a := by
      rw [hy']; exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [← orderOf_eq_of_isConj hconj, h2]
    exact Dvd.intro_left _ rfl
  have ha1 : a ≠ 1 := by simpa using ha.2
  have hane : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.1 h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hane
  exact ⟨r, hr, hrdvd.trans (Subgroup.orderOf_dvd_natCard _ ha.1), hrdvd.trans hord⟩

theorem orderOf_dvd_natCard_of_mem_sat [Finite G] {X : Subgroup G} {x : G}
    (hx : x ∈ Prep03.sat (X : Set G)) : orderOf x ∣ Nat.card ↥X := by
  obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
  have h : IsConj y (g⁻¹ * y * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  rw [← orderOf_eq_of_isConj h]
  exact Subgroup.orderOf_dvd_natCard _ hy

theorem FCH_type_I_P_packet_separation
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FNI_type_p_prime_factors.{u})
    (h₄ : Statements.FPF_type_I_frobenius.{u})
    (h₅ : Statements.FTS_sigma_prime_separation.{u})
    (h₆ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FCH_type_I_P_packet_separation.{u} := by
  classical
  intro G _ _ hG S U W₁ W₂ hcfg L hL hI
  have _ : IsSimpleGroup G := hG.isSimpleGroup
  have hG1 : IsFBGAmbient G :=
    { odd_natCard := hG.odd_natCard
      isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      isSolvable := hG.forall_isSolvable }
  have hG5 : Prep05.IsMinimalSimpleOdd G :=
    { odd_natCard := hG.odd_natCard
      isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      isSolvable_of_ne_top := hG.forall_isSolvable }
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    { odd_natCard := hG.odd_natCard
      isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      isSolvable_of_ne_top := hG.forall_isSolvable }
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set q : ℕ := Nat.card ↥W₁ with hqdef
  obtain ⟨hclass, -⟩ := h₁ G hG1
  obtain ⟨hStype, hp, hq, -, -, -, -, -, -, -, -, -, -, hScard, -⟩ :=
    h₂ G hG5 S U W₁ W₂ hcfg.isCoatom hcfg.config p q rfl rfl
  obtain ⟨-, -, -, -, -, T, hT, -, V, -, hTcfg, -⟩ :=
    h₃ G hG5 S U W₁ W₂ hcfg.isCoatom hcfg.config p q rfl rfl
  obtain ⟨hTtype, -, -, -, -, -, -, -, -, -, -, -, -, hTcard, -⟩ :=
    h₂ G hG5 T V W₂ W₁ hT hTcfg q p rfl rfl
  obtain ⟨-, hsigL, -, -, -, hdade, -⟩ :=
    FCH_type_I_frobenius_coherent_family h₄ h₆ G hG L hL hI
  have hnotI : ∀ M : Subgroup G, IsCoatom M → (IsTypeII M ∨ IsTypeIII M) →
      ∀ g : G, M ≠ Prep09.conjSub g L := by
    intro M hM hMt g hEq
    exact not_isTypeI_of_isTypeII_or_isTypeIII hclass hM hMt (hEq ▸ hI.conj g)
  have hpS : p ∈ sigmaPrimes S := by
    refine mem_sigmaPrimes_of_dvd_natCard_hallCore hcfg.isCoatom hp ?_
    have h : Nat.card ↥(hallCore ↥S) = p ^ q := by
      rw [← Subgroup.card_subtype S (hallCore ↥S)]; exact hScard
    rw [h]
    exact dvd_pow_self p hq.pos.ne'
  have hqT : q ∈ sigmaPrimes T := by
    refine mem_sigmaPrimes_of_dvd_natCard_hallCore hT hq ?_
    have h : Nat.card ↥(hallCore ↥T) = q ^ p := by
      rw [← Subgroup.card_subtype T (hallCore ↥T)]; exact hTcard
    rw [h]
    exact dvd_pow_self q hp.pos.ne'
  have hsepS : sigmaPrimes L ∩ sigmaPrimes S = ∅ :=
    h₅ G hG9 L S hL hcfg.isCoatom (hnotI S hcfg.isCoatom hStype)
  have hsepT : sigmaPrimes L ∩ sigmaPrimes T = ∅ :=
    h₅ G hG9 L T hL hT (hnotI T hT hTtype)
  have hmemL : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(Prep03.hallCoreIn L) → r ∈ sigmaPrimes L := by
    intro r hr hrd
    refine mem_sigmaPrimes_of_dvd_natCard_hallCore hL hr ?_
    rwa [← Subgroup.card_subtype L (hallCore ↥L)]
  have hpnd : ¬ p ∣ Nat.card ↥(Prep03.hallCoreIn L) := by
    intro hd
    have h : p ∈ sigmaPrimes L ∩ sigmaPrimes S := ⟨hmemL p hp hd, hpS⟩
    rw [hsepS] at h
    exact h
  have hqnd : ¬ q ∣ Nat.card ↥(Prep03.hallCoreIn L) := by
    intro hd
    have h : q ∈ sigmaPrimes L ∩ sigmaPrimes T := ⟨hmemL q hq hd, hqT⟩
    rw [hsepT] at h
    exact h
  have hcop : Nat.Coprime (Nat.card ↥(Prep03.hallCoreIn L)) (p * q) :=
    Nat.Coprime.mul_right ((hp.coprime_iff_not_dvd.2 hpnd).symm)
      ((hq.coprime_iff_not_dvd.2 hqnd).symm)
  have hWcard : Nat.card ↥(W₁ ⊔ W₂ : Subgroup G) = q * p :=
    hcfg.config.isInternalDirectProduct_sup.card_eq_mul
  have hdisj : Prep03.hallDadeSupport L ∩
      (Prep03.sat (Prep03.hallCoreIn S : Set G) ∪
        Prep03.sat ((W₁ ⊔ W₂ : Subgroup G) : Set G)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x ⟨hxD, hxS⟩ => ?_
    obtain ⟨r, hr, hrh, hrx⟩ := exists_prime_dvd_natCard_hallCoreIn_and_orderOf hdade hxD
    rcases hxS with hxS | hxS
    · have hdv : orderOf x ∣ p ^ q := by
        have h := orderOf_dvd_natCard_of_mem_sat hxS
        rwa [show Nat.card ↥(Prep03.hallCoreIn S) = p ^ q from hScard] at h
      have h : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow (hrx.trans hdv))
      exact hpnd (h ▸ hrh)
    · have hdv : orderOf x ∣ q * p := hWcard ▸ orderOf_dvd_natCard_of_mem_sat hxS
      rcases (Nat.Prime.dvd_mul hr).1 (hrx.trans hdv) with h | h
      · exact hqnd ((Nat.prime_dvd_prime_iff_eq hr hq).1 h ▸ hrh)
      · exact hpnd ((Nat.prime_dvd_prime_iff_eq hr hp).1 h ▸ hrh)
  refine ⟨hcop, hdisj, fun f _ x hx => ?_⟩
  refine dadeSupportExtension_eq_zero_of_notMem fun hxD => ?_
  exact Set.eq_empty_iff_forall_notMem.1 hdisj x ⟨hxD, hx⟩

end

end CFSG.FeitThompson.Proofs
