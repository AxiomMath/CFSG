module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.OddOrder.PartnerKernelPrimeOverlapCover
import CFSG.FeitThompson.Representations.TypeIIIVExtendedDadeSupport
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.OddOrder.PartnerKernelMixedTICardinalBound
import CFSG.FeitThompson.OddOrder.PacketBoundInverseDadeContradiction
import CFSG.FeitThompson.OddOrder.TypeIIIVCoreAbelianizationBound
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.Representations.TypeVMaximalExclusion
import CFSG.FeitThompson.Representations.UniformLocalBridgePuncturedSupportNorm
import CFSG.FeitThompson.Representations.CoprimeValueBoundInverseDadeNorm
import all CFSG.FeitThompson.Representations.UniformLocalBridgePuncturedSupportNorm
import all CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import Mathlib.GroupTheory.FixedPointFree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise CFSG.FeitThompson.Prep06

variable {G : Type*} [Group G]

def coprimeExceptionOf [Finite G] (M W₁ : Subgroup G) : Set G :=
  {g | g ∉ dadeDeltaM M ∧ ¬ (orderOf g).Coprime (Nat.card ↥W₁)}

theorem mem_coprimeExceptionOf [Finite G] {M W₁ : Subgroup G} {g : G} :
    g ∈ coprimeExceptionOf M W₁ ↔
      g ∉ dadeDeltaM M ∧ ¬ (orderOf g).Coprime (Nat.card ↥W₁) := Iff.rfl

theorem coprimeExceptionOf_subset [Finite G] (M W₁ : Subgroup G) :
    coprimeExceptionOf M W₁ ⊆ {g : G | 1 < Nat.gcd (orderOf g) (Nat.card ↥W₁)} := by
  intro g hg
  have hpos : 0 < Nat.gcd (orderOf g) (Nat.card ↥W₁) :=
    Nat.pos_of_ne_zero fun h0 =>
      absurd (Nat.eq_zero_of_gcd_eq_zero_right h0) (Nat.card_pos (α := ↥W₁)).ne'
  exact lt_of_le_of_ne hpos (Ne.symm hg.2)

theorem three_le_natCard_of_ne_bot [Finite G] {X : Subgroup G} (hodd : Odd (Nat.card G))
    (hX : X ≠ ⊥) : 3 ≤ Nat.card ↥X := by
  have h1 : 1 < Nat.card ↥X := (Subgroup.one_lt_card_iff_ne_bot X).2 hX
  obtain ⟨k, hk⟩ : Odd (Nat.card ↥X) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card X)
  omega

theorem isTIWithNormalizer_of_subset {D D' : Set G} {L : Subgroup G}
    (h : IsTIWithNormalizer D' L) (hsub : D ⊆ D') (hne : D.Nonempty) (h1 : (1 : G) ∉ D)
    (hstab : ∀ g ∈ L, MulAut.conj g '' D = D) : IsTIWithNormalizer D L where
  nonempty := hne
  one_notMem := h1
  normalizer_eq := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · by_contra hgL
      have hd : Disjoint D (MulAut.conj g '' D) :=
        (h.disjoint_conj_image g hgL).mono hsub (Set.image_mono hsub)
      rw [Subgroup.mem_normalizer_iff_conj_image_eq.1 hg] at hd
      exact hne.ne_empty (disjoint_self.mp hd)
    · exact Subgroup.mem_normalizer_iff_conj_image_eq.2 (hstab g hg)
  disjoint_conj_image := fun g hg =>
    (h.disjoint_conj_image g hg).mono hsub (Set.image_mono hsub)

theorem conj_image_hallCoreSharp {N : Subgroup G} {g : G} (hg : g ∈ N) :
    MulAut.conj g '' hallCoreSharp N = hallCoreSharp N := by
  have hnorm : MulAut.conj g '' (((hallCore N).map N.subtype : Subgroup G) : Set G)
      = (((hallCore N).map N.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_conj_image_eq.1 (le_normalizer_map_subtype_hallCore N hg)
  rw [hallCoreSharp_eq, Set.image_sdiff (MulAut.conj g).injective, hnorm]
  simp

section Partner

variable [Finite G] {N E W₁ W₂ : Subgroup G}

theorem isTIWithNormalizer_hallCoreSharp
    (hti : IsTIWithNormalizer (fittingRawSharp N) N)
    (hcN : IsWitnessedPConfiguration N E W₂ W₁) :
    IsTIWithNormalizer (hallCoreSharp N) N :=
  isTIWithNormalizer_of_subset hti (hallCoreSharp_subset_fittingRawSharp N)
    hcN.hallCoreSharp_nonempty (one_notMem_hallCoreSharp N)
    (fun _ hg => conj_image_hallCoreSharp hg)

theorem isFrobeniusPartnerConfig_of_typeII
    (hti : IsTIWithNormalizer (fittingRawSharp N) N)
    (hEbot : E ≠ ⊥)
    (hhall : (Nat.card ↥((hallCore ↥N).map N.subtype)).Coprime
      ((hallCore ↥N).map N.subtype).index)
    (hcN : IsWitnessedPConfiguration N E W₂ W₁)
    (hfree : ∀ e ∈ E, e ≠ 1 →
      (hallCore ↥N).map N.subtype ⊓ centralizer ({e} : Set G) = ⊥) :
    IsFrobeniusPartnerConfig N ((hallCore ↥N).map N.subtype) E (⁅N, N⁆ : Subgroup G) W₁ W₂ := by
  have hKnormal := normal_subgroupOf_commutator_self N
  have hJN : ((hallCore ↥N).map N.subtype) ≤ N := Subgroup.map_subtype_le _
  have hEN : E ≤ N := hcN.le_M_E
  have hnormJ : N ≤ normalizer (((hallCore ↥N).map N.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore N
  have hnormK : N ≤ normalizer ((⁅N, N⁆ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.commutator_le_self N)
  have hTIJ := isTIWithNormalizer_hallCoreSharp hti hcN
  have hKeq : ((⁅N, N⁆ : Subgroup G) : Set G)
      = (((hallCore ↥N).map N.subtype : Subgroup G) : Set G) * (E : Set G) := by
    have h := Subgroup.coe_mul_of_right_le_normalizer_left ((hallCore ↥N).map N.subtype) E
      (hEN.trans hnormJ)
    rw [hcN.sup_hallCore_E] at h
    exact h
  have hNeq : (N : Set G) = ((⁅N, N⁆ : Subgroup G) : Set G) * (W₂ : Set G) := by
    have h := Subgroup.coe_mul_of_right_le_normalizer_left (⁅N, N⁆ : Subgroup G) W₂
      (hcN.le_M_W₁.trans hnormK)
    rw [hcN.sup_commutator_W₁] at h
    exact h
  refine
    { ne_bot_H := hcN.hallCore_ne_bot
      ne_bot_U := hEbot
      ne_bot_W1 := hcN.ne_bot_W₂
      ne_bot_W2 := hcN.ne_bot_W₁
      le_N_H := hJN
      normal_subgroupOf_H := ?_
      disjoint_H_U := hcN.disjoint_hallCore_E
      coe_K_eq := hKeq
      normal_subgroupOf_K := hKnormal
      coe_N_eq := hNeq
      disjoint_K_W2 := hcN.disjoint_commutator_W₁
      coprime_natCard_K_W2 := hcN.coprime_natCard_W₁_natCard_commutator.symm
      le_normalizer_H := hcN.le_M_E.trans hnormJ
      le_normalizer_U := hcN.le_normalizer_E
      hall_H := hhall
      inf_centralizer_H_eq_bot := hfree
      le_H_W1 := hcN.le_hallCore_W₂
      inf_centralizer_K_eq_W1 := hcN.inf_centralizer_eq_W₂
      isCyclic_W1 := hcN.isCyclic_W₂
      isCyclic_W2 := hcN.isCyclic_W₁
      setOf_conj_eq_self := ?_
      inter_conj_image_eq_empty := ?_ }
  · have h : (((hallCore ↥N).map N.subtype).subgroupOf N) = hallCore ↥N :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [h]; exact hallCore_normal
  · rw [← hallCoreSharp_eq N, setOf_conj_eq_self_eq_normalizer, hTIJ.normalizer_eq]
  · intro g hg
    have h := hTIJ.disjoint_image_conj_inv hg
    rw [hallCoreSharp_eq] at h
    exact Set.disjoint_iff_inter_eq_empty.1 h

theorem fixedPointFree_conjOnNormalized_E
    (hcN : IsWitnessedPConfiguration N E W₂ W₁) {w : ↥W₂} (hw : w ≠ 1) :
    MonoidHom.FixedPointFree (conjOnNormalized E hcN.le_normalizer_E w) := by
  intro d hd
  have hw1 : (w : G) ≠ 1 := fun hcon => hw (Subtype.ext hcon)
  have hcomm : (w : G) * (d : G) * (w : G)⁻¹ = (d : G) := by
    have := congrArg (fun z : ↥E => (z : G)) hd
    simpa [conjOnNormalized_apply_coe] using this
  have hcen : (d : G) ∈ (⁅N, N⁆ : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hcN.le_commutator_E d.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc (w : G) * (d : G) = ((w : G) * (d : G) * (w : G)⁻¹) * (w : G) := by group
      _ = (d : G) * (w : G) := by rw [hcomm]
  rw [hcN.inf_centralizer_eq_W₂ (w : G) w.2 hw1] at hcen
  have hmem : (d : G) ∈ ((hallCore ↥N).map N.subtype) ⊓ E :=
    Subgroup.mem_inf.2 ⟨hcN.le_hallCore_W₂ hcen, d.2⟩
  rw [disjoint_iff.1 hcN.disjoint_hallCore_E] at hmem
  exact Subtype.ext (by simpa using hmem)

theorem natCard_W₂_dvd_natCard_E_sub_one
    (hcN : IsWitnessedPConfiguration N E W₂ W₁) :
    Nat.card ↥W₂ ∣ Nat.card ↥E - 1 :=
  card_dvd_card_sub_one_of_fixedPointFree
    (fun _ hw => fixedPointFree_conjOnNormalized_E hcN hw)

theorem seven_le_natCard_E (hodd : Odd (Nat.card G)) (hEbot : E ≠ ⊥)
    (hcN : IsWitnessedPConfiguration N E W₂ W₁) : 7 ≤ Nat.card ↥E := by
  obtain ⟨k, hk⟩ := natCard_W₂_dvd_natCard_E_sub_one hcN
  have hu : 3 ≤ Nat.card ↥E := three_le_natCard_of_ne_bot hodd hEbot
  have hp : 3 ≤ Nat.card ↥W₂ := three_le_natCard_of_ne_bot hodd hcN.ne_bot_W₁
  have hpodd : Odd (Nat.card ↥W₂) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card W₂)
  have huodd : Odd (Nat.card ↥E) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E)
  have heven : Even (Nat.card ↥E - 1) := by
    obtain ⟨a, ha⟩ := huodd; exact ⟨a, by omega⟩
  have hkeven : Even k := by
    rw [hk] at heven
    rcases (Nat.even_mul).1 heven with h | h
    · exact absurd h (Nat.not_even_iff_odd.2 hpodd)
    · exact h
  have hk2 : 2 ≤ k := by
    have hk0 : k ≠ 0 := by intro h; rw [h, Nat.mul_zero] at hk; omega
    obtain ⟨m, hm⟩ := hkeven; omega
  have hmul : 2 * Nat.card ↥W₂ ≤ Nat.card ↥W₂ * k := by
    calc 2 * Nat.card ↥W₂ = Nat.card ↥W₂ * 2 := by ring
      _ ≤ Nat.card ↥W₂ * k := Nat.mul_le_mul_left _ hk2
  omega

end Partner

theorem natCard_W₂_mul_le_natCard_commutator [Finite G] {M U W₁ W₂ : Subgroup G}
    (hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hnonab : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Nat.card ↥W₂ * (2 * Nat.card ↥W₁ + 1) ≤ Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
  obtain ⟨-, -, hbound, -⟩ :=
    natCard_W₁_bound_of_isWitnessedPConfiguration hodd hsimple hnonab hsolv hM htype hc
  set K2 : Subgroup G := ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆
  have hle : K2 ≤ (⁅M, M⁆ : Subgroup G) := Subgroup.commutator_le_self _
  have hprod : Nat.card ↥K2 * K2.relIndex (⁅M, M⁆ : Subgroup G)
      = Nat.card ↥(⁅M, M⁆ : Subgroup G) := natCard_mul_relIndex hle
  have hp : Nat.card ↥W₂ ≤ Nat.card ↥K2 :=
    Nat.card_le_card_of_injective _ (Set.inclusion_injective hc.le_commutator_commutator_W₂)
  have hidx : 2 * Nat.card ↥W₁ + 1 ≤ K2.relIndex (⁅M, M⁆ : Subgroup G) := by
    have hw1 : 1 ≤ Nat.card ↥W₁ := Nat.card_pos
    omega
  calc Nat.card ↥W₂ * (2 * Nat.card ↥W₁ + 1)
      ≤ Nat.card ↥K2 * K2.relIndex (⁅M, M⁆ : Subgroup G) := Nat.mul_le_mul hp hidx
    _ = Nat.card ↥(⁅M, M⁆ : Subgroup G) := hprod

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson CFSG.FeitThompson.Prep06

universe u

theorem measure_coprimeExceptionOf_le {G : Type u} [Group G] [Finite G]
    {M N E U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hpartner : IsFrobeniusPartnerConfig N ((hallCore ↥N).map N.subtype) E
      (⁅N, N⁆ : Subgroup G) W₁ W₂) :
    ((coprimeExceptionOf M W₁).ncard : ℝ) / (Nat.card G : ℝ)
      ≤ 1 / ((Nat.card ↥E : ℝ) * (Nat.card ↥W₂ : ℝ))
        + ((Nat.card ↥W₁ : ℝ) - 1) * ((Nat.card ↥W₂ : ℝ) - 1)
          / ((Nat.card ↥W₁ : ℝ) * (Nat.card ↥W₂ : ℝ)) := by
  have hV : cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ = cyclicTIset W₁ W₂ := cyclicTIDiff_sup_eq_cyclicTIset
  refine hpartner.measure_le_of_subset_gcd_orderOf rfl rfl rfl ?_ ?_
    (coprimeExceptionOf_subset M W₁)
  · rw [hV, setOf_conj_eq_self_eq_normalizer, hc.normalizer_cyclicTIset]
  · intro g hg
    rw [hV]
    exact Set.disjoint_iff_inter_eq_empty.1
      (hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg)

set_option maxHeartbeats 1000000 in
theorem one_sub_measure_sub_inv_lt_div
    (hdade : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (hconst : Statements.FPF_type_iii_v_local_character_constants.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsize : 2 * Nat.card ↥W₁ + 1 ≤ Nat.card ↥(⁅M, M⁆ : Subgroup G))
    (hcoh : HasCoherentMap M W₁ W₂
      (CFSG.FeitThompson.Prep06.indFamNonprincipal M (CFSG.FeitThompson.Prep06.derivedOf M))) :
    1 - ((coprimeExceptionOf M W₁).ncard : ℝ) / (Nat.card G : ℝ)
        - 1 / (Nat.card ↥W₁ : ℝ)
      < (Nat.card ↥W₁ : ℝ) / (Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ) := by
  classical
  have hfin : Finite G := Finite.of_fintype G
  have hprime : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M) :=
    hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hnK : (derivedOf M).Normal := hprime.normal
  have hsolvM : Group.IsSolvable ↥M := hG.solvable M hc.lt_top.ne
  have hsolvK : Group.IsSolvable ↥(derivedOf M) := by
    have h : derivedOf M = commutator ↥M := rfl
    rw [h]; infer_instance
  have hfameq : CFSG.FeitThompson.Prep06.indFamNonprincipal M (derivedOf M)
      = indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) := by
    rw [CFSG.FeitThompson.Prep06.indFamNonprincipal_eq, nonprincipalIrr_eq_sdiff_singleton]
  rw [hfameq] at hcoh
  have hcardW1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hmapK : Subgroup.map M.subtype (derivedOf M) = (⁅M, M⁆ : Subgroup G) :=
    CFSG.FeitThompson.Prep06.map_subtype_derivedOf M
  have hcardK : Nat.card ↥(derivedOf M) = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    rw [← hmapK]
    exact Nat.card_eq_of_bijective _
      (Subgroup.equivMapOfInjective (derivedOf M) M.subtype M.subtype_injective).bijective
  obtain ⟨⟨σ, hσ⟩, -, hconsts⟩ := hconst G hG M U W₁ W₂ hM htype hc
  set w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :=
    fun i j => hprime.isCyclicTIPair.basisProdIrr (i, j) with hw
  set l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ := fun i => hprime.inflateLeft i with hl
  have hrow : IsRowData M W₁ W₂ σ w l := by
    refine { isometry := hσ, prod := ?_, infl := ?_ }
    · intro i j x y z hz
      rw [hw, hprime.isCyclicTIPair.coe_basisProdIrr_apply]
      have h6 := hprime.isCyclicTIPair.prodChar_apply_mul (i : ↥(W₁.subgroupOf M) → ℂ)
        (j : ↥(W₂.subgroupOf M) → ℂ) x.2 y.2
      convert h6 using 2
      exact Subtype.ext hz
    · intro i k v z hz
      subst hz
      exact hprime.inflateLeft_apply_mul i k.2 v.2
  set sg : ↑(Irr ↥(W₂.subgroupOf M)) → ℂ := fun j => hprime.primeTISign σ j with hsg
  set mu : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) → ↥M → ℂ :=
    fun i j => hprime.primeTIirr σ i j with hmu
  have hsetup : IsRowSetup M W₁ W₂ σ w l sg mu := by
    refine { toIsRowData := hrow, sign := ?_, mu_zero_mem := ?_, mu_eq := ?_ }
    · intro j; exact hprime.primeTISign_eq_one_or_eq_neg_one j
    · intro j
      have h4 := hprime.primeTIirr_principal_left_mem_Irr hσ j
      rw [hprime.primeTIirr_principal_left] at h4
      exact h4
    · intro i j
      change hprime.primeTIirr σ i j = _
      rw [hprime.primeTIirr_eq_mul i j, hprime.primeTIirr_principal_left]
  obtain ⟨d, n, dsign, hdodd, hd1, hdsign, hneven, hn2, hmu1, hsgj, hsubeq⟩ :=
    hconsts σ w l sg mu hsetup
  set δZ : ℤ := if dsign = 1 then 1 else -1 with hδZ
  have hδZcast : ((δZ : ℤ) : ℂ) = dsign := by
    rcases hdsign with h | h
    · simp [hδZ, h]
    · rw [hδZ, h]; norm_num
  have hδZsign : δZ = 1 ∨ δZ = -1 := by
    rcases hdsign with h | h
    · left; simp [hδZ, h]
    · right; rw [hδZ, h]; norm_num
  have hsubZ : (d : ℤ) - δZ = (n : ℤ) * (Nat.card ↥(W₁.subgroupOf M) : ℤ) := by
    have h2 : (((d : ℤ) - δZ : ℤ) : ℂ)
        = (((n : ℤ) * (Nat.card ↥(W₁.subgroupOf M) : ℤ) : ℤ) : ℂ) := by
      push_cast
      rw [hδZcast, hcardW1]
      exact_mod_cast hsubeq
    exact_mod_cast h2
  have hKbot : derivedOf M ≠ ⊥ := by
    intro h
    have h2 := hc.ne_bot_commutator
    rw [← hmapK, h] at h2
    simp at h2
  have hfix : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset (derivedOf M) (W₁.subgroupOf M) :=
    hc.fixesOnlyCommutatorCoset_subgroupOf hG.odd
  obtain ⟨ζ, hζmem⟩ := FrobeniusQuotientLayer.kerLayerIndFam_commutator_nonempty
    (K := derivedOf M) (L := ↥M) hKbot
  have hζIrr : ζ ∈ Irr ↥M :=
    FrobeniusQuotientLayer.kerLayerIndFam_commutator_subset_Irr hprime.mul_eq_univ hfix hζmem
  have hζ1 : ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ) :=
    FrobeniusQuotientLayer.apply_one_eq_card_of_mem_kerLayerIndFam_commutator
      hprime.mul_eq_univ hprime.inf_eq_bot hζmem
  have hζfam : ζ ∈ indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) := by
    obtain ⟨θ, hθ, hθe⟩ := NormalInducedFamily.mem_kerLayerIndFam.1 hζmem
    obtain ⟨hθ1, -, hθ3⟩ := NormalInducedFamily.mem_kerLayerIrr.1 hθ
    exact hθe ▸ Set.mem_image_of_mem (indClassFun (derivedOf M))
      (show θ ∈ Irr ↥(derivedOf M) \ {1} from ⟨hθ1, hθ3⟩)
  have hA8 : ∀ (i : ↑(Irr ↥(W₁.subgroupOf M))) (j : ↑(Irr ↥(W₂.subgroupOf M))),
      j ≠ principalIrr ↥(W₂.subgroupOf M) → hprime.primeTIirr σ i j 1 = ((d : ℤ) : ℂ) := by
    intro i j hj
    have h3 := hmu1 i j hj
    change hprime.primeTIirr σ i j 1 = _ at h3
    rw [h3]; push_cast; ring
  have hA9 : ∀ (j : ↑(Irr ↥(W₂.subgroupOf M))), j ≠ principalIrr ↥(W₂.subgroupOf M) →
      hprime.primeTISign σ j = ((δZ : ℤ) : ℂ) := by
    intro j hj
    have h3 := hsgj j hj
    change hprime.primeTISign σ j = _ at h3
    rw [h3, hδZcast]
  have hlocal : hprime.IsUniformBridgeData σ ζ (d : ℤ) (n : ℤ) δZ :=
    ⟨hσ, hζfam, hζIrr, hζ1, by exact_mod_cast hd1, by exact_mod_cast hn2, hδZsign, hA8, hA9, hsubZ⟩
  obtain ⟨-, -, -, hDD, -⟩ := hdade G hG M U W₁ W₂ hM htype hc
  have hsup : Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M) = W₁ ⊔ W₂ := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hc.le_M_W₁, map_subgroupOf_eq_of_le hc.le_M_W₂]
  have hpair : IsCyclicTIPair (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
      (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M)) := by
    refine hprime.isCyclicTIPair_map_subtype ?_ ?_
    · rw [hsup, map_subgroupOf_eq_of_le hc.le_M_W₁, map_subgroupOf_eq_of_le hc.le_M_W₂,
        cyclicTIDiff_sup_eq_cyclicTIset, setOf_conj_eq_self_eq_normalizer,
        hc.normalizer_cyclicTIset]
    · intro g hg
      rw [hsup, map_subgroupOf_eq_of_le hc.le_M_W₁, map_subgroupOf_eq_of_le hc.le_M_W₂,
        cyclicTIDiff_sup_eq_cyclicTIset]
      rw [hsup] at hg
      exact Set.disjoint_iff_inter_eq_empty.1
        (hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg).symm
  obtain ⟨ω, hω⟩ := hpair.exists_isCyclicTIIsometry
  have hcTI : ∀ a : ↥M, a ∈ cyclicTIset (W₁.subgroupOf M) (W₂.subgroupOf M) →
      (a : G) ∈ cyclicTIset W₁ W₂ := by
    intro a ha
    obtain ⟨hmem, hn1, hn2'⟩ := mem_cyclicTIset.1 ha
    exact mem_cyclicTIset.2 ⟨by rw [← hsup]; exact ⟨a, hmem, rfl⟩, hn1, hn2'⟩
  have hbsub : primeTIbridgeSupport (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      = ((derivedOf M : Set ↥M) \ {1})
        ∪ Group.conjugatesOfSet (cyclicTIset (W₁.subgroupOf M) (W₂.subgroupOf M)) := rfl
  have himg : (fun x : ↥M => (x : G)) '' primeTIbridgeSupport (derivedOf M)
      (W₁.subgroupOf M) (W₂.subgroupOf M) ⊆ dadeA0 M W₁ W₂ := by
    rintro g ⟨x, hx, rfl⟩
    rw [dadeA0_eq]
    rw [hbsub] at hx
    rcases hx with hx1 | hx1
    · refine Or.inl ⟨?_, ?_⟩
      · rw [← hmapK]; exact ⟨x, hx1.1, rfl⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hx1.2 (by simp [Subtype.ext_iff, h])
    · right
      rw [Group.mem_conjugatesOfSet_iff] at hx1
      obtain ⟨a, ha, hconj⟩ := hx1
      obtain ⟨m, hm⟩ := isConj_iff.1 hconj
      refine CFSG.FeitThompson.Proofs.mem_mixedConj.2
        ⟨((m : G))⁻¹, M.inv_mem m.2, (a : G), hcTI a ha, ?_⟩
      have hx2 : ((m * a * m⁻¹ : ↥M) : G) = (x : G) := by rw [hm]
      push_cast at hx2
      simpa using hx2
  obtain ⟨ν, hνinner, hνtau⟩ := hcoh
  have hνeq : ∀ (f : ↥(Submodule.span ℤ (indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}))))
      (F : ↥(dadeDomain M (dadeA0 M W₁ W₂))), (f : ↥M → ℂ) = (F : ↥M → ℂ) →
      ((ν f : G → ℂ)) = ((dadeMap hDD F : G → ℂ)) := by
    intro f F hfF
    have hF1 : (F : ↥M → ℂ) 1 = 0 := by
      refine (mem_dadeDomain.1 F.2).2 1 ?_
      intro h
      have h5 := hDD.subset_sdiff h
      simp at h5
    have hf1 : (f : ↥M → ℂ) 1 = 0 := by rw [hfF]; exact hF1
    rw [hνtau f hf1, coe_dadeMap hDD F, ← hfF, dadeTau_eq]
  have hCD : IsUniformBridgeCoherenceData hprime σ ζ (d : ℤ) (n : ℤ) δZ
      (dadeA0 M W₁ W₂) (dadeT M) ω ν :=
    ⟨hlocal, hG.odd, hDD, himg, hpair, hω, hνinner, hνeq⟩
  have hconc := hCD.one_sub_sub_inv_lt_div (by rw [hcardW1, hcardK]; exact hsize)
  have hset : coprimeExceptionSet (derivedOf M) (W₁.subgroupOf M) (dadeT M)
      = coprimeExceptionOf M W₁ := by
    have hpc : puncturedCoreSet (derivedOf M) = ((⁅M, M⁆ : Subgroup G) : Set G) \ {1} := by
      rw [puncturedCoreSet_def]
      have h : ((fun x : ↥M => (x : G))) = M.subtype := rfl
      rw [h, Set.image_sdiff M.subtype_injective]
      rw [show (M.subtype '' (derivedOf M : Set ↥M)) = ((⁅M, M⁆ : Subgroup G) : Set G) from by
        rw [← hmapK]; rfl]
      simp
    ext g
    rw [mem_coprimeExceptionSet, hpc, ← dadeDeltaM_eq M, hcardW1]
    exact Iff.rfl
  rw [hset, hcardW1, hcardK] at hconc
  exact hconc

theorem FPF_type_iii_v_frobenius_partner_contradiction
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₃ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (h₄ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u}) :
    Statements.FPF_type_iii_v_frobenius_partner_contradiction.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc N E hN htypeII hcN hfree hcoh
  have hfin : Finite G := Finite.of_fintype G
  have hamb2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    { odd_natCard := hG.odd, isSimpleGroup := hG.simple,
      not_isMulCommutative := hG.nonabelian, isSolvable_of_ne_top := hG.solvable }
  have hamb5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    { odd_natCard := hG.odd, isSimpleGroup := hG.simple,
      not_isMulCommutative := hG.nonabelian, isSolvable_of_ne_top := hG.solvable }
  obtain ⟨hIIIV, hEbot, -, -, -, -⟩ :=
    htypeII.clauses_of_isWitnessedPConfiguration (hG.solvable N hN.1) hcN
  have hhall : (Nat.card ↥((hallCore ↥N).map N.subtype)).Coprime
      ((hallCore ↥N).map N.subtype).index := by
    have hS : sigmaCore N = CFSG.FeitThompson.Prep05.hallCoreOf N :=
      (h₂ G hamb5 N hN).1 htypeII
    obtain ⟨-, hHall, -⟩ := FBG_sigma_core_normal_hall G hamb2 N hN
    rw [hS, CFSG.FeitThompson.Prep05.hallCoreOf_eq] at hHall
    exact hHall.coprime_natCard_index
  have hpartner := isFrobeniusPartnerConfig_of_typeII
    hIIIV.isTIWithNormalizer_fittingRawSharp hEbot hhall hcN hfree
  have hmeasure := measure_coprimeExceptionOf_le hc hpartner
  have hsize := natCard_W₂_mul_le_natCard_commutator hG.odd hG.simple hG.nonabelian
    hG.solvable hM htype hc
  have hp3 : 3 ≤ Nat.card ↥W₂ := three_le_natCard_of_ne_bot hG.odd hc.ne_bot_W₂
  have he3 : 3 ≤ Nat.card ↥W₁ := three_le_natCard_of_ne_bot hG.odd hc.ne_bot_W₁
  have hu7 : 7 ≤ Nat.card ↥E := seven_le_natCard_E hG.odd hEbot hcN
  have hsizeN : 2 * Nat.card ↥W₁ + 1 ≤ Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    have : 1 * (2 * Nat.card ↥W₁ + 1) ≤ Nat.card ↥W₂ * (2 * Nat.card ↥W₁ + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hlt := one_sub_measure_sub_inv_lt_div
    (FPF_type_iii_v_extended_dade_support h₁ h₂ h₄ h₅)
    (FPF_type_iii_v_local_character_constants h₃) hG hM htype hc hsizeN hcoh
  refine not_exists_packet_bound_and_lt_div
    (e := (Nat.card ↥W₁ : ℝ)) (p := (Nat.card ↥W₂ : ℝ)) (u := (Nat.card ↥E : ℝ))
    (h := (Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ))
    (by exact_mod_cast he3) (by exact_mod_cast (by omega : 0 < Nat.card ↥W₂))
    (by exact_mod_cast hu7) ?_ ⟨_, hmeasure, hlt⟩
  calc (Nat.card ↥W₂ : ℝ) * (2 * (Nat.card ↥W₁ : ℝ) + 1)
      = ((Nat.card ↥W₂ * (2 * Nat.card ↥W₁ + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ) := by exact_mod_cast hsize

end CFSG.FeitThompson.Proofs
