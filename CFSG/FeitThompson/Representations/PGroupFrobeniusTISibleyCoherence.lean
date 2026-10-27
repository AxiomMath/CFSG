module

public import CFSG.FeitThompson.Representations.FreeCentralSectionTISylowRestriction
public import CFSG.FeitThompson.Representations.AbelianFrobeniusKernelTICoherence
public import CFSG.FeitThompson.Representations.DisjointConjugateFamiliesOrthogonalImages
import CFSG.FeitThompson.Representations.SibleyCentralLinearJoining
import CFSG.FeitThompson.Representations.JoinedLayersStrictBoundRemainingChars
import CFSG.FeitThompson.Representations.CentralLayerCoherenceExtension
import CFSG.FeitThompson.Foundations.NonabelianPGroupInvariantCentralDerived
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Representations.FreeCentralSectionCoherentLayer
import CFSG.FeitThompson.Representations.PrimeCubeLocalArrayNonlinearCharacters
import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SibleyPGroupCoherence

open Subgroup NormalLinearInduced
open scoped ComplexOrder

section Abstract

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

theorem isCoherent_of_isCoherent_subfamily {S T : Set (L → ℂ)} (hSfin : S.Finite)
    (hSIrr : S ⊆ Irr L) (hTS : T ⊆ S) (hTfin : T.Finite) (h2 : 2 ≤ T.ncard)
    {ψ : L → ℂ} (hψ : ψ ∈ T)
    (τ : charSpanZero S →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero S,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0)
    (hcoh : IsCoherent T (restrictBaseline hTS τ))
    (hdeg : ∀ χ ∈ S, ∃ d : ℤ, 0 < d ∧ χ 1 = (d : ℂ) * ψ 1)
    (hthr : ∀ χ ∈ S, 2 * ψ 1 * χ 1 < ∑ f ∈ hTfin.toFinset, f 1 ^ 2) :
    IsCoherent S τ := by
  classical
  set D : Finset (L → ℂ) := hSfin.toFinset \ hTfin.toFinset with hD
  have hDS : (D : Set (L → ℂ)) ⊆ S := by
    intro x hx
    rw [hD] at hx
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Set.Finite.coe_toFinset] at hx
    exact hx.1
  have hunion : T ∪ (D : Set (L → ℂ)) = S := by
    rw [hD]
    simp only [Finset.coe_sdiff, Set.Finite.coe_toFinset]
    rw [Set.union_sdiff_self]
    exact Set.union_eq_self_of_subset_left hTS
  have hU : T ∪ (D : Set (L → ℂ)) ⊆ S := hunion.le
  have key := isCoherent_union_coe_finset hTfin (hTS.trans hSIrr) h2 hψ τ hτiso hτ1 hTS hcoh
    D (hDS.trans hSIrr) (fun χ hχ => hdeg χ (hDS hχ)) (fun χ hχ => hthr χ (hDS hχ)) hU
  refine (isCoherent_restrictBaseline_congr hunion τ hU (subset_refl S) key).congr_baseline ?_
  intro f
  rw [restrictBaseline_apply]
  rfl

end Abstract

section Prelim

variable {G : Type*} [Group G] {p a : ℕ} {L P E : Subgroup G}

theorem subgroupOf_ne_bot (hp : p.Prime) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hPL : P ≤ L) : P.subgroupOf L ≠ ⊥ := by
  have hPbot : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have h1 : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  intro hbot
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hPL] at hbot
  exact hPbot hbot

theorem sdiff_eq_sdiff_map_subgroupOf (hPL : P ≤ L) :
    ((P : Set G) \ {1}) = (((P.subgroupOf L).map L.subtype : Subgroup G) : Set G) \ {1} := by
  rw [Subgroup.map_subgroupOf_eq_of_le hPL]

theorem isComplement'_subgroupOf (hPL : P ≤ L) (hEL : E ≤ L)
    (hnormP : L ≤ normalizer (P : Set G)) (hsup : P ⊔ E = L) (hinf : P ⊓ E = ⊥) :
    (P.subgroupOf L).IsComplement' (E.subgroupOf L) := by
  have _ : (P.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).2 hnormP
  have hsupOf : P.subgroupOf L ⊔ E.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPL hEL, hsup, Subgroup.subgroupOf_self]
  have hinfOf : P.subgroupOf L ⊓ E.subgroupOf L = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    have hmem : (x : G) ∈ P ⊓ E := Subgroup.mem_inf.2 ⟨hx1, hx2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext hmem)
  exact (isComplement'_of_sup_eq_top_of_inf_eq_bot hsupOf hinfOf).symm

theorem isTIWithNormalizer_sdiff (hp : p.Prime) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hPL : P ≤ L)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) ∩ ((P : Set G) \ {1}) = ∅) :
    IsTIWithNormalizer ((P : Set G) \ {1}) L :=
  isTIWithNormalizer_of_conj_image_eq_or_disjoint
    (sdiff_eq_sdiff_map_subgroupOf hPL ▸
      sdiff_map_nonempty (H := P.subgroupOf L) (subgroupOf_ne_bot hp ha hPcard hPL))
    (sdiff_eq_sdiff_map_subgroupOf hPL ▸ one_notMem_sdiff_map (H := P.subgroupOf L)) hTIor hstab

variable [Fintype ↥L]

theorem indFam_subset_Irr (hp : p.Prime) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hPL : P ≤ L) (hEL : E ≤ L) (hnormP : L ≤ normalizer (P : Set G))
    (hsup : P ⊔ E = L) (hinf : P ⊓ E = ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥) :
    indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)) ⊆ Irr ↥L :=
  have _ : (P.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).2 hnormP
  indFam_nonprincipalIrr_subset_Irr (subgroupOf_ne_bot hp ha hPcard hPL)
    (isComplement'_subgroupOf hPL hEL hnormP hsup hinf) (free_subgroupOf hPL hCfree)

theorem charSpanZero_le_dadeZDomain_sdiff (hp : p.Prime) (ha : 1 ≤ a)
    (hPcard : Nat.card ↥P = p ^ a)
    (hPL : P ≤ L) (hEL : E ≤ L) (hnormP : L ≤ normalizer (P : Set G))
    (hsup : P ⊔ E = L) (hinf : P ⊓ E = ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥) :
    charSpanZero (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)))
      ≤ dadeZDomain L ((P : Set G) \ {1}) :=
  have _ : (P.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).2 hnormP
  charSpanZero_le_dadeZDomain (indFam_mono _ nonprincipalIrr_subset_Irr)
    (indFam_subset_Irr (E := E) hp ha hPcard hPL hEL hnormP hsup hinf hCfree)
    (sdiff_eq_sdiff_map_subgroupOf hPL)

end Prelim

section Config

variable {G : Type*} [Group G] [Fintype G] {p a : ℕ} {L P E : Subgroup G} [Fintype ↥L]

omit [Fintype G] [Fintype ↥L] in
theorem isFreeCentralSection_center_inf_commutator
    (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hLodd : Odd (Nat.card ↥L)) (hPL : P ≤ L) (hEL : E ≤ L)
    (hnormP : L ≤ normalizer (P : Set G))
    (hsup : P ⊔ E = L) (hinf : P ⊓ E = ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) ∩ ((P : Set G) \ {1}) = ∅)
    (hna : ¬ IsMulCommutative ↥P) :
    IsFreeCentralSection p a L P E ((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆) := by
  refine
  { prime := hp
    odd_prime := hpodd
    one_le_exponent := ha
    natCard_P := hPcard
    odd_natCard_L := hLodd
    P_le := hPL
    le_normalizer_P := hnormP
    E_le := hEL
    sup_eq := hsup
    inf_eq_bot := hinf
    E_ne_bot := hEbot
    Z_ne_bot := inf_centralizer_inf_commutator_ne_bot P hp hPcard hna
    le_normalizer_Z := ?_
    Z_le_center := inf_le_left
    inf_centralizer_eq_bot := ?_
    stabilizer_punctured_eq := Set.ext fun g => hstab g
    inter_conj_eq_empty := ?_ }
  · rw [← map_subtype_center_inf_commutator P]
    exact le_normalizer_map_subtype_of_characteristic _ hnormP
  · intro u hu hu1
    refine le_bot_iff.1 (le_trans ?_ (le_of_eq (hCfree u hu hu1)))
    exact inf_le_inf_right _ (le_trans inf_le_left inf_le_left)
  · intro g hg
    rcases hTIor g with hc | hc
    · exact absurd ((hstab g).1 hc) hg
    · rw [Set.inter_comm]; exact hc

theorem isCoherent_of_isFreeCentralSection
    (h : IsFreeCentralSection p a L P E ((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆))
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥)
    (hSIrr : indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)) ⊆ Irr ↥L)
    (τ : charSpanZero (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))) →+
      virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (hτiso : ∀ f g : charSpanZero (indFam (P.subgroupOf L)
      (nonprincipalIrr ↥(P.subgroupOf L))),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ))
    (hτ1 : ∀ f : charSpanZero (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))),
      (τ f : G → ℂ) 1 = 0) :
    IsCoherent (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))) τ := by
  classical
  have hPn := h.normal_subgroupOf
  have hZn := h.normal_Z_subgroupOf
  have hXS : indFamDetect (P.subgroupOf L)
      ((((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆).subgroupOf L).subgroupOf (P.subgroupOf L))
      ⊆ indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)) :=
    indFamDetect_subset_indFam_nonprincipalIrr _ _
  have hYS : indFamLinear (P.subgroupOf L)
      ⊆ indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)) := by
    rw [nonprincipalIrr_eq_sdiff_singleton]
    exact indFamLinear_subset_indFam
  have hXYS := Set.union_subset hXS hYS
  have hcohXY :=
    SibleyCentralLinearJoining.IsFreeCentralSection.isCoherent_indFamDetect_union_indFamLinear
      h inf_le_right hCfree (restrictBaseline hXYS τ)
      (fun f => by rw [restrictBaseline_apply]; exact hτ _)
  have hXfin : (indFamDetect (P.subgroupOf L)
      ((((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆).subgroupOf L).subgroupOf
        (P.subgroupOf L))).Finite := finite_indFamDetect _ _
  have hYfin : (indFamLinear (P.subgroupOf L)).Finite := finite_indFamLinear _
  have hXYfin := hXfin.union hYfin
  have hSfin : (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))).Finite :=
    indFam_finite _ finite_nonprincipalIrr
  have hdisj := Set.disjoint_iff_inter_eq_empty.2
    (h.inter_indFamDetect_indFamLinear_eq_empty' inf_le_right)
  obtain ⟨η₀, hη₀⟩ := h.indFamLinear_nonempty' (E := E)
  obtain ⟨ξ₀, hξ₀⟩ := h.indFamDetect_nonempty_subgroupOf (E := E)
  have hne : ξ₀ ≠ η₀ := fun hcon => (Set.disjoint_left.1 hdisj) hξ₀ (hcon ▸ hη₀)
  have hXY2 : 2 ≤ (indFamDetect (P.subgroupOf L)
      ((((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆).subgroupOf L).subgroupOf (P.subgroupOf L))
      ∪ indFamLinear (P.subgroupOf L)).ncard := by
    have hsub : ({ξ₀, η₀} : Set (↥L → ℂ)) ⊆ (indFamDetect (P.subgroupOf L)
        ((((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆).subgroupOf L).subgroupOf (P.subgroupOf L))
        ∪ indFamLinear (P.subgroupOf L)) := by
      intro x hx
      rcases hx with rfl | hx
      · exact Set.mem_union_left _ hξ₀
      · rw [Set.mem_singleton_iff] at hx; exact Set.mem_union_right _ (hx ▸ hη₀)
    calc (2 : ℕ) = ({ξ₀, η₀} : Set (↥L → ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ _ := Set.ncard_le_ncard hsub hXYfin
  have hη₀deg : η₀ 1 = (Nat.card ↥E : ℂ) := h.apply_one_of_mem_indFamLinear hη₀
  have hdeg : ∀ χ ∈ indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)),
      ∃ d : ℤ, 0 < d ∧ χ 1 = (d : ℂ) * η₀ 1 := by
    intro χ hχ
    obtain ⟨n, hn0, hn⟩ := h.exists_pos_apply_one_div_natCard_eq hχ
    have hcard : ((Nat.card ↥E : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [div_eq_iff hcard] at hn
    exact ⟨(n : ℤ), Int.natCast_pos.2 hn0, by rw [hη₀deg, hn]; push_cast; ring⟩
  have hsum : ∑ f ∈ hXYfin.toFinset, f 1 ^ 2
      = (∑ ξ ∈ indFamDetectFinset (P.subgroupOf L)
            ((((P ⊓ centralizer (P : Set G)) ⊓ ⁅P, P⁆).subgroupOf L).subgroupOf
              (P.subgroupOf L)), ξ 1 ^ 2)
        + ∑ η ∈ indFamLinearFinset (P.subgroupOf L), η 1 ^ 2 := by
    rw [Set.Finite.toFinset_union hXfin hYfin, Finset.sum_union]
    · congr 1
      · apply Finset.sum_congr _ (fun _ _ => rfl)
        ext f; rw [Set.Finite.mem_toFinset, mem_indFamDetectFinset]
      · apply Finset.sum_congr _ (fun _ _ => rfl)
        ext f; rw [Set.Finite.mem_toFinset, mem_indFamLinearFinset]
    · rw [Finset.disjoint_left]
      intro f hf hf2
      rw [Set.Finite.mem_toFinset] at hf hf2
      exact (Set.disjoint_left.1 hdisj) hf hf2
  have hthr : ∀ χ ∈ indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)),
      2 * η₀ 1 * χ 1 < ∑ f ∈ hXYfin.toFinset, f 1 ^ 2 := by
    intro χ hχ
    rw [hsum, hη₀deg]
    exact h.two_mul_natCard_mul_apply_one_lt_sum_sq hχ
  exact isCoherent_of_isCoherent_subfamily hSfin hSIrr hXYS hXYfin hXY2
    (Set.mem_union_right _ hη₀) τ hτiso hτ1 hcohXY hdeg hthr

theorem isCoherent_indFam_nonprincipalIrr
    (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hLodd : Odd (Nat.card ↥L)) (hPL : P ≤ L) (hEL : E ≤ L)
    (hnormP : L ≤ normalizer (P : Set G))
    (hsup : P ⊔ E = L) (hinf : P ⊓ E = ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) ∩ ((P : Set G) \ {1}) = ∅)
    (τ : charSpanZero (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))) →+
      virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))) τ := by
  classical
  have _ : (P.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).2 hnormP
  have hHbot : P.subgroupOf L ≠ ⊥ := subgroupOf_ne_bot hp ha hPcard hPL
  have hcompl : (P.subgroupOf L).IsComplement' (E.subgroupOf L) :=
    isComplement'_subgroupOf hPL hEL hnormP hsup hinf
  have hCOf : ∀ u ∈ E.subgroupOf L, u ≠ 1 →
      (P.subgroupOf L) ⊓ centralizer ({u} : Set ↥L) = ⊥ := free_subgroupOf hPL hCfree
  have hA := sdiff_eq_sdiff_map_subgroupOf (P := P) hPL
  have hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L :=
    isTIWithNormalizer_sdiff hp ha hPcard hPL hstab hTIor
  have hpair := SibleyCentralLinearJoining.conjInv_image_eq_or_inter_eq_empty hTI
  have hSIrr : indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)) ⊆ Irr ↥L :=
    indFam_subset_Irr (E := E) hp ha hPcard hPL hEL hnormP hsup hinf hCfree
  have hz0 := charSpanZero_le_dadeZDomain_sdiff (E := E) hp ha hPcard hPL hEL hnormP hsup hinf
    hCfree
  have hτiso : ∀ f g : charSpanZero (indFam (P.subgroupOf L)
      (nonprincipalIrr ↥(P.subgroupOf L))),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := fun f g => by
    rw [hτ f, hτ g]
    exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hz0 f.2))
      (mem_dadeDomain_of_mem_dadeZDomain (hz0 g.2))
  have hτ1 : ∀ f : charSpanZero (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))),
      (τ f : G → ℂ) 1 = 0 := fun f => by
    rw [hτ f]
    exact hTI.indClassFun_apply_one fun x hx => (mem_dadeZDomain.1 (hz0 f.2)).2 x hx
  by_cases habel : IsMulCommutative ↥P
  ·
    have : IsMulCommutative ↥(P.subgroupOf L) :=
      isMulCommutative_subgroupOf_of_isMulCommutative habel
    exact isCoherent_of_coe_eq_indClassFun (A := (P : Set G) \ {1}) hHbot hcompl hCOf hA hstab
      hpair τ hτ
  ·
    exact isCoherent_of_isFreeCentralSection
      (isFreeCentralSection_center_inf_commutator hp hpodd ha hPcard hLodd hPL hEL hnormP hsup
        hinf hEbot hCfree hstab hTIor habel)
      hCfree hSIrr τ hτ hτiso hτ1

theorem isCoherent_indCharSpanZeroHom
    (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hLodd : Odd (Nat.card ↥L)) (hPL : P ≤ L) (hEL : E ≤ L)
    (hnormP : L ≤ normalizer (P : Set G))
    (hsup : P ⊔ E = L) (hinf : P ⊓ E = ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) ∩ ((P : Set G) \ {1}) = ∅) :
    IsCoherent (indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)))
      ((isTIWithNormalizer_sdiff hp ha hPcard hPL hstab hTIor).indCharSpanZeroHom
        (charSpanZero_le_dadeZDomain_sdiff (E := E) hp ha hPcard hPL hEL hnormP hsup hinf
          hCfree)) :=
  isCoherent_indFam_nonprincipalIrr hp hpodd ha hPcard hLodd hPL hEL hnormP hsup hinf hEbot
    hCfree hstab hTIor _ (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)

end Config

end SibleyPGroupCoherence

end CFSG.FeitThompson

end
