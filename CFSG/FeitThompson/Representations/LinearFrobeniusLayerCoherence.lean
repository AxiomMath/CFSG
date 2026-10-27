module

public import CFSG.FeitThompson.Representations.FreeCentralSectionTISylowRestriction
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
public import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
public import CFSG.FeitThompson.Representations.DerivedKernelLayerUniformlyIrreducible
public import CFSG.FeitThompson.Representations.SolvableGroupNonprincipalLinearCharacter
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
public import CFSG.FeitThompson.Representations.NormalInductionPreservesKernelSubgroup
public import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
public import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
public import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport
public import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup NormalLinearInduced

section Internal

variable {L : Type*} [Group L] [Fintype L] {P E Z : Subgroup L}

theorem indFamLinear_subset_Irr_of_centralizer_le [P.Normal] [Group.IsSolvable ↥P] [Nontrivial ↥P]
    (hPE : P.IsComplement' E) (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E))
    (hC : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set L) ≤ (⁅P, P⁆ : Subgroup L)) :
    indFamLinear P ⊆ Irr L := by
  have : Fintype ↥P := Fintype.ofFinite _
  have : Fintype ↥E := Fintype.ofFinite _
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear P).1 hf
  obtain ⟨hθirr, hθ1, hθne⟩ := mem_nonprincipalLinearIrr.1 hθ
  have hker : ((_root_.commutator ↥P : Subgroup ↥P) : Set ↥P) ⊆ charValueKernel θ :=
    Irr.commutator_subset_charValueKernel hθirr hθ1
  have hfree : ∀ u : ↥E, u ≠ 1 → ∀ k : ↥P,
      frobeniusConjAut P E u k = k → k ∈ _root_.commutator ↥P := by
    intro u hu k hk
    have hcoe : (u : L) * (k : L) * (u : L)⁻¹ = (k : L) := by
      rw [← coe_frobeniusConjAut_apply (E := E) u k, hk]
    refine (coe_mem_commutator_iff P).1 (hC (u : L) u.2 (fun hc => hu (Subtype.ext hc)) ?_)
    refine Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (k : L) * (u : L) = ((u : L) * (k : L) * (u : L)⁻¹) * (u : L) := by rw [hcoe]
      _ = (u : L) * (k : L) := by group
  refine mem_Irr_of_comp_mulEquiv (frobeniusMulEquiv hPE) ?_
  rw [indClassFun_comp_frobeniusMulEquiv hPE θ]
  exact indClassFun_kernelClassFun_mem_Irr_of_commutator_subset hcop hfree hθirr hθne hker

theorem indFamLinear_nonempty [Group.IsSolvable ↥P] [Nontrivial ↥P] :
    (indFamLinear P).Nonempty := by
  obtain ⟨θ, hθ, hθ1, hθne⟩ := exists_mem_Irr_apply_one_eq_one_and_ne_one ↥P
  exact ⟨indClassFun P θ, indClassFun_mem_indFamLinear P
    (mem_nonprincipalLinearIrr.2 ⟨hθ, hθ1, hθne⟩)⟩

theorem not_conj_eq_self_of_mem_indFamLinear (hodd : Odd (Nat.card L))
    (hY : indFamLinear P ⊆ Irr L) {f : L → ℂ} (hf : f ∈ indFamLinear P) :
    f ≠ fun x => (starRingEnd ℂ) (f x) :=
  ne_conj_of_mem_Irr_of_ne_one_of_odd hodd (hY hf) (ne_one_of_mem_indFamLinear P hf)

theorem not_subset_charValueKernel_of_mem_indFamDetect [Z.Normal] (hZP : Z ≤ P) {f : L → ℂ}
    (hf : f ∈ indFamDetect P (Z.subgroupOf P)) :
    ¬ (Z : Set L) ⊆ charValueKernel f := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect P).1 hf
  obtain ⟨hθirr, hθker⟩ := mem_irrDetect.1 hθ
  rw [← normalInduction_indClassFun_eq,
    NormalInduction.subset_charValueKernel_indClassFun_iff hZP
      (by rw [normalInduction_irrChars_eq_Irr, Irr_eq_irrChar]; exact hθirr)]
  exact hθker

theorem inter_indFamDetect_indFamLinear_eq_empty [P.Normal] [Z.Normal] (hZP : Z ≤ P)
    (hZ : Z ≤ (⁅P, P⁆ : Subgroup L)) :
    indFamDetect P (Z.subgroupOf P) ∩ indFamLinear P = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun f ⟨hfX, hfY⟩ => ?_
  refine not_subset_charValueKernel_of_mem_indFamDetect hZP hfX fun z hz => ?_
  exact mem_charValueKernel.2 (apply_eq_apply_one_of_mem_commutator P hfY (hZ hz))

end Internal

section Coherence

variable {G : Type*} [Group G] {L P : Subgroup G}

theorem mem_dadeZDomain_of_mem_charSpanZero [Fintype ↥L] [(P.subgroupOf L).Normal]
    {S : Set (↥L → ℂ)} (hSind : S ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)))
    (hSirr : S ⊆ Irr ↥L) (f : charSpanZero S) :
    (f : ↥L → ℂ) ∈ dadeZDomain L ((P : Set G) \ {1}) := by
  refine mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
    (Submodule.span_mono hSirr (charSpanZero_le S f.2)), ?_⟩
  intro x hx
  by_cases hxP : (x : G) ∈ P
  · have hx1 : x = 1 := Subtype.ext (by simpa [hxP] using hx)
    rw [hx1]
    exact charSpanZero_apply_one f
  · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem _ hSind
      (charSpanZero_le S f.2) (fun hc => hxP (Subgroup.mem_subgroupOf.1 hc))

noncomputable def tiIndCharSpanZeroHom [Fintype G] [Fintype ↥L] [(P.subgroupOf L).Normal]
    (hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L) {S : Set (↥L → ℂ)}
    (hSind : S ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L))) (hSirr : S ⊆ Irr ↥L) :
    charSpanZero S →+ virtualChars G where
  toFun f := ⟨indClassFun L (f : ↥L → ℂ),
    hTI.indClassFun_mem_virtualChars (mem_dadeZDomain_of_mem_charSpanZero hSind hSirr f)⟩
  map_zero' := Subtype.ext (indClassFun_zero L)
  map_add' f g := Subtype.ext (indClassFun_add L (f : ↥L → ℂ) (g : ↥L → ℂ))

@[simp] theorem coe_tiIndCharSpanZeroHom [Fintype G] [Fintype ↥L] [(P.subgroupOf L).Normal]
    (hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L) {S : Set (↥L → ℂ)}
    (hSind : S ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L))) (hSirr : S ⊆ Irr ↥L)
    (f : charSpanZero S) :
    ((tiIndCharSpanZeroHom hTI hSind hSirr f : virtualChars G) : G → ℂ)
      = indClassFun L (f : ↥L → ℂ) := (rfl)

theorem isCoherent_tiIndCharSpanZeroHom [Fintype G] [Fintype ↥L] [(P.subgroupOf L).Normal]
    (hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L) {S : Set (↥L → ℂ)} (hSfin : S.Finite)
    (hSind : S ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L))) (hSirr : S ⊆ Irr ↥L)
    {d : ℂ} (hdeg : ∀ χ ∈ S, χ 1 = d) :
    IsCoherent S (tiIndCharSpanZeroHom hTI hSind hSirr) := by
  refine isCoherent_of_forall_apply_one_eq hSfin hSirr hdeg _ (fun f g => ?_) (fun f => ?_)
  · rw [coe_tiIndCharSpanZeroHom, coe_tiIndCharSpanZeroHom]
    exact hTI.cfInner_indClassFun
      (mem_dadeDomain_of_mem_dadeZDomain (mem_dadeZDomain_of_mem_charSpanZero hSind hSirr f))
      (mem_dadeDomain_of_mem_dadeZDomain (mem_dadeZDomain_of_mem_charSpanZero hSind hSirr g))
  · rw [coe_tiIndCharSpanZeroHom]
    exact hTI.indClassFun_apply_one
      (mem_dadeZDomain.1 (mem_dadeZDomain_of_mem_charSpanZero hSind hSirr f)).2

end Coherence

section Configuration

variable {G : Type*} [Group G] {L P E Z : Subgroup G}

theorem commutator_subgroupOf_eq (hP : P ≤ L) :
    ⁅P.subgroupOf L, P.subgroupOf L⁆ = (⁅P, P⁆ : Subgroup G).subgroupOf L := by
  have hinj : Function.Injective (Subgroup.map L.subtype) :=
    Subgroup.map_injective L.subtype_injective
  apply hinj
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hP, inf_eq_left.2 ((Subgroup.commutator_le_self P).trans hP)]

namespace IsFreeCentralSection

variable {p a : ℕ} (h : IsFreeCentralSection p a L P E Z)

include h

theorem sup_subgroupOf' : P.subgroupOf L ⊔ E.subgroupOf L = ⊤ := by
  rw [← Subgroup.subgroupOf_sup h.P_le h.E_le, h.sup_eq, Subgroup.subgroupOf_self]

theorem inf_subgroupOf_eq_bot' : P.subgroupOf L ⊓ E.subgroupOf L = ⊥ := by
  rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, h.inf_eq_bot]
  simp [Subgroup.ker_subtype]

theorem isComplement'_subgroupOf : (P.subgroupOf L).IsComplement' (E.subgroupOf L) := by
  have := h.normal_subgroupOf
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_iff.2 h.inf_subgroupOf_eq_bot') ?_
  rw [← Subgroup.normal_mul, h.sup_subgroupOf']
  simp

theorem isPGroup_subgroupOf_P : IsPGroup p ↥(P.subgroupOf L) :=
  h.isPGroup_P.comap_of_injective L.subtype L.subtype_injective

theorem isSolvable_subgroupOf_P [Finite G] : Group.IsSolvable ↥(P.subgroupOf L) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.isPGroup_subgroupOf_P.isNilpotent
  infer_instance

theorem nontrivial_subgroupOf_P : Nontrivial ↥(P.subgroupOf L) :=
  (subgroupOfEquivOfLe h.P_le).toEquiv.nontrivial_congr.2
    ((Subgroup.nontrivial_iff_ne_bot P).2 h.P_ne_bot)

theorem coprime_natCard_subgroupOf [Finite G] :
    (Nat.card ↥(P.subgroupOf L)).Coprime (Nat.card ↥(E.subgroupOf L)) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe h.P_le).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe h.E_le).toEquiv]
  exact h.coprime_natCard

theorem normal_Z_subgroupOf' : (Z.subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.Z_le).2 h.le_normalizer_Z

theorem inf_centralizer_subgroupOf_le
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G))
    (u : ↥L) (hu : u ∈ E.subgroupOf L) (hu1 : u ≠ 1) :
    P.subgroupOf L ⊓ centralizer ({u} : Set ↥L) ≤ ⁅P.subgroupOf L, P.subgroupOf L⁆ := by
  intro k hk
  obtain ⟨hkP, hkc⟩ := Subgroup.mem_inf.1 hk
  have hcomm : ((k : G)) * ((u : G)) = ((u : G)) * ((k : G)) := by
    have := congrArg (fun w : ↥L => (w : G))
      (Subgroup.mem_centralizer_singleton_iff.1 hkc)
    simpa using this
  rw [commutator_subgroupOf_eq h.P_le]
  refine Subgroup.mem_subgroupOf.2 (hCP (u : G) hu (fun hc => hu1 (Subtype.ext hc)) ?_)
  exact Subgroup.mem_inf.2
    ⟨Subgroup.mem_subgroupOf.1 hkP, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩

variable [Fintype ↥L]

theorem indFamLinear_subset_Irr [Finite G]
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G)) :
    indFamLinear (P.subgroupOf L) ⊆ Irr ↥L := by
  have := h.normal_subgroupOf
  have := h.isSolvable_subgroupOf_P
  have := h.nontrivial_subgroupOf_P
  exact indFamLinear_subset_Irr_of_centralizer_le h.isComplement'_subgroupOf
    h.coprime_natCard_subgroupOf
    (fun u hu hu1 => h.inf_centralizer_subgroupOf_le hCP u hu hu1)

theorem indFamLinear_nonempty' [Finite G] : (indFamLinear (P.subgroupOf L)).Nonempty := by
  have := h.isSolvable_subgroupOf_P
  have := h.nontrivial_subgroupOf_P
  exact indFamLinear_nonempty

theorem apply_one_of_mem_indFamLinear [Finite G] {f : ↥L → ℂ}
    (hf : f ∈ indFamLinear (P.subgroupOf L)) : f 1 = (Nat.card ↥E : ℂ) := by
  rw [NormalLinearInduced.apply_one_of_mem_indFamLinear (P.subgroupOf L) hf,
    h.index_subgroupOf_eq]

theorem inter_indFamDetect_indFamLinear_eq_empty' (hZ : Z ≤ (⁅P, P⁆ : Subgroup G)) :
    indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ∩ indFamLinear (P.subgroupOf L) = ∅ := by
  have := h.normal_subgroupOf
  have := h.normal_Z_subgroupOf'
  refine inter_indFamDetect_indFamLinear_eq_empty
    (fun x hx => Subgroup.mem_subgroupOf.2 (h.Z_le_P (Subgroup.mem_subgroupOf.1 hx))) ?_
  rw [commutator_subgroupOf_eq h.P_le]
  exact Subgroup.subgroupOf_mono L hZ

theorem not_conj_eq_self_of_mem_indFamLinear' [Finite G]
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G))
    {f : ↥L → ℂ} (hf : f ∈ indFamLinear (P.subgroupOf L)) :
    f ≠ fun x => (starRingEnd ℂ) (f x) :=
  not_conj_eq_self_of_mem_indFamLinear h.odd_natCard_L (h.indFamLinear_subset_Irr hCP) hf

variable [Fintype G] [(P.subgroupOf L).Normal]

theorem isCoherent_indFamLinear
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G)) :
    IsCoherent (indFamLinear (P.subgroupOf L))
      (tiIndCharSpanZeroHom h.isTI (indFamLinear_subset_indFam_Irr (P.subgroupOf L))
        (h.indFamLinear_subset_Irr hCP)) :=
  isCoherent_tiIndCharSpanZeroHom h.isTI (finite_indFamLinear _) _ _
    (fun _ hχ => h.apply_one_of_mem_indFamLinear hχ)

end IsFreeCentralSection

end Configuration

end CFSG.FeitThompson
