module

public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
import CFSG.FeitThompson.Local.SplitKernelSubgroupInheritsComplement
import Mathlib.Analysis.Complex.Polynomial.Basic
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Representations.SchurLemmaAlgebraicallyClosed
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped commutatorElement

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exists_common_eigenvector_of_commute [Finite K] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ K V) (N : Subgroup K)
    (hcomm : ∀ m ∈ N, ∀ n ∈ N, Commute (ρ m) (ρ n)) :
    ∃ v : V, v ≠ 0 ∧ ∀ n ∈ N, ∃ c : ℂ, ρ n v = c • v := by
  classical
  set σ : Representation ℂ ↥N V := ρ.comp N.subtype with hσ
  obtain ⟨p, hp⟩ := exists_isIrreducible_subrepresentation σ
  have hpi := hp
  have hnt : Nontrivial ↥p.toSubmodule := Representation.nontrivial_of_isIrreducible _ hp
  obtain ⟨w, hw⟩ := exists_ne (0 : ↥p.toSubmodule)
  refine ⟨(w : V), by simpa using hw, ?_⟩
  intro n hn
  have hcom : ∀ m : ↥N, Commute (p.toRepresentation ⟨n, hn⟩) (p.toRepresentation m) := by
    intro m
    ext x
    have h1 : (ρ n) ((ρ (m : K)) (x : V)) = (ρ (m : K)) ((ρ n) (x : V)) :=
      congrArg (fun T : Module.End ℂ V => T (x : V)) (hcomm n hn m m.2)
    simpa [Subrepresentation.toRepresentation, hσ] using h1
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_eq_smul_one_of_commute
    p.toRepresentation (p.toRepresentation ⟨n, hn⟩) hcom
  refine ⟨c, ?_⟩
  have h2 := congrArg (fun T : Module.End ℂ ↥p.toSubmodule => ((T w : ↥p.toSubmodule) : V)) hc
  simpa [Subrepresentation.toRepresentation, hσ] using h2

theorem Representation.finrank_le_index_of_forall_commute [Finite K] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ K V) (hρ : ρ.IsIrreducible) (N : Subgroup K)
    (hcomm : ∀ m ∈ N, ∀ n ∈ N, Commute (ρ m) (ρ n)) :
    finrank ℂ V ≤ N.index := by
  classical
  have hnt : Nontrivial V := Representation.nontrivial_of_isIrreducible ρ hρ
  obtain ⟨v, hv, hev⟩ := exists_common_eigenvector_of_commute ρ N hcomm
  set f : K ⧸ N → V := fun q => ρ (Quotient.out q) v with hf
  have hmem : ∀ k : K, ρ k v ∈ Submodule.span ℂ (Set.range f) := by
    intro k
    have hq : (Quotient.out (QuotientGroup.mk k : K ⧸ N))⁻¹ * k ∈ N :=
      (QuotientGroup.eq (s := N)).1 (QuotientGroup.out_eq' _)
    obtain ⟨c, hc⟩ := hev _ hq
    have h1 : (ρ (Quotient.out (QuotientGroup.mk k : K ⧸ N)))
        ((ρ ((Quotient.out (QuotientGroup.mk k : K ⧸ N))⁻¹ * k)) v) = ρ k v := by
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    have h2 : ρ k v = c • f (QuotientGroup.mk k : K ⧸ N) := by
      rw [← h1, hc, map_smul, hf]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hWtop : Submodule.span ℂ (Set.range f) = ⊤ := by
    refine eq_top_of_isIrreducible_of_map_le hρ (fun g => ?_) ?_
    · rw [Submodule.map_span, Submodule.span_le]
      rintro x ⟨y, ⟨q, rfl⟩, rfl⟩
      have h3 : (ρ g) (f q) = ρ (g * Quotient.out q) v := by
        rw [map_mul]; rfl
      simp only [SetLike.mem_coe, h3]
      exact hmem _
    · intro h0
      have hvW : v ∈ Submodule.span ℂ (Set.range f) := by simpa using hmem 1
      rw [h0] at hvW
      exact hv (by simpa using hvW)
  have : Fintype (Set.range f) := Fintype.ofFinite _
  have hQ : Fintype (K ⧸ N) := Fintype.ofFinite _
  have h1 : finrank ℂ V ≤ (Set.range f).toFinset.card := by
    have h := finrank_span_le_card (R := ℂ) (Set.range f)
    rwa [hWtop, finrank_top] at h
  calc finrank ℂ V ≤ (Set.range f).toFinset.card := h1
    _ = Fintype.card (Set.range f) := Set.toFinset_card _
    _ ≤ Fintype.card (K ⧸ N) := Fintype.card_range_le f
    _ = N.index := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem commutatorElement_mem_of_isMulCommutative_quotient {N A : Subgroup K} [A.Normal]
    (habel : IsMulCommutative (↥N ⧸ A.subgroupOf N)) {m n : K}
    (hm : m ∈ N) (hn : n ∈ N) : ⁅m, n⁆ ∈ A := by
  have hc : _root_.commutator ↥N ≤ A.subgroupOf N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).1 habel
  have h1 : (⁅(⟨m, hm⟩ : ↥N), (⟨n, hn⟩ : ↥N)⁆ : ↥N) ∈ _root_.commutator ↥N := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  simpa [commutatorElement_def] using Subgroup.mem_subgroupOf.1 (hc h1)

theorem isMulCommutative_quotient_of_commutator_le {N A : Subgroup K} [A.Normal]
    (h : ⁅N, N⁆ ≤ A) : IsMulCommutative (↥N ⧸ A.subgroupOf N) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def,
    Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [Subgroup.mem_subgroupOf]
  exact h (Subgroup.commutator_mem_commutator g₁.2 g₂.2)

theorem Representation.finrank_le_index_of_isMulCommutative_quotient [Finite K]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) (hρ : ρ.IsIrreducible) {N A : Subgroup K}
    [A.Normal] (habel : IsMulCommutative (↥N ⧸ A.subgroupOf N))
    (hker : ∀ a ∈ A, ρ a = 1) : finrank ℂ V ≤ N.index := by
  refine Representation.finrank_le_index_of_forall_commute ρ hρ N fun m hm n hn => ?_
  have hmem : ⁅m, n⁆ ∈ A := commutatorElement_mem_of_isMulCommutative_quotient habel hm hn
  have key : ρ ⁅m, n⁆ * (ρ n * ρ m) = ρ m * ρ n := by
    rw [← map_mul, ← map_mul, ← map_mul, commutatorElement_def]
    congr 1
    group
  rw [hker _ hmem, one_mul] at key
  exact key.symm

theorem exists_degree_le_index_of_isMulCommutative_quotient [Finite K] {θ : K → ℂ}
    (hθ : θ ∈ Irr K) {N A : Subgroup K} [A.Normal]
    (habel : IsMulCommutative (↥N ⧸ A.subgroupOf N))
    (hker : (A : Set K) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = n ∧ n ≤ N.index := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have hirr : Representation.IsIrreducible W.ρ := hW
  have hker' : ∀ a ∈ A, W.ρ a = 1 := by
    intro a ha
    have h := hker ha
    rw [mem_charValueKernel, fdRepCharacter_eq, Representation.char_one W.ρ] at h
    exact (Representation.character_eq_finrank_iff_of_finite W.ρ).1 h
  exact ⟨finrank ℂ (W.V : Type), W.char_one,
    Representation.finrank_le_index_of_isMulCommutative_quotient (V := W.V) W.ρ hirr habel hker'⟩

section Scalar

variable {E U : Subgroup K}

theorem inf_centralizer_iSup {ι : Type*} [Nonempty ι] (U : Subgroup K) (L : ι → Subgroup K) :
    U ⊓ Subgroup.centralizer ((⨆ i, L i : Subgroup K) : Set K)
      = ⨅ i, (U ⊓ Subgroup.centralizer (L i : Set K)) := by
  have hcen : Subgroup.centralizer ((⨆ i, L i : Subgroup K) : Set K)
      = ⨅ i, Subgroup.centralizer (L i : Set K) := by
    refine le_antisymm (le_iInf fun i =>
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_iSup L i))) ?_
    rw [Subgroup.le_centralizer_iff, iSup_le_iff]
    intro i
    rw [← Subgroup.le_centralizer_iff]
    exact iInf_le _ i
  rw [hcen, inf_iInf]

theorem commutatorElement_mul_mul_of_le_centralizer {C : Subgroup K} [IsMulCommutative ↥E]
    (hEC : C ≤ Subgroup.centralizer (E : Set K))
    {e₁ e₂ c₁ c₂ : K} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) :
    ⁅e₁ * c₁, e₂ * c₂⁆ = ⁅c₁, c₂⁆ := by
  have hcen : ∀ c ∈ C, ∀ e ∈ E, e * c = c * e := fun c hc e he =>
    Subgroup.mem_centralizer_iff.1 (hEC hc) e he
  have hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (E.le_centralizer hy) x hx
  have hxy : (e₁ * c₁) * (e₂ * c₂) = (e₁ * e₂) * (c₁ * c₂) := by
    rw [show e₁ * c₁ * (e₂ * c₂) = e₁ * (c₁ * e₂) * c₂ by group, ← hcen c₁ hc₁ e₂ he₂]
    group
  have hyx : (e₂ * c₂) * (e₁ * c₁) = (e₁ * e₂) * (c₂ * c₁) := by
    rw [show e₂ * c₂ * (e₁ * c₁) = e₂ * (c₂ * e₁) * c₁ by group, ← hcen c₂ hc₂ e₁ he₁,
      show e₂ * (e₁ * c₂) * c₁ = (e₂ * e₁) * (c₂ * c₁) by group, hE e₂ he₂ e₁ he₁]
  have hd : ⁅c₁, c₂⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)
  have hcomm : (e₁ * e₂) * ⁅c₁, c₂⁆ = ⁅c₁, c₂⁆ * (e₁ * e₂) :=
    hcen _ hd _ (E.mul_mem he₁ he₂)
  calc ⁅e₁ * c₁, e₂ * c₂⁆ = ((e₁ * c₁) * (e₂ * c₂)) * ((e₂ * c₂) * (e₁ * c₁))⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ((e₁ * e₂) * (c₁ * c₂)) * ((e₁ * e₂) * (c₂ * c₁))⁻¹ := by rw [hxy, hyx]
    _ = (e₁ * e₂) * ⁅c₁, c₂⁆ * (e₁ * e₂)⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅c₁, c₂⁆ := by rw [hcomm]; group

theorem commutator_sup_le_commutator_of_le_centralizer {C : Subgroup K} [E.Normal]
    [IsMulCommutative ↥E] (hEC : C ≤ Subgroup.centralizer (E : Set K)) :
    ⁅E ⊔ C, E ⊔ C⁆ ≤ ⁅C, C⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg₁ hg₂
  obtain ⟨e₁, he₁, c₁, hc₁, rfl⟩ := hg₁
  obtain ⟨e₂, he₂, c₂, hc₂, rfl⟩ := hg₂
  rw [commutatorElement_mul_mul_of_le_centralizer hEC he₁ he₂ hc₁ hc₂]
  exact Subgroup.commutator_mem_commutator hc₁ hc₂

theorem sup_inf_eq_of_isComplement' [E.Normal] {C : Subgroup K} (h : E.IsComplement' U)
    (hCU : C ≤ U) : (E ⊔ C) ⊓ U = C := by
  refine le_antisymm ?_ (le_inf le_sup_right hCU)
  intro x hx
  obtain ⟨hxEC, hxU⟩ := Subgroup.mem_inf.1 hx
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hxEC
  obtain ⟨e, he, c, hc, rfl⟩ := hxEC
  have he' : e ∈ U := by
    have hrw : e = (e * c) * c⁻¹ := by group
    rw [hrw]
    exact U.mul_mem hxU (U.inv_mem (hCU hc))
  have h1 : e = 1 := by
    have hb : E ⊓ U = ⊥ := disjoint_iff.1 h.disjoint
    rw [Subgroup.eq_bot_iff_forall] at hb
    exact hb e (Subgroup.mem_inf.2 ⟨he, he'⟩)
  simpa [h1] using hc

theorem index_sup_eq_relIndex [Finite K] [E.Normal] {C : Subgroup K} (h : E.IsComplement' U)
    (hCU : C ≤ U) : (E ⊔ C).index = C.relIndex U := by
  have h2 := relIndex_inf_eq_index_of_isComplement' (U := E ⊔ C) h le_sup_left
  rw [sup_inf_eq_of_isComplement' h hCU] at h2
  exact h2.symm

theorem normal_inf_centralizer_of_isComplement' [E.Normal] (h : E.IsComplement' U) :
    (U ⊓ Subgroup.centralizer (E : Set K)).Normal := by
  set C := U ⊓ Subgroup.centralizer (E : Set K) with hC
  have hCU : C ≤ U := inf_le_left
  have hCcent : C ≤ Subgroup.centralizer (E : Set K) := inf_le_right
  have hUconj : ∀ x ∈ U, ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx c hc
    refine Subgroup.mem_inf.2 ⟨U.mul_mem (U.mul_mem hx (hCU hc)) (U.inv_mem hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hE : x⁻¹ * e * x ∈ E := by
      simpa [mul_assoc] using ‹E.Normal›.conj_mem e he x⁻¹
    have hcc := Subgroup.mem_centralizer_iff.1 (hCcent hc) _ hE
    calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [hcc]
      _ = (x * c * x⁻¹) * e := by group
  constructor
  intro c hc k
  have hktop : k ∈ E ⊔ U := by rw [h.sup_eq_top]; exact Subgroup.mem_top k
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hktop
  obtain ⟨e, he, x, hx, rfl⟩ := hktop
  have hd : x * c * x⁻¹ ∈ C := hUconj x hx c hc
  have hcomm := Subgroup.mem_centralizer_iff.1 (hCcent hd) e he
  have hkey : e * x * c * (e * x)⁻¹ = x * c * x⁻¹ :=
    calc e * x * c * (e * x)⁻¹ = e * (x * c * x⁻¹) * e⁻¹ := by group
      _ = (x * c * x⁻¹) * e * e⁻¹ := by rw [← hcomm]
      _ = x * c * x⁻¹ := by group
  rw [hkey]
  exact hd

theorem exists_degree_le_relIndex_centralizer_of_isComplement' [Finite K] [E.Normal]
    [IsMulCommutative ↥E] (h : E.IsComplement' U) {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hker : ((⁅U ⊓ Subgroup.centralizer (E : Set K), U ⊓ Subgroup.centralizer (E : Set K)⁆ :
        Subgroup K) : Set K) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = n ∧ n ≤ (U ⊓ Subgroup.centralizer (E : Set K)).relIndex U := by
  set C := U ⊓ Subgroup.centralizer (E : Set K) with hC
  have hCnormal : C.Normal := normal_inf_centralizer_of_isComplement' h
  have hAnormal : (⁅C, C⁆ : Subgroup K).Normal := Subgroup.commutator_normal C C
  have habel : IsMulCommutative (↥(E ⊔ C) ⧸ (⁅C, C⁆ : Subgroup K).subgroupOf (E ⊔ C)) :=
    isMulCommutative_quotient_of_commutator_le
      (commutator_sup_le_commutator_of_le_centralizer (E := E) inf_le_right)
  obtain ⟨n, hn, hle⟩ :=
    exists_degree_le_index_of_isMulCommutative_quotient hθ (N := E ⊔ C) (A := ⁅C, C⁆) habel hker
  exact ⟨n, hn, by rwa [index_sup_eq_relIndex h inf_le_left] at hle⟩

end Scalar

end CFSG.FeitThompson
