module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzOrthKernel
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeGeneration

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Basic

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_hypPair_of_regular {U : Submodule K V}
    (hU : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate) {e : V} (heU : e ∈ U)
    (he0 : e ≠ 0) (heQ : Q e = 0) : ∃ f ∈ U, Q f = 0 ∧ polar Q e f = 1 := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ U, polar Q e g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (congrArg Subtype.val (hU.1 ⟨e, heU⟩ fun z => hcon z z.2))
  obtain ⟨f₀, hf₀U, hf₀⟩ : ∃ f₀ ∈ U, polar Q e f₀ = 1 :=
    ⟨(polar Q e g)⁻¹ • g, U.smul_mem _ hgU, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hg]⟩
  have hee : polar Q e e = 0 := polar_self_eq_zero heQ
  refine ⟨f₀ - Q f₀ • e, U.sub_mem hf₀U (U.smul_mem _ heU), ?_, ?_⟩
  · have h1 : Q (f₀ - Q f₀ • e) = Q f₀ + Q (-(Q f₀ • e)) + polar Q f₀ (-(Q f₀ • e)) := by
      rw [sub_eq_add_neg]
      exact QuadraticMap.map_add Q f₀ (-(Q f₀ • e))
    rw [h1, QuadraticMap.map_neg, map_smul_eq_sq, heQ, polar_neg_right, polar_smul_right_eq,
      polar_comm Q f₀ e, hf₀]
    ring
  · rw [polar_sub_right, polar_smul_right_eq, hee, hf₀]
    ring

end Basic

section Plane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {E : Subgroup (orthDerived Q)}

theorem eichler_mem_span_of_lineFix (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {M : Subgroup E} (hM : M ≠ ⊥) {e w : V} (he : e ∈ lineFixSpace M) (hw : w ∈ lineFixSpace M) :
    eichler Q e w ∈ orthCentralizerSpan Q E := by
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
  have hmem : ((t : E) : orthDerived Q) ∈ E := (t : E).2
  have hfix : ∀ v ∈ lineFixSpace M, (((t : E) : orthDerived Q) : V ≃ₗ[K] V) v = v := by
    intro v hv
    exact (mem_fixSpace.mp hv) _ ⟨((t : E) : orthDerived Q), ⟨(t : E), t.2, rfl⟩, rfl⟩
  by_cases h : Q e = 0 ∧ polar Q e w = 0
  · refine eichler_mem_orthCentralizerSpan_of_fix hEΩ (x := ((t : E) : orthDerived Q)) hmem ?_
      (hfix e he) (hfix w hw)
    intro h1
    exact ht1 (Subtype.ext (Subtype.ext h1))
  · rw [eichler_of_not h]
    exact Subgroup.one_mem _

end Plane


section Cases

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Nontrivial V] {Q : QuadraticForm K V} {p : ℕ}

theorem closure_eq_top_of_singular_fixed (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) {e : V} (he : e ∈ planeFixSpace E) (he0 : e ≠ 0)
    (heQ : Q e = 0) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hreg : (LinearMap.BilinForm.restrict (polarBilin Q) (planeFixSpace E)).Nondegenerate :=
    hK.regular none
  obtain ⟨f, hfU, hfQ, hef⟩ := exists_hypPair_of_regular hreg he he0 heQ
  have hle := elementaryGroup_le_orthCentralizerSpan_of_hypPair hp hQ hT hK
    ⟨e, f, heQ, hfQ, hef⟩ he hfU
  exact closure_centralizers_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

omit [Nontrivial V] in
theorem closure_eq_top_of_split (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hGΩ : E.map (orthDerived Q).subtype ≤ orthDerived Q := Subgroup.map_subtype_le E
  have hGcard : Nat.card (E.map (orthDerived Q).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective, hcard]
  have hgen := orthogonal_plane_derived_centralizers_generate hQ hT hp hp3 hpq
    (E.map (orthDerived Q).subtype) hGΩ (isElemAbelian_map_subtype E hcomm hexp) hGcard
  exact closure_centralizers_eq_top_of_le E (orthDerived_le_orthCentralizerSpan_of_iSup E hgen)

end Cases

end CFSG.LieType.SeitzGeneration
