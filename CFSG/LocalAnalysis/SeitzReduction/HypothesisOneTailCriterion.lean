module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneHeightRigidityAut
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneInnerBasic
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem commute_of_mem_closure_odd_tail {G : Type*} [Group G] {t u x : G}
    (hu : ∀ c : G, c * t = t * c → Odd (orderOf c) → u * c = c * u)
    (hx : x ∈ closure {c : G | c * t = t * c ∧ Odd (orderOf c)}) : u * x = x * u := by
  have hle : closure {c : G | c * t = t * c ∧ Odd (orderOf c)} ≤ centralizer {u} :=
    (closure_le _).2 fun c hc => mem_centralizer_singleton_iff.2 (hu c hc.1 hc.2).symm
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm


theorem conj_injective_adjointGroup_tail [Finite K] {τ : Tag} :
    Function.Injective (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [← center_adjointGroup_eq_bot (τ := τ) (K := K), Subgroup.mem_center_iff]
  intro x
  have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hc) x
  rw [MulAut.conj_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm


theorem innerCentralizerCriterion_of_heightSeries [Finite K] {τ : Tag} {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail τ h) {t : adjointGroup τ K}
    (hodd : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ u ∈ posUnipotent τ K, (∀ x ∈ heightSeries τ K h, u * x = x * u) →
      (∀ c : adjointGroup τ K, c * t = t * c → Odd (orderOf c) →
        u * (c : ModGL τ K) = (c : ModGL τ K) * u) → u ^ 2 = 1)
    (hout : ∀ β : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x) →
        β ∈ diagonalFieldActors τ K) :
    InnerCentralizerCriterion t := by
  refine innerCentralizerCriterion_of_pointwise conj_injective_adjointGroup_tail
    (V := (heightSeries τ K h).subgroupOf (adjointGroup τ K))
    (fun x hx => hodd x (Subgroup.mem_subgroupOf.1 hx)) fun β hβ => ?_
  have hfix : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x :=
    fun x hx => hβ x (Subgroup.mem_subgroupOf.2 hx)
  obtain ⟨u, hu, huC, rfl, hcomm⟩ :=
    exists_eq_conj_commute_of_mem_actors_of_fix_heightSeries h1 hd (hout β hfix) hfix
  refine ⟨⟨u, huC⟩, rfl, fun hc => Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact hcen u hu hcomm fun c hct hco => congrArg Subtype.val (hc c hct hco)

theorem innerCentralizerCriterion_of_rootSpan [Finite K] {τ : Tag} {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail τ h) {t : adjointGroup τ K} {S : Set (Fin τ.rank → ℤ)}
    (htail : heightSeries τ K h ≤ rootSpan τ K S)
    (hodd : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSpan τ K S →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ z ∈ posUnipotent τ K, (∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) →
      z ^ 2 = 1)
    (hout : ∀ β : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSpan τ K S → β x = x) →
        β ∈ diagonalFieldActors τ K) :
    InnerCentralizerCriterion t := by
  refine innerCentralizerCriterion_of_pointwise conj_injective_adjointGroup_tail
    (V := (rootSpan τ K S).subgroupOf (adjointGroup τ K))
    (fun x hx => hodd x (Subgroup.mem_subgroupOf.1 hx)) fun β hβ => ?_
  have hfixS : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSpan τ K S → β x = x :=
    fun x hx => hβ x (Subgroup.mem_subgroupOf.2 hx)
  obtain ⟨u, hu, huC, rfl, -⟩ :=
    exists_eq_conj_commute_of_mem_actors_of_fix_heightSeries h1 hd (hout β hfixS)
      fun x hx => hfixS x (htail hx)
  refine ⟨⟨u, huC⟩, rfl, fun _ => Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  refine hcen u hu fun δ hδ => ?_
  have e := congrArg Subtype.val (hfixS ⟨pinnedX τ K δ 1, pinnedX_mem_adjointGroup _ _⟩
    (pinnedX_mem_rootSpan hδ 1))
  rw [MulAut.conj_apply] at e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
  calc u * pinnedX τ K δ 1 = u * pinnedX τ K δ 1 * u⁻¹ * u := by group
    _ = pinnedX τ K δ 1 * u := by rw [e]

theorem innerCentralizerCriterion_of_heightSeries_of_pinnedX [Finite K] {τ : Tag} {h : ℤ}
    (h1 : 1 ≤ h) (hd : SimpleDiffTail τ h) {t : adjointGroup τ K} {S : Set (Fin τ.rank → ℤ)}
    (hodd : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hS : ∀ δ ∈ S, (⟨pinnedX τ K δ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈
      closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ z ∈ posUnipotent τ K, (∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) →
      z ^ 2 = 1)
    (hout : ∀ β : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x) →
        β ∈ diagonalFieldActors τ K) :
    InnerCentralizerCriterion t := by
  refine innerCentralizerCriterion_of_heightSeries h1 hd hodd (fun u hu _ hc => ?_) hout
  refine hcen u hu fun δ hδ => ?_
  have e := commute_of_mem_closure_odd_tail (u := (⟨u, posUnipotent_le_adjointGroup hu⟩ :
    adjointGroup τ K)) (fun c hct hco => Subtype.ext (hc c hct hco)) (hS δ hδ)
  exact congrArg Subtype.val e

theorem innerCentralizerCriterion_E_of_heightSeries [Finite K] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {h : ℤ} (h1 : 1 ≤ h) (hh : h ≤ simpleDiffTailMax τ)
    {t : adjointGroup τ K}
    (hodd : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ u ∈ posUnipotent τ K, (∀ x ∈ heightSeries τ K h, u * x = x * u) →
      (∀ c : adjointGroup τ K, c * t = t * c → Odd (orderOf c) →
        u * (c : ModGL τ K) = (c : ModGL τ K) * u) → u ^ 2 = 1) :
    InnerCentralizerCriterion t :=
  innerCentralizerCriterion_of_heightSeries h1 (simpleDiffTail_of_le hh) hodd hcen
    fun _ hβ => mem_diagonalFieldActors_of_fix_heightSeries_E hτ h1 hh hβ

theorem innerCentralizerCriterion_E_of_rootSpan [Finite K] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {h : ℤ} (h1 : 1 ≤ h) (hh : h ≤ simpleDiffTailMax τ)
    {t : adjointGroup τ K} {S : Set (Fin τ.rank → ℤ)}
    (htail : heightSeries τ K h ≤ rootSpan τ K S)
    (hodd : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSpan τ K S →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ z ∈ posUnipotent τ K, (∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) →
      z ^ 2 = 1) :
    InnerCentralizerCriterion t :=
  innerCentralizerCriterion_of_rootSpan h1 (simpleDiffTail_of_le hh) htail hodd hcen
    fun _ hβ => mem_diagonalFieldActors_of_fix_heightSeries_E hτ h1 hh fun x hx => hβ x (htail hx)

theorem innerCentralizerCriterion_E_of_heightSeries_of_pinnedX [Finite K] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {h : ℤ} (h1 : 1 ≤ h) (hh : h ≤ simpleDiffTailMax τ)
    {t : adjointGroup τ K} {S : Set (Fin τ.rank → ℤ)}
    (hodd : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hS : ∀ δ ∈ S, (⟨pinnedX τ K δ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈
      closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)})
    (hcen : ∀ z ∈ posUnipotent τ K, (∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) →
      z ^ 2 = 1) :
    InnerCentralizerCriterion t :=
  innerCentralizerCriterion_of_heightSeries_of_pinnedX h1 (simpleDiffTail_of_le hh) hodd hS hcen
    fun _ hβ => mem_diagonalFieldActors_of_fix_heightSeries_E hτ h1 hh hβ

end CFSG.SeitzReduction
