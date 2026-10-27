module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Abstract

variable {M : Type} [Group M]

theorem linkedIn_of_layer {F : Set (Subgroup M)} (hF : ∀ R ∈ F, ∀ g : M, conjSub g R ∈ F)
    (hperf : ∀ R ∈ F, R ≤ ⁅R, R⁆) (hnab : ∀ R ∈ F, ¬ Commutes R R) {R₀ L : Subgroup M}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hLC : L ≤ Subgroup.centralizer (R₀ : Set M))
    (hLperf : ∀ P : Subgroup M, P ≤ Subgroup.centralizer (R₀ : Set M) → P ≤ ⁅P, P⁆ → P ≤ L)
    {R₁ R₂ : Subgroup M} (h₁ : R₁ ∈ F) (h₂ : R₂ ∈ F) (c₁ : Commutes R₁ R₀)
    (c₂ : Commutes R₂ R₀) : LinkedIn F R₀ R₁ R₂ := by
  classical
  set Λ : Set (Subgroup M) := {R | R ∈ F ∧ Commutes R R₀} with hΛ
  have hΛC : ∀ R ∈ Λ, R ≤ Subgroup.centralizer (R₀ : Set M) := by
    intro R hR x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hR.2 x hx y hy).symm
  have hΛL : ∀ R ∈ Λ, R ≤ L := fun R hR => hLperf R (hΛC R hR) (hperf R hR.1)
  have hconj : ∀ g ∈ L, ∀ R ∈ Λ, conjSub g R ∈ Λ := by
    intro g hg R hR
    refine ⟨hF R hR.1 g, fun x hx y hy => ?_⟩
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ R, x = g * x' * g⁻¹ :=
      ⟨g⁻¹ * x * g, mem_conjSub_iff.mp hx, by group⟩
    have hgy : y * g = g * y := Subgroup.mem_centralizer_iff.mp (hLC hg) y hy
    have e1 : g⁻¹ * y = y * g⁻¹ := by
      calc g⁻¹ * y = g⁻¹ * y * g * g⁻¹ := by group
        _ = g⁻¹ * (g * y) * g⁻¹ := by rw [mul_assoc g⁻¹ y g, hgy]
        _ = y * g⁻¹ := by group
    have hxy : x' * y = y * x' := hR.2 x' hx' y hy
    calc g * x' * g⁻¹ * y = g * x' * (g⁻¹ * y) := by group
      _ = g * (x' * y) * g⁻¹ := by rw [e1]; group
      _ = g * (y * x') * g⁻¹ := by rw [hxy]
      _ = (g * y) * x' * g⁻¹ := by group
      _ = (y * g) * x' * g⁻¹ := by rw [← hgy]
      _ = y * (g * x' * g⁻¹) := by group
  set B : Set (Subgroup M) := {R | R ∈ Λ ∧ LinkedIn F R₀ R₁ R} with hB
  have hR₁Λ : R₁ ∈ Λ := ⟨h₁, c₁⟩
  have hR₂Λ : R₂ ∈ Λ := ⟨h₂, c₂⟩
  have hR₁B : R₁ ∈ B := ⟨hR₁Λ, Relation.ReflTransGen.refl⟩
  have hcomm : ∀ R ∈ Λ, R ∉ B → ∀ R' ∈ B, Commutes R R' := by
    intro R hR hRB R' hR'
    by_contra hnc
    exact hRB ⟨hR, hR'.2.tail ⟨hR'.1.1, hR.1, hR'.1.2, hR.2, fun h => hnc (Commutes.symm h)⟩⟩
  let H : Subgroup M := ⨆ R : ↥B, R.1
  let H' : Subgroup M := ⨆ R : ↥(Λ \ B), R.1
  have hHL : H ≤ L := iSup_le fun R => hΛL R.1 R.2.1
  have hH'L : H' ≤ L := iSup_le fun R => hΛL R.1 R.2.1
  have hHH' : Commutes H H' := commutes_iSup_iSup fun i j =>
    (hcomm j.1 j.2.1 j.2.2 i.1 i.2).symm
  have hle_sup : ∀ R ∈ Λ, R ≤ H ⊔ H' := by
    intro R hR
    by_cases hRB : R ∈ B
    · exact (le_iSup (fun R : ↥B => R.1) ⟨R, hRB⟩).trans le_sup_left
    · exact (le_iSup (fun R : ↥(Λ \ B) => R.1) ⟨R, hR, hRB⟩).trans le_sup_right
  let M₀ : Subgroup M := ⨆ R : ↥Λ, R.1
  have hM₀L : M₀ ≤ L := iSup_le fun R => hΛL R.1 R.2
  have hM₀norm : ∀ g ∈ L, ∀ n ∈ M₀, g * n * g⁻¹ ∈ M₀ := by
    intro g hg n hn
    induction hn using Subgroup.iSup_induction' with
    | hp R x hx =>
      exact (le_iSup (fun R : ↥Λ => R.1) ⟨conjSub g R.1, hconj g hg R.1 R.2⟩)
        (conj_mem_conjSub hx)
    | h1 => simp
    | hmul u v _ _ hu hv =>
      have e : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [e]
      exact M₀.mul_mem hu hv
  have hM₀normal : (M₀.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hM₀norm g g.2 n hn
  have hnoncentral : ∀ N : Subgroup M, N ≤ L → R₁ ≤ N → ¬ N.subgroupOf L ≤ Subgroup.center ↥L := by
    intro N hNL hR₁N hcen
    apply hnab R₁ h₁
    intro x hx y hy
    have := Subgroup.mem_center_iff.mp
      (hcen (show (⟨x, hΛL R₁ hR₁Λ hx⟩ : ↥L) ∈ N.subgroupOf L from hR₁N hx))
      ⟨y, hΛL R₁ hR₁Λ hy⟩
    exact congrArg Subtype.val this.symm
  have hLM₀ : L ≤ M₀ := by
    rcases normal_eq_top_or_le_center hLq hM₀normal with h | h
    · exact Subgroup.subgroupOf_eq_top.mp h
    · exact absurd h (hnoncentral M₀ hM₀L (le_iSup (fun R : ↥Λ => R.1) ⟨R₁, hR₁Λ⟩))
  have hLHH' : L ≤ H ⊔ H' := hLM₀.trans (iSup_le fun R => hle_sup R.1 R.2)
  have hnormlz : H ⊔ H' ≤ Subgroup.normalizer (H : Set M) := by
    refine sup_le Subgroup.le_normalizer fun w hw => ?_
    rw [Subgroup.mem_normalizer_iff]
    have hfix : ∀ w ∈ H', ∀ h ∈ H, w * h * w⁻¹ = h := by
      intro w hw h hh
      have := hHH' h hh w hw
      calc w * h * w⁻¹ = (h * w) * w⁻¹ := by rw [this]
        _ = h := by group
    intro n
    constructor
    · intro hn
      rw [hfix w hw n hn]
      exact hn
    · intro hn
      have h2 := hfix w⁻¹ (H'.inv_mem hw) _ hn
      have h3 : n = w⁻¹ * (w * n * w⁻¹) * w⁻¹⁻¹ := by group
      rw [h3, h2]
      exact hn
  have hHnormal : (H.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hnormlz (hLHH' g.2)) n).mp hn
  have hR₁H : R₁ ≤ H := le_iSup (fun R : ↥B => R.1) ⟨R₁, hR₁B⟩
  have hLH : L ≤ H := by
    rcases normal_eq_top_or_le_center hLq hHnormal with h | h
    · exact Subgroup.subgroupOf_eq_top.mp h
    · exact absurd h (hnoncentral H hHL hR₁H)
  by_contra hnl
  have hR₂nB : R₂ ∉ B := fun hB' => hnl hB'.2
  apply hnab R₂ h₂
  intro x hx y hy
  have hxH' : x ∈ H' := (le_iSup (fun R : ↥(Λ \ B) => R.1) ⟨R₂, hR₂Λ, hR₂nB⟩) hx
  have hyH : y ∈ H := hLH (hΛL R₂ hR₂Λ hy)
  exact (hHH' y hyH x hxH').symm

end Abstract

section Model

variable {p : ℕ} [Fact p.Prime]

theorem not_commutes_self_modelFund {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible t n p e) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ ModelFund p t n e) : ¬ Commutes R R := by
  have hperf : Gaps.FundPerfect t (modelUniv t n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 hfund hadm (by omega)
  intro hab
  apply Exotic.fundamentalSubgroups_ne_bot hfund hadm hR
  refine eq_bot_iff.mpr ((hperf R hR).trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_))
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hab x hx y hy

end Model

section Exceptional

variable {p : ℕ} [Fact p.Prime]

theorem linkedIn_modelFund_exceptional {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (hexc : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t n p e) {R R₁ R₂ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ ModelFund p t n e) (hR₁ : R₁ ∈ ModelFund p t n e) (hR₂ : R₂ ∈ ModelFund p t n e)
    (c₁ : Commutes R₁ R) (c₂ : Commutes R₂ R) : LinkedIn (ModelFund p t n e) R R₁ R₂ := by
  have hfund : IsFundTag t := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hperf : Gaps.FundPerfect t (modelUniv t n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 hfund hadm (by omega)
  obtain ⟨L, hLq, hLC, hLperf, -⟩ := Exotic.excLayer hp2 hq t n hexc hadm R hR
  exact linkedIn_of_layer (F := ModelFund p t n e)
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g) hperf
    (fun R' hR' => not_commutes_self_modelFund hp2 hfund hq hadm hR') hLq hLC hLperf hR₁ hR₂ c₁ c₂

end Exceptional

end CFSG.ClassicalInvolution.RouteD
