module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCalc
public import CFSG.LieType.SeitzGeneration.ExcHighThree.NonEllipticCore

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Fixed


theorem cen_monomial_conj_mem_rootLevel {K : Type} [Field K] {n : ModGL Tag.E6 K}
    (hn : n ∈ monomialSubgroup Tag.E6 K) {v : WeylGroup Tag.E6} (hnv : MapsRootLines n v)
    {l : Fin Tag.E6.rank → ℤ} {m : ℤ}
    (hv : ∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * (v • β) i = ∑ i, l i * β i)
    {y : ModGL Tag.E6 K} (hy : y ∈ rootLevel Tag.E6 K l m) :
    n * y * n⁻¹ ∈ rootLevel Tag.E6 K l m := by
  have hvq : weylQuotientHom Tag.E6 K ⟨n, hn⟩ = v := weylQuotientHom_eq hnv
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, hβm, t, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hβ
    rw [hμ, hvq]
    exact pinnedX_mem_rootLevel (IsRoot.smul hβ v) (by rw [hv]; exact hβm) _
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have e : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem cen_exists_rootLevel_normalized {K : Type} [Field K] [Finite K]
    {l : Fin Tag.E6.rank → ℤ} (hl : l ≠ 0) :
    ∃ R : Subgroup (adjointGroup Tag.E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ (X : MulAut (adjointGroup Tag.E6 K)) (v : WeylGroup Tag.E6), BmMono X v →
        (∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * (v • β) i = ∑ i, l i * β i) →
        R.map X.toMonoidHom = R := by
  obtain ⟨m, hm, ⟨α₀, hα₀, hα₀m⟩, hmax⟩ := exists_max_root_pairing l hl
  have hcomm := E6_level_comm (L := K) l hm hmax
  have : Finite (adjointGroup Tag.E6 K) := generated_group_finite Tag.E6 K
  set R : Subgroup (adjointGroup Tag.E6 K) :=
    (rootLevel Tag.E6 K l m).subgroupOf (adjointGroup Tag.E6 K) with hR
  have hmemR : ∀ g : adjointGroup Tag.E6 K,
      g ∈ R ↔ (g : ModGL Tag.E6 K) ∈ rootLevel Tag.E6 K l m := fun g => Subgroup.mem_subgroupOf
  refine ⟨R, ?_, ?_, ?_⟩
  · intro h
    have h1 : (⟨pinnedX Tag.E6 K α₀ 1, pinnedX_mem_adjointGroup α₀ 1⟩ :
        adjointGroup Tag.E6 K) ∈ R := (hmemR _).2 (pinnedX_mem_rootLevel hα₀ hα₀m 1)
    rw [h, Subgroup.mem_bot] at h1
    have h2 : pinnedX Tag.E6 K α₀ 1 = pinnedX Tag.E6 K α₀ 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (pinnedX_injective Tag.E6 K α₀ h2)
  · intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact rootLevel_pow (ringChar K) hcomm ((hmemR _).1 g.2)
  · intro X v hX hv
    have hle : R.map X.toMonoidHom ≤ R := by
      obtain ⟨n, b, hn, hnv, rfl⟩ := hX
      rintro _ ⟨g, hg, rfl⟩
      exact (hmemR _).2 (cen_monomial_conj_mem_rootLevel hn hnv hv
        (rootLevel_conj_diag b ((hmemR g).1 hg)))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective X.injective])

theorem e6NormalizesR_of_bmMono_fixed {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {l : Fin Tag.E6.rank → ℤ} (hl : l ≠ 0)
    (hE : ∀ X ∈ E, ∃ v : WeylGroup Tag.E6, BmMono X v ∧
      ∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * (v • β) i = ∑ i, l i * β i) :
    E6NormalizesR K E := by
  obtain ⟨R, hR1, hRp, hRX⟩ := cen_exists_rootLevel_normalized (K := K) hl
  refine ⟨R, hR1, hRp, fun ε hε => ?_⟩
  obtain ⟨v, hX, hv⟩ := hE ε hε
  exact hRX ε v hX hv

end Fixed

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
