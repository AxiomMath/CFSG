module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.G2QuotientSetup

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open scoped commutatorElement

section Action

variable
  {K : Type} [Field K]

instance factClassTwoG2 : Fact (ClassTwo (Qg K) (Zg K)) := ⟨classTwoG2⟩

theorem isQRoot_a : IsQRoot gA := Or.inl rfl
theorem isQRoot_u : IsQRoot gU := Or.inr (Or.inl rfl)
theorem isQRoot_v : IsQRoot gV := Or.inr (Or.inr (Or.inl rfl))
theorem isQRoot_b : IsQRoot gB := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem isQRoot_c : IsQRoot gC := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem Xr_normalizes (t : K) :
    ∀ q ∈ Qg K, pinnedX .G2 K gR t * q * (pinnedX .G2 K gR t)⁻¹ ∈ Qg K := by
  refine conj_mem_closure (S := genSet K) ?_
  rintro _ ⟨γ, hγ, c, rfl⟩
  have key : ∀ (x : ModGL .G2 K), pinnedX .G2 K gR t * x * (pinnedX .G2 K gR t)⁻¹ =
      (pinnedX .G2 K gR t * x * (pinnedX .G2 K gR t)⁻¹ * x⁻¹) * x := fun x => conj_eq_comm_mul _ _
  have hQ := fun {δ} (hδ : IsQRoot δ) (d : K) => X_mem_Qg (K := K) hδ d
  rcases hγ with rfl | rfl | rfl | rfl | rfl
  · rw [key]
    have := comm_r_a t c
    rw [commutatorElement_def] at this
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQ isQRoot_u _) (Subgroup.mul_mem _ (hQ isQRoot_v _)
      (Subgroup.mul_mem _ (hQ isQRoot_b _) (hQ isQRoot_c _)))) (hQ isQRoot_a _)
  · rw [key]
    have := comm_r_u t c
    rw [commutatorElement_def] at this
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQ isQRoot_v _) (Subgroup.mul_mem _ (hQ isQRoot_c _)
      (hQ isQRoot_b _))) (hQ isQRoot_u _)
  · rw [key]
    have := comm_r_v t c
    rw [commutatorElement_def] at this
    rw [this]
    exact Subgroup.mul_mem _ (hQ isQRoot_b _) (hQ isQRoot_v _)
  · rw [conj_eq_of_mul_comm (commute_r_b t c).eq]
    exact hQ isQRoot_b _
  · rw [conj_eq_of_mul_comm (commute_r_c t c).eq]
    exact hQ isQRoot_c _

theorem nR_normalizes :
    ∀ q ∈ Qg K, weylElt .G2 K iR 1 * q * (weylElt .G2 K iR 1)⁻¹ ∈ Qg K := by
  refine conj_mem_closure (S := genSet K) ?_
  rintro _ ⟨γ, hγ, c, rfl⟩
  have hQ := fun {{δ}} (hδ : IsQRoot δ) (d : K) => X_mem_Qg (K := K) hδ d
  rcases hγ with rfl | rfl | rfl | rfl | rfl
  · rw [nR_a]; exact hQ isQRoot_b _
  · rw [nR_u]; exact hQ isQRoot_v _
  · rw [nR_v]; exact hQ isQRoot_u _
  · rw [nR_b]; exact hQ isQRoot_a _
  · rw [nR_c]; exact hQ isQRoot_c _

theorem Xr_Z (t : K) : ∀ z ∈ Zg K, pinnedX .G2 K gR t * z * (pinnedX .G2 K gR t)⁻¹ ∈ Zg K := by
  intro z hz
  obtain ⟨c, rfl⟩ := mem_Zg.1 hz
  rw [conj_eq_of_mul_comm (commute_r_c t c).eq]
  exact X_mem_Zg _

theorem nR_Z : ∀ z ∈ Zg K, weylElt .G2 K iR 1 * z * (weylElt .G2 K iR 1)⁻¹ ∈ Zg K := by
  intro z hz
  obtain ⟨c, rfl⟩ := mem_Zg.1 hz
  rw [nR_c]
  exact X_mem_Zg _

open Classical in
@[expose] def clsT (g : ModGL .G2 K) : V (Qg K) (Zg K) :=
  if h : g ∈ Qg K then ClassTwo.cls (⟨g, h⟩ : Qg K) else 0

theorem clsT_of_mem {g : ModGL .G2 K} (h : g ∈ Qg K) :
    clsT g = ClassTwo.cls (⟨g, h⟩ : Qg K) := by
  simp [clsT, h]

theorem clsT_mul {g h : ModGL .G2 K} (hg : g ∈ Qg K) (hh : h ∈ Qg K) :
    clsT (g * h) = clsT g + clsT h := by
  rw [clsT_of_mem hg, clsT_of_mem hh, clsT_of_mem (Subgroup.mul_mem _ hg hh)]
  exact ClassTwo.cls_mul (⟨g, hg⟩ : Qg K) ⟨h, hh⟩

theorem clsT_Z {g : ModGL .G2 K} (hg : g ∈ Zg K) : clsT g = 0 := by
  have hQ : g ∈ Qg K := classTwoG2.le hg
  rw [clsT_of_mem hQ, ← ClassTwo.cls_one (Q := Qg K) (Z := Zg K), ClassTwo.cls_eq_iff]
  simpa using hg

theorem clsT_eq_iff {g h : ModGL .G2 K} (hg : g ∈ Qg K) (hh : h ∈ Qg K) :
    clsT g = clsT h ↔ g⁻¹ * h ∈ Zg K := by
  rw [clsT_of_mem hg, clsT_of_mem hh, ClassTwo.cls_eq_iff]
  rfl

@[expose] def cx (t : K) : V (Qg K) (Zg K) →+ V (Qg K) (Zg K) :=
  ClassTwo.conjV (pinnedX .G2 K gR t) (Xr_normalizes t) (Xr_Z t)

@[expose] def cn : V (Qg K) (Zg K) →+ V (Qg K) (Zg K) :=
  ClassTwo.conjV (weylElt .G2 K iR 1) nR_normalizes nR_Z

theorem cx_clsT (t : K) {g : ModGL .G2 K} (hg : g ∈ Qg K) :
    cx t (clsT g) = clsT (pinnedX .G2 K gR t * g * (pinnedX .G2 K gR t)⁻¹) := by
  rw [clsT_of_mem hg, clsT_of_mem (Xr_normalizes t g hg)]
  exact ClassTwo.conjV_cls _ _ _ ⟨g, hg⟩

theorem cn_clsT {g : ModGL .G2 K} (hg : g ∈ Qg K) :
    cn (clsT g) = clsT (weylElt .G2 K iR 1 * g * (weylElt .G2 K iR 1)⁻¹) := by
  rw [clsT_of_mem hg, clsT_of_mem (nR_normalizes g hg)]
  exact ClassTwo.conjV_cls _ _ _ ⟨g, hg⟩

theorem cx_a (t s : K) :
    cx t (clsT (pinnedX .G2 K gA s)) = clsT (pinnedX .G2 K gA s) +
      clsT (pinnedX .G2 K gU (-(t * s))) + clsT (pinnedX .G2 K gV (t ^ 2 * s)) +
      clsT (pinnedX .G2 K gB (t ^ 3 * s)) := by
  have hc := comm_r_a t s
  rw [commutatorElement_def] at hc
  have ma := X_mem_Qg (K := K) isQRoot_a s
  have mu := X_mem_Qg (K := K) isQRoot_u (-(t * s))
  have mv := X_mem_Qg (K := K) isQRoot_v (t ^ 2 * s)
  have mb := X_mem_Qg (K := K) isQRoot_b (t ^ 3 * s)
  have mc := X_mem_Qg (K := K) isQRoot_c (2 * t ^ 3 * s ^ 2)
  rw [cx_clsT t ma, conj_eq_comm_mul, hc,
    clsT_mul (Subgroup.mul_mem _ mu (Subgroup.mul_mem _ mv (Subgroup.mul_mem _ mb mc))) ma,
    clsT_mul mu (Subgroup.mul_mem _ mv (Subgroup.mul_mem _ mb mc)),
    clsT_mul mv (Subgroup.mul_mem _ mb mc), clsT_mul mb mc, clsT_Z (X_mem_Zg _)]
  abel

theorem cx_u (t s : K) :
    cx t (clsT (pinnedX .G2 K gU s)) = clsT (pinnedX .G2 K gU s) +
      clsT (pinnedX .G2 K gV (-(2 * t * s))) + clsT (pinnedX .G2 K gB (-(3 * t ^ 2 * s))) := by
  have hc := comm_r_u t s
  rw [commutatorElement_def] at hc
  have mu := X_mem_Qg (K := K) isQRoot_u s
  have mv := X_mem_Qg (K := K) isQRoot_v (-(2 * t * s))
  have mc := X_mem_Qg (K := K) isQRoot_c (-(3 * t * s ^ 2))
  have mb := X_mem_Qg (K := K) isQRoot_b (-(3 * t ^ 2 * s))
  have hcb := Subgroup.mul_mem _ mc mb
  rw [cx_clsT t mu, conj_eq_comm_mul, hc, clsT_mul (Subgroup.mul_mem _ mv hcb) mu,
    clsT_mul mv hcb, clsT_mul mc mb, clsT_Z (X_mem_Zg _)]
  abel

theorem cx_v (t s : K) :
    cx t (clsT (pinnedX .G2 K gV s)) = clsT (pinnedX .G2 K gV s) +
      clsT (pinnedX .G2 K gB (3 * t * s)) := by
  have hc := comm_r_v t s
  rw [commutatorElement_def] at hc
  have mv := X_mem_Qg (K := K) isQRoot_v s
  have mb := X_mem_Qg (K := K) isQRoot_b (3 * t * s)
  rw [cx_clsT t mv, conj_eq_comm_mul, hc, clsT_mul mb mv]
  abel

theorem cx_b (t s : K) :
    cx t (clsT (pinnedX .G2 K gB s)) = clsT (pinnedX .G2 K gB s) := by
  rw [cx_clsT t (X_mem_Qg (K := K) isQRoot_b s), conj_eq_of_mul_comm (commute_r_b t s).eq]

theorem cn_a (s : K) : cn (clsT (pinnedX .G2 K gA s)) = clsT (pinnedX .G2 K gB s) := by
  rw [cn_clsT (X_mem_Qg (K := K) isQRoot_a s), nR_a]

theorem cn_b (s : K) : cn (clsT (pinnedX .G2 K gB s)) = clsT (pinnedX .G2 K gA (-s)) := by
  rw [cn_clsT (X_mem_Qg (K := K) isQRoot_b s), nR_b]

theorem cn_u (s : K) : cn (clsT (pinnedX .G2 K gU s)) = clsT (pinnedX .G2 K gV s) := by
  rw [cn_clsT (X_mem_Qg (K := K) isQRoot_u s), nR_u]

theorem cn_v (s : K) : cn (clsT (pinnedX .G2 K gV s)) = clsT (pinnedX .G2 K gU (-s)) := by
  rw [cn_clsT (X_mem_Qg (K := K) isQRoot_v s), nR_v]

end Action

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
