module

public import CFSG.Fischer.Classification.PartII.O2Mono
public import CFSG.Fischer.Classification.Symplectic.Basic
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

abbrev XT (E μ : Set H) := {f : H // f ∈ E ∧ f ∉ μ}

@[expose] def bform (μ : Set H) (f g : H) : ZMod 2 := by
  classical exact if f * g ≠ g * f ∧ f * g * f ∉ μ then 1 else 0

theorem bform_eq_one_iff {f g : H} : bform μ f g = 1 ↔ f * g ≠ g * f ∧ f * g * f ∉ μ := by
  classical
  unfold bform
  split_ifs with h <;> simp [h]

theorem bform_eq_zero_iff {f g : H} : bform μ f g = 0 ↔ ¬ (f * g ≠ g * f ∧ f * g * f ∉ μ) := by
  classical
  unfold bform
  split_ifs with h <;> simp [h]

theorem bform_of_commute {f g : H} (h : f * g = g * f) : bform μ f g = 0 :=
  bform_eq_zero_iff.2 fun h' => h'.1 h

theorem bform_of_mem {f g : H} (h : f * g * f ∈ μ) : bform μ f g = 0 :=
  bform_eq_zero_iff.2 fun h' => h'.2 h

theorem bform_of_not_mem {f g : H} (hfg : f * g ≠ g * f) (h : f * g * f ∉ μ) :
    bform μ f g = 1 :=
  bform_eq_one_iff.2 ⟨hfg, h⟩

theorem bform_comm (hP : Pair H E) {f g : H} (hf : f ∈ E) (hg : g ∈ E) :
    bform μ f g = bform μ g f := by
  by_cases hfg : f * g = g * f
  · rw [bform_of_commute hfg, bform_of_commute hfg.symm]
  · have e := Pair.mul_mul_eq hP hf hg hfg
    by_cases hm : f * g * f ∈ μ
    · rw [bform_of_mem hm, bform_of_mem (e ▸ hm)]
    · rw [bform_of_not_mem hfg hm, bform_of_not_mem (fun h => hfg h.symm) (e ▸ hm)]

section Free

variable (E μ)

@[expose] def freeForm : LinearMap.BilinForm (ZMod 2) (XT E μ →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) fun f : XT E μ =>
    Finsupp.linearCombination (ZMod 2) fun g : XT E μ => bform μ (f : H) g

theorem freeForm_single (f g : XT E μ) (a c : ZMod 2) :
    freeForm E μ (Finsupp.single f a) (Finsupp.single g c) = a * (c * bform μ (f : H) g) := by
  simp [freeForm, Finsupp.linearCombination_single]

variable {E μ}

theorem freeForm_comm (hP : Pair H E) (φ ψ : XT E μ →₀ ZMod 2) :
    freeForm E μ φ ψ = freeForm E μ ψ φ := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ₁ φ₂ h₁ h₂ => simp [h₁, h₂]
  | single f a =>
    induction ψ using Finsupp.induction_linear with
    | zero => simp
    | add ψ₁ ψ₂ h₁ h₂ => simp [h₁, h₂]
    | single g c =>
      rw [freeForm_single, freeForm_single, bform_comm hP f.2.1 g.2.1]
      ring

theorem mem_ker_freeForm {φ : XT E μ →₀ ZMod 2} :
    φ ∈ LinearMap.ker (freeForm E μ) ↔ ∀ ψ, freeForm E μ φ ψ = 0 := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  rfl

variable (E μ)

abbrev SecModule := (XT E μ →₀ ZMod 2) ⧸ LinearMap.ker (freeForm E μ)

@[expose] def secFormAux :
    SecModule E μ →ₗ[ZMod 2] (XT E μ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.ker (freeForm E μ)).liftQ (freeForm E μ) le_rfl

theorem secFormAux_mk (φ ψ : XT E μ →₀ ZMod 2) :
    secFormAux E μ (Submodule.Quotient.mk φ) ψ = freeForm E μ φ ψ :=
  rfl

variable {E μ}

theorem ker_freeForm_le_ker_flip (hP : Pair H E) :
    LinearMap.ker (freeForm E μ) ≤ LinearMap.ker (secFormAux E μ).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
    secFormAux_mk, LinearMap.zero_comp, LinearMap.zero_apply]
  rw [freeForm_comm hP]
  exact mem_ker_freeForm.1 hr φ

@[expose] def secForm (hP : Pair H E) : LinearMap.BilinForm (ZMod 2) (SecModule E μ) :=
  ((LinearMap.ker (freeForm E μ)).liftQ (secFormAux E μ).flip
    (ker_freeForm_le_ker_flip hP)).flip

theorem secForm_mk (hP : Pair H E) (φ ψ : XT E μ →₀ ZMod 2) :
    secForm hP (Submodule.Quotient.mk φ) (Submodule.Quotient.mk ψ) = freeForm E μ φ ψ :=
  rfl

@[expose] def vec (f : XT E μ) : SecModule E μ :=
  Submodule.Quotient.mk (Finsupp.single f 1)

theorem secForm_vec (hP : Pair H E) (f g : XT E μ) :
    secForm hP (vec f) (vec g) = bform μ (f : H) g := by
  rw [vec, vec, secForm_mk, freeForm_single, one_mul, one_mul]

theorem secForm_comm (hP : Pair H E) (v w : SecModule E μ) :
    secForm hP v w = secForm hP w v := by
  induction v using Submodule.Quotient.induction_on with
  | H φ =>
    induction w using Submodule.Quotient.induction_on with
    | H ψ => rw [secForm_mk, secForm_mk, freeForm_comm hP]

theorem secForm_nondegenerate (hP : Pair H E) (v : SecModule E μ)
    (hv : ∀ w, secForm hP v w = 0) : v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H φ =>
    rw [Submodule.Quotient.mk_eq_zero, mem_ker_freeForm]
    exact fun ψ => hv (Submodule.Quotient.mk ψ)

variable (E μ) in
theorem span_range_vec : Submodule.span (ZMod 2) (Set.range (vec (E := E) (μ := μ))) = ⊤ := by
  have h : Set.range (vec (E := E) (μ := μ)) =
      (LinearMap.ker (freeForm E μ)).mkQ '' Set.range (Finsupp.basisSingleOne (R := ZMod 2)) := by
    ext v
    simp [vec]
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_mkQ]

theorem eq_of_secForm_vec (hP : Pair H E) {v w : SecModule E μ}
    (h : ∀ g : XT E μ, secForm hP v (vec g) = secForm hP w (vec g)) : v = w := by
  rw [← sub_eq_zero]
  refine secForm_nondegenerate hP _ fun u => ?_
  have hu : u ∈ Submodule.span (ZMod 2) (Set.range (vec (E := E) (μ := μ))) := by
    rw [span_range_vec]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [map_sub, LinearMap.sub_apply, h g, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

end Free

end O2Mod

end CFSG.Fischer.Classification
