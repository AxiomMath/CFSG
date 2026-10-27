module

public import CFSG.Fischer.Pairs
public import CFSG.Fischer.Classification.Defs
public import CFSG.Fischer.Classification.Symplectic.Basic
import CFSG.Fischer.Classification.Basic.Center
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.Fischer.Classification.Symplectic

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {X : Type} [Group X]

section Ncomm

@[expose] def ncomm (e f : X) : ZMod 2 := by
  classical exact if e * f = f * e then 0 else 1

theorem ncomm_eq_zero_iff {e f : X} : ncomm e f = 0 ↔ e * f = f * e := by
  classical
  unfold ncomm
  split_ifs with h <;> simp [h]

theorem ncomm_eq_one_iff {e f : X} : ncomm e f = 1 ↔ e * f ≠ f * e := by
  classical
  unfold ncomm
  split_ifs with h <;> simp [h]

theorem ncomm_of_commute {e f : X} (h : e * f = f * e) : ncomm e f = 0 :=
  ncomm_eq_zero_iff.2 h

theorem ncomm_of_not_commute {e f : X} (h : e * f ≠ f * e) : ncomm e f = 1 :=
  ncomm_eq_one_iff.2 h

theorem ncomm_comm (e f : X) : ncomm e f = ncomm f e := by
  by_cases h : e * f = f * e
  · rw [ncomm_of_commute h, ncomm_of_commute h.symm]
  · rw [ncomm_of_not_commute h, ncomm_of_not_commute (Ne.symm h)]

theorem ncomm_self (e : X) : ncomm e e = 0 :=
  ncomm_of_commute rfl

theorem ncomm_conj (g e f : X) : ncomm (g * e * g⁻¹) (g * f * g⁻¹) = ncomm e f := by
  have : g * e * g⁻¹ * (g * f * g⁻¹) = g * f * g⁻¹ * (g * e * g⁻¹) ↔ e * f = f * e := by
    constructor
    · intro h
      have h' := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using h'
    · intro h
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc e f, h, mul_assoc]
  by_cases h : e * f = f * e
  · rw [ncomm_of_commute h, ncomm_of_commute (this.2 h)]
  · rw [ncomm_of_not_commute h, ncomm_of_not_commute (mt this.1 h)]

variable {E : Set X}

theorem ncomm_line (hP : Pair X E) (hsymp : IsSymplecticType E) {d f g : X} (hd : d ∈ E)
    (hf : f ∈ E) (hg : g ∈ E) (hdf : d * f ≠ f * d) :
    ncomm d g + ncomm f g + ncomm (d * f * d) g = 0 := by
  classical
  have hdd := Pair.mul_self hP hd
  have hff := Pair.mul_self hP hf
  have hbraid := Pair.mul_mul_eq hP hd hf hdf
  have h12 : g * d = d * g → g * f = f * g → g * (d * f * d) = d * f * d * g := fun h1 h2 => by
    calc g * (d * f * d) = (g * d) * f * d := by simp only [mul_assoc]
      _ = d * (g * f) * d := by rw [h1]; simp only [mul_assoc]
      _ = d * f * (g * d) := by rw [h2]; simp only [mul_assoc]
      _ = d * f * d * g := by rw [h1]; simp only [mul_assoc]
  have hdfd : d * (d * f * d) * d = f := by
    calc d * (d * f * d) * d = (d * d) * f * (d * d) := by simp only [mul_assoc]
      _ = f := by rw [hdd, one_mul, mul_one]
  have hfdf : f * (d * f * d) * f = d := by
    calc f * (d * f * d) * f = f * (f * d * f) * f := by rw [hbraid]
      _ = (f * f) * d * (f * f) := by simp only [mul_assoc]
      _ = d := by rw [hff, one_mul, mul_one]
  have hcomm3 : ∀ a c : X, g * a = a * g → g * c = c * g → g * (a * c * a) = a * c * a * g :=
    fun a c ha hc => by
      calc g * (a * c * a) = (g * a) * c * a := by simp only [mul_assoc]
        _ = a * (g * c) * a := by rw [ha]; simp only [mul_assoc]
        _ = a * c * (g * a) := by rw [hc]; simp only [mul_assoc]
        _ = a * c * a * g := by rw [ha]; simp only [mul_assoc]
  have h13 : g * d = d * g → g * (d * f * d) = d * f * d * g → g * f = f * g := fun h1 h3 => by
    have := hcomm3 d (d * f * d) h1 h3
    rwa [hdfd] at this
  have h23 : g * f = f * g → g * (d * f * d) = d * f * d * g → g * d = d * g := fun h2 h3 => by
    have := hcomm3 f (d * f * d) h2 h3
    rwa [hfdf] at this
  have hone := hsymp d hd f hf g hg hdf
  have key : ∀ a : X, ncomm a g = if g * a = a * g then 0 else 1 := fun a => by
    by_cases h : g * a = a * g
    · simp only [h, ite_true]
      exact ncomm_of_commute h.symm
    · simp only [h, ite_false]
      exact ncomm_of_not_commute (Ne.symm h)
  rw [key, key, key]
  by_cases c1 : g * d = d * g <;> by_cases c2 : g * f = f * g <;>
    by_cases c3 : g * (d * f * d) = d * f * d * g <;>
    simp only [c1, c2, c3, ite_true, ite_false] <;> first
      | decide
      | exact absurd (h12 c1 c2) c3
      | exact absurd (h13 c1 c3) c2
      | exact absurd (h23 c2 c3) c1
      | exact absurd hone (by tauto)

end Ncomm

section Free

variable (E : Set X)

@[expose] def freeForm : LinearMap.BilinForm (ZMod 2) (E →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) fun e : E =>
    Finsupp.linearCombination (ZMod 2) fun f : E => ncomm (e : X) f

theorem freeForm_single (e f : E) (a c : ZMod 2) :
    freeForm E (Finsupp.single e a) (Finsupp.single f c) = a * (c * ncomm (e : X) f) := by
  simp [freeForm, Finsupp.linearCombination_single]

theorem freeForm_comm (φ ψ : E →₀ ZMod 2) : freeForm E φ ψ = freeForm E ψ φ := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ₁ φ₂ h₁ h₂ => simp [h₁, h₂]
  | single e a =>
    induction ψ using Finsupp.induction_linear with
    | zero => simp
    | add ψ₁ ψ₂ h₁ h₂ => simp [h₁, h₂]
    | single f c =>
      rw [freeForm_single, freeForm_single, ncomm_comm]
      ring

theorem freeForm_self (φ : E →₀ ZMod 2) : freeForm E φ φ = 0 := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ₁ φ₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂, zero_add, add_zero]
    rw [freeForm_comm E φ₂ φ₁]
    exact zmod_two_add_self _
  | single e a => rw [freeForm_single, ncomm_self, mul_zero, mul_zero]

theorem mem_ker_freeForm {φ : E →₀ ZMod 2} :
    φ ∈ LinearMap.ker (freeForm E) ↔ ∀ ψ, freeForm E φ ψ = 0 := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  rfl

abbrev SympModule := (E →₀ ZMod 2) ⧸ LinearMap.ker (freeForm E)

@[expose] def sympFormAux :
    SympModule E →ₗ[ZMod 2] (E →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.ker (freeForm E)).liftQ (freeForm E) le_rfl

theorem sympFormAux_mk (φ ψ : E →₀ ZMod 2) :
    sympFormAux E (Submodule.Quotient.mk φ) ψ = freeForm E φ ψ :=
  rfl

theorem ker_freeForm_le_ker_flip :
    LinearMap.ker (freeForm E) ≤ LinearMap.ker (sympFormAux E).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
    sympFormAux_mk, LinearMap.zero_comp, LinearMap.zero_apply]
  rw [freeForm_comm]
  exact (mem_ker_freeForm E).1 hr φ

@[expose] def sympForm : LinearMap.BilinForm (ZMod 2) (SympModule E) :=
  ((LinearMap.ker (freeForm E)).liftQ (sympFormAux E).flip (ker_freeForm_le_ker_flip E)).flip

theorem sympForm_mk (φ ψ : E →₀ ZMod 2) :
    sympForm E (Submodule.Quotient.mk φ) (Submodule.Quotient.mk ψ) = freeForm E φ ψ :=
  rfl

variable {E}

@[expose] def bar (e : E) : SympModule E :=
  Submodule.Quotient.mk (Finsupp.single e 1)

theorem sympForm_bar (e f : E) : sympForm E (bar e) (bar f) = ncomm (e : X) f := by
  rw [bar, bar, sympForm_mk, freeForm_single, one_mul, one_mul]

variable (E)

theorem sympForm_comm (v w : SympModule E) : sympForm E v w = sympForm E w v := by
  induction v using Submodule.Quotient.induction_on with
  | H φ =>
    induction w using Submodule.Quotient.induction_on with
    | H ψ => rw [sympForm_mk, sympForm_mk, freeForm_comm]

theorem sympForm_self (v : SympModule E) : sympForm E v v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H φ => rw [sympForm_mk, freeForm_self]

theorem sympForm_nondegenerate (v : SympModule E) (hv : ∀ w, sympForm E v w = 0) : v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H φ =>
    rw [Submodule.Quotient.mk_eq_zero, mem_ker_freeForm]
    exact fun ψ => hv (Submodule.Quotient.mk ψ)

theorem span_range_bar : Submodule.span (ZMod 2) (Set.range (bar (E := E))) = ⊤ := by
  have h : Set.range (bar (E := E)) =
      (LinearMap.ker (freeForm E)).mkQ '' Set.range (Finsupp.basisSingleOne (R := ZMod 2)) := by
    ext v
    simp [bar]
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_mkQ]

end Free

section Action

variable {E : Set X}

@[expose] def freeRep (hP : Pair X E) : X →* (E →₀ ZMod 2) ≃ₗ[ZMod 2] (E →₀ ZMod 2) where
  toFun g := Finsupp.domLCongr (Pair.conjPerm hP g)
  map_one' := by
    rw [map_one]
    exact Finsupp.domLCongr_refl
  map_mul' g h := by
    rw [map_mul, LinearEquiv.mul_eq_trans, Finsupp.domLCongr_trans]
    rfl

theorem freeRep_single (hP : Pair X E) (g : X) (e : E) (a : ZMod 2) :
    freeRep hP g (Finsupp.single e a) = Finsupp.single (Pair.conjPerm hP g e) a :=
  Finsupp.domLCongr_single _ _ _

theorem freeForm_freeRep (hP : Pair X E) (g : X) (φ ψ : E →₀ ZMod 2) :
    freeForm E (freeRep hP g φ) (freeRep hP g ψ) = freeForm E φ ψ := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ₁ φ₂ h₁ h₂ => simp [h₁, h₂]
  | single e a =>
    induction ψ using Finsupp.induction_linear with
    | zero => simp
    | add ψ₁ ψ₂ h₁ h₂ => simp [h₁, h₂]
    | single f c =>
      rw [freeRep_single, freeRep_single, freeForm_single, freeForm_single, Pair.conjPerm_apply,
        Pair.conjPerm_apply, ncomm_conj]

theorem map_ker_freeForm (hP : Pair X E) (g : X) :
    (LinearMap.ker (freeForm E)).map (freeRep hP g : (E →₀ ZMod 2) →ₗ[ZMod 2] (E →₀ ZMod 2)) =
      LinearMap.ker (freeForm E) := by
  ext φ
  rw [Submodule.mem_map_equiv, mem_ker_freeForm, mem_ker_freeForm]
  constructor
  · intro h ψ
    have := h ((freeRep hP g).symm ψ)
    rwa [← freeForm_freeRep hP g, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      at this
  · intro h ψ
    rw [← freeForm_freeRep hP g, LinearEquiv.apply_symm_apply]
    exact h _

@[expose] def rho (hP : Pair X E) : X →* SympModule E ≃ₗ[ZMod 2] SympModule E where
  toFun g := Submodule.Quotient.equiv _ _ (freeRep hP g) (map_ker_freeForm hP g)
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H φ => simp
  map_mul' g h := by
    refine LinearEquiv.ext fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H φ => simp [LinearEquiv.mul_apply]

theorem rho_mk (hP : Pair X E) (g : X) (φ : E →₀ ZMod 2) :
    rho hP g (Submodule.Quotient.mk φ) = Submodule.Quotient.mk (freeRep hP g φ) :=
  rfl

theorem rho_bar (hP : Pair X E) (g : X) (e : E) :
    rho hP g (bar e) = bar (Pair.conjPerm hP g e) := by
  rw [bar, rho_mk, freeRep_single, bar]

theorem sympForm_rho (hP : Pair X E) (g : X) (v w : SympModule E) :
    sympForm E (rho hP g v) (rho hP g w) = sympForm E v w := by
  induction v using Submodule.Quotient.induction_on with
  | H φ =>
    induction w using Submodule.Quotient.induction_on with
    | H ψ => rw [rho_mk, rho_mk, sympForm_mk, sympForm_mk, freeForm_freeRep]

theorem eq_of_sympForm_bar (v w : SympModule E) (h : ∀ e : E, sympForm E v (bar e) =
    sympForm E w (bar e)) : v = w := by
  have hlin : sympForm E v = sympForm E w :=
    LinearMap.ext_on_range (span_range_bar E) h
  rw [← sub_eq_zero]
  refine sympForm_nondegenerate E _ fun u => ?_
  rw [map_sub, LinearMap.sub_apply, hlin, sub_self]

theorem rho_apply_eq (hP : Pair X E) (hsymp : IsSymplecticType E) (d : E) (v : SympModule E) :
    rho hP d v = v + sympForm E v (bar d) • bar d := by
  have key : (rho hP d).toLinearMap =
      LinearMap.id + ((sympForm E).flip (bar d)).smulRight (bar d) := by
    refine LinearMap.ext_on_range (span_range_bar E) fun f => ?_
    simp only [LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, rho_bar]
    rw [LinearMap.BilinForm.flip_apply, sympForm_bar]
    by_cases hfd : (f : X) * d = d * f
    · rw [ncomm_of_commute hfd, zero_smul, add_zero]
      congr 1
      apply Subtype.ext
      rw [Pair.conjPerm_apply, ← hfd, mul_assoc, mul_inv_cancel, mul_one]
    · rw [ncomm_of_not_commute hfd, one_smul]
      have hd := d.2
      have hinv : (d : X)⁻¹ = d := Pair.inv_eq hP hd
      refine eq_of_sympForm_bar _ _ fun g => ?_
      rw [map_add, LinearMap.add_apply, sympForm_bar, sympForm_bar, sympForm_bar,
        Pair.conjPerm_apply, hinv]
      have hl := ncomm_line hP hsymp hd f.2 g.2 (fun h => hfd h.symm)
      exact zmod_two_eq_of_add_add _ _ _ hl
  exact LinearMap.congr_fun key v

end Action

section Faithful

variable {E : Set X}

theorem rho_injective (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hsymp : IsSymplecticType E) :
    Function.Injective (rho hP) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hle := commutator_le_of_normal hZ hS hne
  obtain ⟨d, hd, e, he, hde⟩ := Pair.exists_not_commute hP hZ
  have hmem : ⁅d, e⁆ ∈ commutator X := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top d) (Subgroup.mem_top e)
  have h1 : rho hP ⁅d, e⁆ = 1 := hle hmem
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  have h2 := congrArg (fun φ : SympModule E ≃ₗ[ZMod 2] SympModule E => φ (bar ⟨d, hd⟩)) h1
  simp only [LinearEquiv.mul_apply] at h2
  have hd' : rho hP d = rho hP ((⟨d, hd⟩ : E) : X) := rfl
  have he' : rho hP e = rho hP ((⟨e, he⟩ : E) : X) := rfl
  rw [hd', he', rho_apply_eq hP hsymp ⟨e, he⟩, rho_apply_eq hP hsymp ⟨d, hd⟩,
    rho_apply_eq hP hsymp ⟨d, hd⟩, rho_apply_eq hP hsymp ⟨e, he⟩] at h2
  simp only [sympForm_self, zero_smul, add_zero, sympForm_bar, map_add, LinearMap.add_apply,
    ncomm_of_not_commute hde, ncomm_of_not_commute (Ne.symm hde), one_smul] at h2
  have h3 : bar (⟨d, hd⟩ : E) = 0 := by
    have := congrArg (· - (bar (⟨d, hd⟩ : E) + bar (⟨e, he⟩ : E))) h2
    simpa using this
  have h4 := sympForm_bar (⟨d, hd⟩ : E) ⟨e, he⟩
  rw [h3, map_zero, LinearMap.zero_apply, ncomm_of_not_commute hde] at h4
  exact zero_ne_one h4

end Faithful

end CFSG.Fischer.Classification.Symplectic
