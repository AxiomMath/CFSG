module

public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.DadeAveragingLeftInverse

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

def dadeZDomain (L : Subgroup G) (A : Set G) : Submodule ℤ (↥L → ℂ) where
  carrier := {f | f ∈ virtualChars ↥L ∧ ∀ x : ↥L, (x : G) ∉ A → f x = 0}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, fun x hx => by simp [hf.2 x hx]⟩

variable {f : ↥L → ℂ}

@[simp]
theorem mem_dadeZDomain :
    f ∈ dadeZDomain L A ↔ f ∈ virtualChars ↥L ∧ ∀ x : ↥L, (x : G) ∉ A → f x = 0 := Iff.rfl

theorem dadeZDomain_le_virtualChars (L : Subgroup G) (A : Set G) :
    dadeZDomain L A ≤ virtualChars ↥L := fun _ hf => hf.1

theorem dadeZDomain.apply_eq_zero (hf : f ∈ dadeZDomain L A) {x : ↥L} (hx : (x : G) ∉ A) :
    f x = 0 := hf.2 x hx

theorem mem_dadeDomain_of_mem_dadeZDomain (hf : f ∈ dadeZDomain L A) : f ∈ dadeDomain L A :=
  mem_dadeDomain_of_mem_span_Irr (virtualChars_le_span_Irr hf.1) hf.2

theorem dadeZDomain_le_dadeDomain (L : Subgroup G) (A : Set G) :
    dadeZDomain L A ≤ (dadeDomain L A).restrictScalars ℤ :=
  fun _ hf => mem_dadeDomain_of_mem_dadeZDomain hf

theorem mem_charSpanZero_Irr {h : G → ℂ} :
    h ∈ charSpanZero (Irr G) ↔ h ∈ virtualChars G ∧ h 1 = 0 := by
  rw [mem_charSpanZero, mem_virtualChars_iff]

section Finite

variable [Finite G]

noncomputable def dadeZMap (hD : IsDadeData L A H) :
    dadeZDomain L A →+ charSpanZero (Irr G) where
  toFun f := ⟨((dadeMap hD ⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain f.2⟩ :
      classFun G) : G → ℂ),
    mem_charSpanZero.2 ⟨hD.dadeMap_mem_span_Irr _ (virtualChars_le_span_Irr f.2.1),
      dadeMap_one_eq_zero hD _⟩⟩
  map_zero' := by
    refine Subtype.ext ?_
    have h0 : (⟨((0 : dadeZDomain L A) : ↥L → ℂ),
        mem_dadeDomain_of_mem_dadeZDomain (0 : dadeZDomain L A).2⟩ : dadeDomain L A) = 0 := rfl
    simp only [h0, map_zero]
    rfl
  map_add' f g := by
    refine Subtype.ext ?_
    have h1 : (⟨((f + g : dadeZDomain L A) : ↥L → ℂ),
        mem_dadeDomain_of_mem_dadeZDomain (f + g).2⟩ : dadeDomain L A)
        = ⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain f.2⟩
          + ⟨(g : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain g.2⟩ := rfl
    simp only [h1, map_add]
    rfl

theorem coe_dadeZMap (hD : IsDadeData L A H) (f : dadeZDomain L A) :
    ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ)
      = ((dadeMap hD ⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain f.2⟩ :
          classFun G) : G → ℂ) := (rfl)

theorem dadeZMap_mem_virtualChars (hD : IsDadeData L A H) (f : dadeZDomain L A) :
    ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ) ∈ virtualChars G :=
  (mem_charSpanZero_Irr.1 (dadeZMap hD f).2).1

theorem dadeZMap_apply_one (hD : IsDadeData L A H) (f : dadeZDomain L A) :
    ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ) 1 = 0 :=
  (mem_charSpanZero_Irr.1 (dadeZMap hD f).2).2

theorem dadeZMap_apply_of_mem_dadeSupport (hD : IsDadeData L A H) (f : dadeZDomain L A) {a : G}
    (ha : a ∈ A) {x : G} (hx : x ∈ dadeSupport H a) :
    ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ) x
      = (f : ↥L → ℂ) ⟨a, hD.mem_of_mem ha⟩ := by
  rw [coe_dadeZMap]; exact dadeMap_apply_of_mem_dadeSupport hD _ ha hx

theorem dadeZMap_apply_mem (hD : IsDadeData L A H) (f : dadeZDomain L A) {a : G} (ha : a ∈ A) :
    ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ) a
      = (f : ↥L → ℂ) ⟨a, hD.mem_of_mem ha⟩ :=
  dadeZMap_apply_of_mem_dadeSupport hD f ha (self_mem_dadeSupport H a)

theorem dadeZMap_eq_zero_of_notMem (hD : IsDadeData L A H) (f : dadeZDomain L A) {x : G}
    (hx : x ∉ totalDadeSupport A H) :
    ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ) x = 0 := by
  rw [coe_dadeZMap]; exact dadeMap_eq_zero_of_notMem hD _ hx

theorem dadeZMap_injective (hD : IsDadeData L A H) : Function.Injective (dadeZMap hD) := by
  intro f g hfg
  have h : (⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain f.2⟩ : dadeDomain L A)
      = ⟨(g : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain g.2⟩ :=
    dadeMap_injective hD (Subtype.ext (by rw [← coe_dadeZMap hD f, ← coe_dadeZMap hD g, hfg]))
  exact Subtype.ext (congrArg (fun z : dadeDomain L A => (z : ↥L → ℂ)) h)

end Finite

section Isometry

variable [Fintype G] [Fintype ↥L]

theorem cfInner_dadeZMap (hD : IsDadeData L A H) (f h : dadeZDomain L A) :
    cfInner ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ)
        ((dadeZMap hD h : charSpanZero (Irr G)) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ) := by
  rw [coe_dadeZMap, coe_dadeZMap]
  exact cfInner_dadeMap hD _ _

theorem cfInner_self_dadeZMap (hD : IsDadeData L A H) (f : dadeZDomain L A) :
    cfInner ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ)
        ((dadeZMap hD f : charSpanZero (Irr G)) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (f : ↥L → ℂ) :=
  cfInner_dadeZMap hD f f

theorem dadeZMap_eq_zero_iff (hD : IsDadeData L A H) (f : dadeZDomain L A) :
    dadeZMap hD f = 0 ↔ f = 0 := by
  refine ⟨fun hf => Subtype.ext ?_, fun hf => by rw [hf, map_zero]⟩
  have hzero : cfInner (f : ↥L → ℂ) (f : ↥L → ℂ) = 0 := by
    rw [← cfInner_self_dadeZMap hD f, hf]
    simp [cfInner_def]
  exact cfInner_self_eq_zero.1 hzero

end Isometry

end CFSG.FeitThompson

end
