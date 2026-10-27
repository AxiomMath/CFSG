module

public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Representations.DadeIntegerIsometry
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.TISetDadeData

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G}

theorem isTIWithNormalizer_of_conj_image_eq_or_disjoint (hne : A.Nonempty) (h1 : (1 : G) ∉ A)
    (hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅)
    (hL : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L) :
    IsTIWithNormalizer A L :=
  isTIWithNormalizer_of_stabilizer_eq hne h1 hL fun g hg => by
    rcases hTI g with h | h
    · exact absurd ((hL g).1 h) hg
    · rw [Set.inter_comm]; exact h

theorem indClassFun_sub {X : Type*} [Group X] [Fintype X] (K : Subgroup X) (θ ψ : ↥K → ℂ) :
    indClassFun K (θ - ψ) = indClassFun K θ - indClassFun K ψ := by
  have h : θ - ψ = θ + (-1 : ℂ) • ψ := by module
  rw [h, indClassFun_add, indClassFun_smul]
  module

namespace IsTIWithNormalizer

variable [Fintype G]

theorem cfInner_indClassFun [Fintype ↥L] (hTI : IsTIWithNormalizer A L) {f h : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A) (hh : h ∈ dadeDomain L A) :
    cfInner (indClassFun L f) (indClassFun L h) = cfInner f h := by
  have hD := hTI.isDadeData
  rw [← dadeMap_eq_indClassFun hD hTI subset_rfl f hf,
    ← dadeMap_eq_indClassFun hD hTI subset_rfl h hh]
  exact cfInner_dadeMap hD _ _

theorem cfInner_self_indClassFun [Fintype ↥L] (hTI : IsTIWithNormalizer A L) {f : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A) :
    cfInner (indClassFun L f) (indClassFun L f) = cfInner f f :=
  hTI.cfInner_indClassFun hf hf

theorem indClassFun_injOn (hTI : IsTIWithNormalizer A L) {f h : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A) (hh : h ∈ dadeDomain L A)
    (hfh : indClassFun L f = indClassFun L h) : f = h := by
  have : Fintype ↥L := Fintype.ofFinite _
  refine sub_eq_zero.1 (cfInner_self_eq_zero.1 ?_)
  rw [← hTI.cfInner_self_indClassFun (sub_mem hf hh), indClassFun_sub, hfh, sub_self]
  simp [cfInner_def]

theorem indClassFun_apply_one (hTI : IsTIWithNormalizer A L) {f : ↥L → ℂ}
    (hf : ∀ x : ↥L, (x : G) ∉ A → f x = 0) : indClassFun L f 1 = 0 := by
  rw [indClassFun_one, hf 1 (by simpa using hTI.one_notMem), mul_zero]

theorem indClassFun_mem_virtualChars (hTI : IsTIWithNormalizer A L) {f : ↥L → ℂ}
    (hf : f ∈ dadeZDomain L A) : indClassFun L f ∈ virtualChars G := by
  have hD := hTI.isDadeData
  rw [← dadeMap_eq_indClassFun hD hTI subset_rfl f (mem_dadeDomain_of_mem_dadeZDomain hf)]
  exact mem_virtualChars_of_mem_span_Irr
    (hD.dadeMap_mem_span_Irr _ (virtualChars_le_span_Irr (mem_dadeZDomain.1 hf).1))

theorem indClassFun_mem_charSpanZero_Irr (hTI : IsTIWithNormalizer A L) {f : ↥L → ℂ}
    (hf : f ∈ dadeZDomain L A) : indClassFun L f ∈ charSpanZero (Irr G) :=
  mem_charSpanZero_Irr.2 ⟨hTI.indClassFun_mem_virtualChars hf,
    hTI.indClassFun_apply_one (mem_dadeZDomain.1 hf).2⟩

noncomputable def indZMap (hTI : IsTIWithNormalizer A L) :
    dadeZDomain L A →+ charSpanZero (Irr G) where
  toFun f := ⟨indClassFun L (f : ↥L → ℂ), hTI.indClassFun_mem_charSpanZero_Irr f.2⟩
  map_zero' := Subtype.ext (indClassFun_zero L)
  map_add' f g := Subtype.ext (indClassFun_add L (f : ↥L → ℂ) (g : ↥L → ℂ))

theorem coe_indZMap (hTI : IsTIWithNormalizer A L) (f : dadeZDomain L A) :
    ((hTI.indZMap f : charSpanZero (Irr G)) : G → ℂ) = indClassFun L (f : ↥L → ℂ) := (rfl)

theorem cfInner_indZMap [Fintype ↥L] (hTI : IsTIWithNormalizer A L) (f h : dadeZDomain L A) :
    cfInner ((hTI.indZMap f : charSpanZero (Irr G)) : G → ℂ)
        ((hTI.indZMap h : charSpanZero (Irr G)) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ) := by
  rw [coe_indZMap, coe_indZMap]
  exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain f.2)
    (mem_dadeDomain_of_mem_dadeZDomain h.2)

theorem indZMap_injective (hTI : IsTIWithNormalizer A L) :
    Function.Injective hTI.indZMap := fun f g hfg =>
  Subtype.ext (hTI.indClassFun_injOn (mem_dadeDomain_of_mem_dadeZDomain f.2)
    (mem_dadeDomain_of_mem_dadeZDomain g.2)
    (by rw [← coe_indZMap hTI f, ← coe_indZMap hTI g, hfg]))

end IsTIWithNormalizer

variable [Fintype G]

theorem cfInner_indClassFun_of_conj_image_eq_or_disjoint [Fintype ↥L] (hne : A.Nonempty)
    (h1 : (1 : G) ∉ A)
    (hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅)
    (hL : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    {f h : ↥L → ℂ} (hf : f ∈ dadeDomain L A) (hh : h ∈ dadeDomain L A) :
    cfInner (indClassFun L f) (indClassFun L h) = cfInner f h :=
  (isTIWithNormalizer_of_conj_image_eq_or_disjoint hne h1 hTI hL).cfInner_indClassFun hf hh

theorem indClassFun_mem_charSpanZero_Irr_of_conj_image_eq_or_disjoint (hne : A.Nonempty)
    (h1 : (1 : G) ∉ A)
    (hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅)
    (hL : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    {f : ↥L → ℂ} (hf : f ∈ dadeZDomain L A) : indClassFun L f ∈ charSpanZero (Irr G) :=
  (isTIWithNormalizer_of_conj_image_eq_or_disjoint hne h1 hTI hL).indClassFun_mem_charSpanZero_Irr
    hf

end CFSG.FeitThompson

end
