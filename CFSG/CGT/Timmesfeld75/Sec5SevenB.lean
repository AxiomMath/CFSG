module

public import CFSG.CGT.Timmesfeld75.Sec5SevenA
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.CGT.Timmesfeld75.Sec5SixB

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

@[expose] def Sec57Shult : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    (∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) →
    (∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → conjSubgroup g (secA T T₁) ≤ secR₁ T T₁) →
    secA T T₁ = ⊥

@[expose] def Sec57Y : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    secA T T₁ ≠ ⊥ → (∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) →
    ∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → ¬ conjSubgroup g (secA T T₁) ≤ secR₁ T T₁ →
      Nat.card T < Nat.card (secA T T₁) * Nat.card (normIn T T₁) →
      (∀ h : G, IsUIdx T T₁ h → ∀ a ∈ conjSubgroup h (secA T T₁),
        ∀ x ∈ conjSubgroup g (secA T T₁), a * x = x * a) → False

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem sec57 (hres : Sec56Residue) (hshult : Sec57Shult) (hY : Sec57Y) (h1 : Sec4NoA)
    (h3 : Sec4Nine) (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) :
    secA T T₁ = ⊥ := by
  have : Finite G := hy.finite
  have hab := sec56 hres h1 h3 hy hS hI hTO hBW
  by_cases hcase : ∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → conjSubgroup g (secA T T₁) ≤ secR₁ T T₁
  · exact hshult G T T₁ hy hS hI hab hcase
  · push Not at hcase
    obtain ⟨g, hg, hgT, hnR⟩ := hcase
    by_contra hA1
    have hnu : ¬ IsUIdx T T₁ g := fun hu => hnR (by
      unfold secR₁
      exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) g hu)
    have hcard := card_lt_of_not_isUIdx hy.pair hS hI hA1 hg hgT hnu
    exact hY G T T₁ hy hS hI hA1 hab g hg hgT hnR hcard fun h hh a ha x hx =>
      commute_conj_secA_conj_secA_of_card_lt_of_ne h1 h3 hy hS hI hTO hBW hcard hh hg hgT a ha x hx

theorem stepA1_of (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) (h1 : Sec4NoA) (h3 : Sec4Nine) (hs1 : Sec56StepOne)
    (hcorB : Sec56CorB) (hshult : Sec57Shult) (hY : Sec57Y) : StepA1 := by
  intro G _ T T₁ hyp
  have : Finite G := hyp.finite
  have : IsSimpleGroup G := hyp.simple
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hyp.pair.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hyp.nonab hS
  exact sec57 (sec56Residue_of hs1 hcorB) hshult hY h1 h3 hyp hS hI hTO hBW

end CFSG.CGT.Timmesfeld75
