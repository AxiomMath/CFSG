module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open CategoryTheory
open scoped ComplexConjugate

noncomputable def charInner {X : Type*} [Fintype X] (f h : X → ℂ) : ℂ :=
  (Fintype.card X : ℂ)⁻¹ * ∑ x : X, f x * conj (h x)

section CharInner

variable {X : Type*} [Fintype X] (f g h : X → ℂ)

theorem charInner_def :
    charInner f h = (Fintype.card X : ℂ)⁻¹ * ∑ x : X, f x * conj (h x) := (rfl)

theorem charInner_add_left : charInner (f + g) h = charInner f h + charInner g h := by
  simp only [charInner_def, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem charInner_add_right : charInner f (g + h) = charInner f g + charInner f h := by
  simp only [charInner_def, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, mul_add]

theorem charInner_sub_left : charInner (f - g) h = charInner f h - charInner g h := by
  simp only [charInner_def, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem charInner_sub_right : charInner f (g - h) = charInner f g - charInner f h := by
  simp only [charInner_def, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, mul_sub]

@[simp] theorem charInner_zero_left : charInner (0 : X → ℂ) h = 0 := by simp [charInner_def]

@[simp] theorem charInner_zero_right : charInner f (0 : X → ℂ) = 0 := by simp [charInner_def]

theorem conj_charInner : conj (charInner f h) = charInner h f := by
  simp only [charInner_def, map_mul, map_sum, map_inv₀, Complex.conj_natCast, Complex.conj_conj]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => mul_comm _ _)

theorem charInner_star_star : charInner (star f) (star h) = charInner h f := by
  rw [← conj_charInner]
  simp [charInner_def, Pi.star_apply]

theorem charInner_sum_left {ι : Type*} (s : Finset ι) (F : ι → X → ℂ) (h : X → ℂ) :
    charInner (∑ i ∈ s, F i) h = ∑ i ∈ s, charInner (F i) h := by
  simp only [charInner_def, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem charInner_sum_right {ι : Type*} (s : Finset ι) (f : X → ℂ) (F : ι → X → ℂ) :
    charInner f (∑ i ∈ s, F i) = ∑ i ∈ s, charInner f (F i) := by
  simp only [charInner_def, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem charInner_sum_self_of_orthonormal (T : Finset (X → ℂ))
    (h₁ : ∀ r ∈ T, charInner r r = 1)
    (h₂ : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → charInner r s = 0) :
    charInner (∑ r ∈ T, r) (∑ r ∈ T, r) = (T.card : ℂ) := by
  rw [charInner_sum_left]
  have key : ∀ r ∈ T, charInner r (∑ s ∈ T, s) = 1 := fun r hr => by
    rw [charInner_sum_right, Finset.sum_eq_single_of_mem r hr
      fun s hs hsr => h₂ r hr s hs (Ne.symm hsr)]
    exact h₁ r hr
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul, mul_one]

end CharInner

def IsCharacter (X : Type*) [Monoid X] (f : X → ℂ) : Prop :=
  ∃ V : FDRep ℂ X, V.character = f

theorem isCharacter_iff {X : Type*} [Monoid X] {f : X → ℂ} :
    IsCharacter X f ↔ ∃ V : FDRep ℂ X, V.character = f := Iff.rfl

theorem IsCharacter.exists_fdRep {X : Type*} [Monoid X] {f : X → ℂ} (hf : IsCharacter X f) :
    ∃ V : FDRep ℂ X, V.character = f := hf

theorem IsCharacter.of_fdRep {X : Type*} [Monoid X] (V : FDRep ℂ X) :
    IsCharacter X V.character := ⟨V, rfl⟩

theorem IsCharacter.exists_nat_apply_one {X : Type*} [Monoid X] {f : X → ℂ}
    (hf : IsCharacter X f) : ∃ d : ℕ, f 1 = (d : ℂ) := by
  obtain ⟨V, rfl⟩ := hf.exists_fdRep
  exact ⟨Module.finrank ℂ V, FDRep.char_one V⟩

theorem IsCharacter.exists_pos_nat_apply_one {X : Type*} [Monoid X] {f : X → ℂ}
    (hf : IsCharacter X f) (hf0 : f ≠ 0) : ∃ d : ℕ, 0 < d ∧ f 1 = (d : ℂ) := by
  obtain ⟨V, rfl⟩ := hf.exists_fdRep
  refine ⟨Module.finrank ℂ V, ?_, FDRep.char_one V⟩
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with hz | hp
  · refine absurd (funext fun g => ?_) hf0
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp hz
    change LinearMap.trace ℂ V (V.ρ g) = 0
    rw [Subsingleton.elim (V.ρ g) 0, map_zero]
  · exact hp

theorem IsCharacter.apply_one_ne_zero {X : Type*} [Monoid X] {f : X → ℂ} (hf : IsCharacter X f)
    (hf0 : f ≠ 0) : f 1 ≠ 0 := by
  obtain ⟨d, hd, hfd⟩ := hf.exists_pos_nat_apply_one hf0
  rw [hfd]
  exact Nat.cast_ne_zero.2 hd.ne'

theorem IsCharacter.conj_apply_one {X : Type*} [Monoid X] {f : X → ℂ} (hf : IsCharacter X f) :
    conj (f 1) = f 1 := by
  obtain ⟨V, rfl⟩ := hf
  rw [FDRep.char_one]
  simp

theorem IsCharacter.star_apply_one {X : Type*} [Monoid X] {f : X → ℂ} (hf : IsCharacter X f) :
    (star f) 1 = f 1 := hf.conj_apply_one

noncomputable def virtualCharSpan (X : Type*) [Monoid X] : Submodule ℤ (X → ℂ) :=
  Submodule.span ℤ {χ | ∃ V : FDRep ℂ X, Simple V ∧ V.character = χ}

theorem virtualCharSpan_eq_span (X : Type*) [Monoid X] :
    virtualCharSpan X
      = Submodule.span ℤ {χ | ∃ V : FDRep ℂ X, Simple V ∧ V.character = χ} := (rfl)

theorem mem_virtualCharSpan_iff {X : Type*} [Monoid X] {f : X → ℂ} :
    f ∈ virtualCharSpan X
      ↔ f ∈ Submodule.span ℤ {χ | ∃ V : FDRep ℂ X, Simple V ∧ V.character = χ} := Iff.rfl

theorem virtualCharSpan_le_span (X : Type*) [Monoid X] :
    virtualCharSpan X ≤ Submodule.span ℤ {χ | ∃ V : FDRep ℂ X, Simple V ∧ V.character = χ} :=
  (virtualCharSpan_eq_span X).le

theorem virtualCharSpan_le {X : Type*} [Monoid X] {p : Submodule ℤ (X → ℂ)}
    (h : ∀ V : FDRep ℂ X, Simple V → V.character ∈ p) : virtualCharSpan X ≤ p :=
  (virtualCharSpan_eq_span X).trans_le
    (Submodule.span_le.2 fun _ ⟨V, hV, hχ⟩ => hχ ▸ h V hV)

theorem character_mem_virtualCharSpan {X : Type*} [Monoid X] (V : FDRep ℂ X) [Simple V] :
    V.character ∈ virtualCharSpan X :=
  Submodule.subset_span ⟨V, ‹_›, rfl⟩

noncomputable def intSpanZeroAtOne {X : Type*} [One X] (S : Set (X → ℂ)) : Submodule ℤ (X → ℂ) :=
  Submodule.span ℤ S ⊓ LinearMap.ker (LinearMap.proj (1 : X) : (X → ℂ) →ₗ[ℤ] ℂ)

theorem mem_intSpanZeroAtOne {X : Type*} [One X] {S : Set (X → ℂ)} {f : X → ℂ} :
    f ∈ intSpanZeroAtOne S ↔ f ∈ Submodule.span ℤ S ∧ f 1 = 0 := by
  simp [intSpanZeroAtOne, LinearMap.mem_ker]

theorem intSpanZeroAtOne_le_span {X : Type*} [One X] (S : Set (X → ℂ)) :
    intSpanZeroAtOne S ≤ Submodule.span ℤ S := fun _ hf => (mem_intSpanZeroAtOne.1 hf).1

theorem apply_one_eq_zero_of_mem_intSpanZeroAtOne {X : Type*} [One X] {S : Set (X → ℂ)}
    {f : X → ℂ} (hf : f ∈ intSpanZeroAtOne S) : f 1 = 0 :=
  (mem_intSpanZeroAtOne.1 hf).2

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

structure IsSubcoherent (S : Finset (L → ℂ)) (tau : (L → ℂ) → (G → ℂ))
    (R : (L → ℂ) → Finset (G → ℂ)) : Prop where
  isCharacter : ∀ χ ∈ S, IsCharacter L χ
  ne_zero : ∀ χ ∈ S, χ ≠ 0
  star_mem : ∀ χ ∈ S, star χ ∈ S
  star_ne : ∀ χ ∈ S, star χ ≠ χ
  charInner_eq_zero : ∀ χ ∈ S, ∀ ψ ∈ S, χ ≠ ψ → charInner χ ψ = 0
  map_add : ∀ f ∈ intSpanZeroAtOne (S : Set (L → ℂ)),
    ∀ h ∈ intSpanZeroAtOne (S : Set (L → ℂ)), tau (f + h) = tau f + tau h
  tau_mem : ∀ f ∈ intSpanZeroAtOne (S : Set (L → ℂ)), tau f ∈ virtualCharSpan G
  charInner_tau_tau : ∀ f ∈ intSpanZeroAtOne (S : Set (L → ℂ)),
    ∀ h ∈ intSpanZeroAtOne (S : Set (L → ℂ)), charInner (tau f) (tau h) = charInner f h
  tau_apply_one : ∀ f ∈ intSpanZeroAtOne (S : Set (L → ℂ)), tau f 1 = 0
  R_subset : ∀ χ ∈ S, ∀ r ∈ R χ, r ∈ virtualCharSpan G
  charInner_R_self : ∀ χ ∈ S, ∀ r ∈ R χ, charInner r r = 1
  charInner_R_of_ne : ∀ χ ∈ S, ∀ r ∈ R χ, ∀ s ∈ R χ, r ≠ s → charInner r s = 0
  tau_sub_star : ∀ χ ∈ S, tau (χ - star χ) = ∑ r ∈ R χ, r
  charInner_R_R : ∀ χ ∈ S, ∀ ψ ∈ S, ψ ≠ χ → ψ ≠ star χ →
    ∀ r ∈ R χ, ∀ s ∈ R ψ, charInner r s = 0

namespace IsSubcoherent

variable {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem tau_zero (hc : IsSubcoherent S tau R) : tau 0 = 0 := by
  have h0 : (0 : L → ℂ) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := Submodule.zero_mem _
  simpa using (hc.map_add 0 h0 0 h0).symm

noncomputable def tauHom (hc : IsSubcoherent S tau R) :
    intSpanZeroAtOne (S : Set (L → ℂ)) →+ (G → ℂ) where
  toFun f := tau (f : L → ℂ)
  map_zero' := hc.tau_zero
  map_add' f h := hc.map_add _ f.2 _ h.2

@[simp] theorem tauHom_apply (hc : IsSubcoherent S tau R)
    (f : intSpanZeroAtOne (S : Set (L → ℂ))) : hc.tauHom f = tau (f : L → ℂ) := (rfl)

theorem map_sub (hc : IsSubcoherent S tau R) {f h : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hh : h ∈ intSpanZeroAtOne (S : Set (L → ℂ))) : tau (f - h) = tau f - tau h :=
  hc.tauHom.map_sub ⟨f, hf⟩ ⟨h, hh⟩

theorem map_neg (hc : IsSubcoherent S tau R) {f : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ))) : tau (-f) = -tau f :=
  hc.tauHom.map_neg ⟨f, hf⟩

theorem map_zsmul (hc : IsSubcoherent S tau R) (n : ℤ) {f : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ))) : tau (n • f) = n • tau f :=
  hc.tauHom.map_zsmul n ⟨f, hf⟩

theorem sub_star_mem (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    χ - star χ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := by
  refine mem_intSpanZeroAtOne.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
    (Submodule.subset_span (hc.star_mem χ hχ)), ?_⟩
  simp [Pi.star_apply, (hc.isCharacter χ hχ).conj_apply_one]

theorem sum_R_apply_one (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    (∑ r ∈ R χ, r) (1 : G) = 0 := by
  rw [← hc.tau_sub_star χ hχ]
  exact hc.tau_apply_one _ (hc.sub_star_mem hχ)

theorem sum_R_mem (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    (∑ r ∈ R χ, r) ∈ virtualCharSpan G := by
  rw [← hc.tau_sub_star χ hχ]
  exact hc.tau_mem _ (hc.sub_star_mem hχ)

theorem card_R (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ((R χ).card : ℂ) = 2 * charInner χ χ := by
  have hmem := hc.sub_star_mem hχ
  have h := hc.charInner_tau_tau _ hmem _ hmem
  rw [hc.tau_sub_star χ hχ, charInner_sum_self_of_orthonormal _
    (hc.charInner_R_self χ hχ) (hc.charInner_R_of_ne χ hχ)] at h
  have hs : star χ ∈ S := hc.star_mem χ hχ
  have e₁ : charInner χ (star χ) = 0 :=
    hc.charInner_eq_zero χ hχ _ hs (Ne.symm (hc.star_ne χ hχ))
  have e₂ : charInner (star χ) χ = 0 := hc.charInner_eq_zero _ hs χ hχ (hc.star_ne χ hχ)
  rw [h, charInner_sub_left, charInner_sub_right, charInner_sub_right,
    charInner_star_star χ χ, e₁, e₂]
  ring

theorem disjoint_R (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ} (hχ : χ ∈ S) (hψ : ψ ∈ S)
    (h₁ : ψ ≠ χ) (h₂ : ψ ≠ star χ) : Disjoint (R χ) (R ψ) := by
  refine Finset.disjoint_left.2 fun r hr hr' => ?_
  have h := hc.charInner_R_R χ hχ ψ hψ h₁ h₂ r hr r hr'
  rw [hc.charInner_R_self χ hχ r hr] at h
  exact one_ne_zero h

end IsSubcoherent

end CFSG.FeitThompson
