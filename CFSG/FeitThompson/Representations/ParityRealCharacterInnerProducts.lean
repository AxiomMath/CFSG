module

public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G]

omit [Group G] in
theorem conj_eq_self_iff_forall_im_eq_zero {f : G → ℂ} :
    (fun g => conj (f g)) = f ↔ ∀ g, (f g).im = 0 :=
  ⟨fun h g => Complex.conj_eq_iff_im.1 (congrFun h g),
    fun h => funext fun g => Complex.conj_eq_iff_im.2 (h g)⟩

omit [Group G] in
theorem cfInner_conj_right_of_im_eq_zero [Fintype G] {f : G → ℂ} (hf : ∀ g, (f g).im = 0)
    (ψ : G → ℂ) : cfInner f (fun g => conj (ψ g)) = conj (cfInner f ψ) := by
  calc cfInner f (fun g => conj (ψ g))
      = cfInner (fun g => conj (f g)) (fun g => conj (ψ g)) := by
        rw [conj_eq_self_iff_forall_im_eq_zero.2 hf]
    _ = conj (cfInner f ψ) := cfInner_conj_conj f ψ

theorem cfInner_conj_right_eq_self_of_mem_span_Irr [Fintype G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hfr : ∀ g, (f g).im = 0) {ψ : G → ℂ} (hψ : ψ ∈ Irr G) :
    cfInner f (fun g => conj (ψ g)) = cfInner f ψ := by
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hf (Submodule.subset_span hψ)
  rw [cfInner_conj_right_of_im_eq_zero hfr, hm]
  simp

theorem intCast_cfInner_modEq_mul_of_odd [Fintype G] (hodd : Odd (Nat.card G))
    {f h : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G)) (hh : h ∈ Submodule.span ℤ (Irr G))
    (hfr : ∀ g, (f g).im = 0) (hhr : ∀ g, (h g).im = 0)
    {m a b : ℤ} (hm : cfInner f h = (m : ℂ)) (ha : cfInner f (1 : G → ℂ) = (a : ℂ))
    (hb : cfInner h (1 : G → ℂ) = (b : ℂ)) : m ≡ a * b [ZMOD 2] := by
  classical
  have : Fintype (Irr G) := Fintype.ofFinite _
  obtain ⟨A, hfA⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hf
  obtain ⟨B, hhB⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hh
  set χ₁ : Irr G := ⟨1, one_mem_Irr⟩
  have hcoe₁ : (χ₁ : G → ℂ) = 1 := rfl
  set σ : Irr G → Irr G := fun χ => ⟨fun g => conj ((χ : G → ℂ) g), conj_mem_Irr χ.2⟩
  have hσcoe : ∀ χ : Irr G, ((σ χ : Irr G) : G → ℂ) = fun g => conj ((χ : G → ℂ) g) :=
    fun _ => rfl
  have hσσ : ∀ χ, σ (σ χ) = χ := by
    intro χ; apply Subtype.ext; rw [hσcoe, hσcoe]; funext g; simp
  have hσone : σ χ₁ = χ₁ := by
    apply Subtype.ext; rw [hσcoe, hcoe₁]; funext g; simp
  have hcoeff : ∀ (C : Irr G → ℤ) (k : G → ℂ), k = ∑ χ : Irr G, (C χ : ℂ) • (χ : G → ℂ) →
      k ∈ Submodule.span ℤ (Irr G) → (∀ g, (k g).im = 0) → ∀ χ, C (σ χ) = C χ := by
    intro C k hk hkmem hkr χ
    have h1 := cfInner_intCast_sum_Irr_coe C (σ χ)
    have h2 := cfInner_intCast_sum_Irr_coe C χ
    rw [hσcoe] at h1
    rw [← hk] at h1 h2
    have h3 := cfInner_conj_right_eq_self_of_mem_span_Irr hkmem hkr χ.2
    have : ((C (σ χ) : ℂ)) = ((C χ : ℂ)) := by rw [← h1, ← h2]; exact h3
    exact_mod_cast this
  have hAσ := hcoeff A f hfA hf hfr
  have hBσ := hcoeff B h hhB hh hhr
  have hma : m = ∑ χ : Irr G, A χ * B χ := by
    have hm' := hm
    rw [hfA, hhB, cfInner_intCast_sum_Irr_intCast_sum_Irr] at hm'
    exact_mod_cast hm'.symm
  have haA : a = A χ₁ := by
    have ha' := ha
    rw [hfA, ← hcoe₁, cfInner_intCast_sum_Irr_coe] at ha'
    exact_mod_cast ha'.symm
  have hbB : b = B χ₁ := by
    have hb' := hb
    rw [hhB, ← hcoe₁, cfInner_intCast_sum_Irr_coe] at hb'
    exact_mod_cast hb'.symm
  subst hma haA hbB
  refine (ZMod.intCast_eq_intCast_iff _ _ 2).1 ?_
  push_cast
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ χ₁), add_eq_right]
  refine Finset.sum_involution (fun χ _ => σ χ) (fun χ _ => ?_) (fun χ hχ _ => ?_)
    (fun χ hχ => ?_) (fun χ _ => hσσ χ)
  · rw [hAσ, hBσ]
    exact CharTwo.add_self_eq_zero _
  · intro hcon
    refine ne_conj_of_mem_Irr_of_ne_one_of_odd hodd χ.2 ?_ ?_
    · intro h1
      exact absurd (Subtype.ext h1 : χ = χ₁) (Finset.mem_erase.1 hχ).1
    · rw [← hσcoe, hcon]
  · refine Finset.mem_erase.2 ⟨fun hcon => (Finset.mem_erase.1 hχ).1 ?_, Finset.mem_univ _⟩
    rw [← hσσ χ, hcon, hσone]

theorem exists_int_cfInner_sub_mul_cfInner_one_eq_two_mul_of_odd [Fintype G]
    (hodd : Odd (Nat.card G)) {f h : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    (hh : h ∈ Submodule.span ℤ (Irr G)) (hfr : ∀ g, (f g).im = 0) (hhr : ∀ g, (h g).im = 0) :
    ∃ k : ℤ, cfInner f h - cfInner f (1 : G → ℂ) * cfInner h (1 : G → ℂ) = 2 * (k : ℂ) := by
  have h1 : (1 : G → ℂ) ∈ Submodule.span ℤ (Irr G) := Submodule.subset_span one_mem_Irr
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hf hh
  obtain ⟨a, ha⟩ := exists_int_cfInner_of_mem_span_Irr hf h1
  obtain ⟨b, hb⟩ := exists_int_cfInner_of_mem_span_Irr hh h1
  obtain ⟨k, hk⟩ := (intCast_cfInner_modEq_mul_of_odd hodd hf hh hfr hhr hm ha hb).symm.dvd
  refine ⟨k, ?_⟩
  rw [hm, ha, hb, show (m : ℂ) - (a : ℂ) * (b : ℂ) = ((m - a * b : ℤ) : ℂ) by push_cast; ring, hk]
  push_cast
  ring

end CFSG.FeitThompson
