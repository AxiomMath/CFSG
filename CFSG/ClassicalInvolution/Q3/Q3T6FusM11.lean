module

public import CFSG.ClassicalInvolution.AschTight.S19MLift
public import CFSG.ClassicalInvolution.Asc77.AscIHHelp
public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.Uniform.UFacade

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section M11

open CFSG.Blueprint

variable {E : Type} [Group E] {Φ : Set (Subgroup E)}

theorem m11_injective (hM : Q3.M11Facts) (ψ : ↥NativeSporadic.M11 →* E)
    (hψ1 : ∃ x, ψ x ≠ 1) : Function.Injective ψ := by
  have := hM.1
  refine (MonoidHom.ker_eq_bot_iff ψ).mp ?_
  rcases (MonoidHom.normal_ker ψ).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := hψ1
    exact hx (by
      have : x ∈ ψ.ker := by rw [h]; trivial
      exact this)

noncomputable def m11Equiv (hM : Q3.M11Facts) (ψ : ↥NativeSporadic.M11 →* E)
    (hsurj : Function.Surjective ψ) (hψ1 : ∃ x, ψ x ≠ 1) : ↥NativeSporadic.M11 ≃* E :=
  MulEquiv.ofBijective ψ ⟨m11_injective hM ψ hψ1, hsurj⟩

theorem m11_facts (hM : Q3.M11Facts)
    (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g)
    (ψ : ↥NativeSporadic.M11 →* E) (hsurj : Function.Surjective ψ) (hψ1 : ∃ x, ψ x ≠ 1)
    (hconj : ConjInvariant Φ) (hne : ∃ R ∈ Q3.M11ClassicalClass, R.map ψ ∈ Φ) :
    IsSimpleGroup E ∧ (∀ φ : MulAut E, ∃ e, φ = MulAut.conj e) ∧
      ∀ x : E, x * x = 1 → x ≠ 1 → ∃ X ∈ Φ, IsUniqueInvolution X x := by
  have hinj := m11_injective hM ψ hψ1
  set e : ↥NativeSporadic.M11 ≃* E := m11Equiv hM ψ hsurj hψ1 with he
  have hev : ∀ y, e y = ψ y := fun y => rfl
  have := hM.1
  refine ⟨MulEquiv.isSimpleGroup e.symm, ?_, ?_⟩
  · intro φ
    obtain ⟨g, hg⟩ := hOut (e.trans (φ.trans e.symm))
    refine ⟨e g, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun α : MulAut ↥NativeSporadic.M11 => e (α (e.symm x))) hg
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply, map_mul,
      map_inv] at h1 ⊢
    exact h1
  · intro x hx hx1
    obtain ⟨R₀, hR₀, hR₀Φ⟩ := hne
    obtain ⟨z₀, hz₀⟩ := hR₀
    set y := e.symm x with hy
    have hy2 : y * y = 1 := by
      apply e.injective
      rw [map_mul, hy, MulEquiv.apply_symm_apply, hx, map_one]
    have hy1 : y ≠ 1 := fun h => hx1 (by
      have := congrArg e h
      rwa [hy, MulEquiv.apply_symm_apply, map_one] at this)
    have hyord : orderOf y = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hy2) hy1
    have hc := (Q3.isConj_m11SdZ_of_orderOf_eq_two hz₀.orderOf_eq_two).symm.trans
      (Q3.isConj_m11SdZ_of_orderOf_eq_two hyord)
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    have hRy : Q3.IsClassicalMember3 (R₀.map (MulAut.conj g).toMonoidHom) y := by
      have := hz₀.map_mulEquiv (MulAut.conj g)
      rwa [MulAut.conj_apply, hg] at this
    have hI : IsUniqueInvolution (R₀.map (MulAut.conj g).toMonoidHom) y :=
      (isClassicalMember3_iff_U.mp hRy).isUniqueInvolution (MemberType.cert_sl2 3 1)
    have hker : Odd (Nat.card ψ.ker) := by
      have : ψ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ψ).mpr hinj
      rw [this, Subgroup.card_bot]
      exact odd_one
    refine ⟨(R₀.map (MulAut.conj g).toMonoidHom).map ψ, ?_, ?_⟩
    · rw [map_conj_eq_conjSub_map]
      exact hconj _ _ hR₀Φ
    · have := S19M.isUniqueInvolution_map hker hI
      rwa [show ψ y = x from by rw [← hev, hy, MulEquiv.apply_symm_apply]] at this

end M11

end CFSG.ClassicalInvolution.Q3.Q3T6
