module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.ModelStar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondBasic
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.EvenSporadicStandard.Wong77.Module

@[expose] def FrameFact : Prop :=
  ∃ (φ : Multiplicative Word →* J) (T : Subgroup J),
    (∀ w : Word, φ (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode) ∧
    φ (eVec 0) = d ∧ (∀ i, φ (eVec i) ∈ D23) ∧
    T ≤ Subgroup.centralizer {d} ∧ Nat.card T = 2 ^ 18 ∧
    ∀ x ∈ D23, x ∈ T ↔ ∃ i, φ (eVec i) = x

theorem φ_mem_of_eVec {X : Type*} [Group X] (φ : Multiplicative Word →* X) {T : Subgroup X}
    (h : ∀ i, φ (eVec i) ∈ T) (w : Word) : φ (Multiplicative.ofAdd w) ∈ T := by
  have hP : ∀ a b : Word, φ (Multiplicative.ofAdd a) ∈ T → φ (Multiplicative.ofAdd b) ∈ T →
      φ (Multiplicative.ofAdd (a + b)) ∈ T := fun a b ha hb => by
    rw [ofAdd_add, map_mul]
    exact T.mul_mem ha hb
  rw [← Finset.univ_sum_single w]
  refine Finset.sum_induction _ (fun v => φ (Multiplicative.ofAdd v) ∈ T) hP
    (by rw [ofAdd_zero, map_one]; exact T.one_mem) ?_
  intro i _
  have hw : w i = 0 ∨ w i = 1 := by
    generalize w i = a
    revert a
    decide
  rcases hw with hw | hw
  · rw [hw, Pi.single_zero, ofAdd_zero, map_one]
    exact T.one_mem
  · rw [hw]
    exact h i

section Lift

variable {Λ X : Type*} [Group Λ] [Group X] (ψ : Λ →* X) (hψ : Function.Injective ψ)
  (φ : Multiplicative Word →* X) (hrange : ∀ w : Word, ∃ x, ψ x = φ (Multiplicative.ofAdd w))

@[expose] noncomputable def liftHom : Multiplicative Word →* Λ :=
  (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp
    (φ.codRestrict ψ.range fun w => MonoidHom.mem_range.2 (hrange w))

include hrange in
theorem psi_liftHom (w : Word) :
    ψ (liftHom ψ hψ φ hrange (Multiplicative.ofAdd w)) = φ (Multiplicative.ofAdd w) := by
  have h := (MonoidHom.ofInjective hψ).apply_symm_apply
    (φ.codRestrict ψ.range (fun w => MonoidHom.mem_range.2 (hrange w)) (Multiplicative.ofAdd w))
  exact congrArg Subtype.val h

include hrange in
theorem liftHom_eq_one_iff (w : Word) :
    liftHom ψ hψ φ hrange (Multiplicative.ofAdd w) = 1 ↔ φ (Multiplicative.ofAdd w) = 1 := by
  constructor
  · intro h
    rw [← psi_liftHom ψ hψ φ hrange w, h, map_one]
  · intro h
    apply hψ
    rw [psi_liftHom ψ hψ φ hrange w, h, map_one]

end Lift

section FrameJ

variable {φ : Multiplicative Word →* J} {T₀ : Subgroup J}

theorem frame_star_iff (hker : ∀ w : Word, φ (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode)
    (h0 : φ (eVec 0) = d) (hD : ∀ i, φ (eVec i) ∈ D23) (hle : T₀ ≤ Subgroup.centralizer {d})
    (hT : ∀ x ∈ D23, x ∈ T₀ ↔ ∃ i, φ (eVec i) = x) (y : J) :
    (y ∈ T₀ ∧ y ∈ LocalClass D23 d) ↔ ∃ i, i ≠ 0 ∧ φ (eVec i) = y := by
  constructor
  · rintro ⟨hy, hyD, hyd, -⟩
    obtain ⟨i, hi⟩ := (hT y hyD).1 hy
    refine ⟨i, fun h => hyd ?_, hi⟩
    rw [← hi, h, h0]
  · rintro ⟨i, hi, rfl⟩
    have hmem : φ (eVec i) ∈ T₀ := (hT _ (hD i)).2 ⟨i, rfl⟩
    refine ⟨hmem, hD i, fun h => hi ?_, mem_centralizer_singleton_iff.1 (hle hmem)⟩
    have hinj := (goodFrame_of_ker_eq φ hker).pt_injective
    apply hinj
    show φ (eVec i) = φ (eVec 0)
    rw [h, h0]

theorem frame_star2_iff (hker : ∀ w : Word, φ (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode)
    (h0 : φ (eVec 0) = d) (hD : ∀ i, φ (eVec i) ∈ D23) (hle : T₀ ≤ Subgroup.centralizer {d})
    (hT : ∀ x ∈ D23, x ∈ T₀ ↔ ∃ i, φ (eVec i) = x) (y : J) :
    (y ∈ T₀ ∧ y ∈ starSet true) ↔ ∃ i, i ≠ 0 ∧ d * φ (eVec i) = y := by
  have hd : d ∈ T₀ := h0 ▸ (hT _ (hD 0)).2 ⟨0, rfl⟩
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    have hz' : z ∈ T₀ := by
      have : d * (d * z) ∈ T₀ := T₀.mul_mem hd hy
      rwa [← mul_assoc, d_sq, one_mul] at this
    obtain ⟨i, hi, hiz⟩ := (frame_star_iff hker h0 hD hle hT z).1 ⟨hz', hz⟩
    exact ⟨i, hi, by rw [hiz]; rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have h1 := (frame_star_iff hker h0 hD hle hT (φ (eVec i))).2 ⟨i, hi, rfl⟩
    exact ⟨T₀.mul_mem hd h1.1, φ (eVec i), h1.2, rfl⟩

end FrameJ

end CFSG.EvenSporadicStandard.TwoFi22
