module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.ComponentClassification

namespace AutQuot

variable {Λ Q : Type*} [Group Λ] [Group Q] (π : Λ →* Q) (hπ : Function.Surjective π)
  (hker : π.ker = center Λ)

theorem apply_mem_center (σ : MulAut Λ) {x : Λ} (hx : x ∈ center Λ) : σ x ∈ center Λ := by
  rw [mem_center_iff] at hx ⊢
  intro g
  obtain ⟨h, rfl⟩ := σ.surjective g
  rw [← map_mul, ← map_mul, hx h]

include hker in
theorem ker_le_ker_comp (σ : MulAut Λ) : π.ker ≤ (π.comp σ.toMonoidHom).ker := by
  intro x hx
  rw [hker] at hx
  have h := apply_mem_center σ hx
  rw [← hker] at h
  exact h

@[expose] noncomputable def inducedHom (σ : MulAut Λ) : Q →* Q :=
  (π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ))
    ⟨π.comp σ.toMonoidHom, ker_le_ker_comp π hker σ⟩

theorem inducedHom_apply (σ : MulAut Λ) (x : Λ) :
    inducedHom π hπ hker σ (π x) = π (σ x) :=
  MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
    (Function.rightInverse_surjInv hπ) ⟨π.comp σ.toMonoidHom, ker_le_ker_comp π hker σ⟩ x

@[expose] noncomputable def inducedAut : MulAut Λ →* MulAut Q where
  toFun σ := MonoidHom.toMulEquiv (inducedHom π hπ hker σ) (inducedHom π hπ hker σ⁻¹)
    (by
      ext q
      obtain ⟨x, rfl⟩ := hπ q
      simp [inducedHom_apply])
    (by
      ext q
      obtain ⟨x, rfl⟩ := hπ q
      simp [inducedHom_apply])
  map_one' := by
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    simp [inducedHom_apply]
  map_mul' σ τ := by
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    simp [inducedHom_apply]

theorem inducedAut_apply (σ : MulAut Λ) (x : Λ) : inducedAut π hπ hker σ (π x) = π (σ x) :=
  inducedHom_apply π hπ hker σ x

theorem inducedAut_injective [Group.IsPerfect Λ] : Function.Injective (inducedAut π hπ hker) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hcentral : ∀ x : Λ, x⁻¹ * σ.toMonoidHom x ∈ center Λ := by
    intro x
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    have h1 : π (σ x) = π x := by
      have := congrArg (fun α : MulAut Q => α (π x)) hσ
      simpa [inducedAut_apply] using this
    have h2 : π (σ.toMonoidHom x) = π x := h1
    rw [h2, inv_mul_cancel]
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement σ.toMonoidHom hcentral
  ext x
  have := DFunLike.congr_fun hid x
  simpa using this

theorem inducedAut_conj (x : Λ) :
    inducedAut π hπ hker (MulAut.conj x) = MulAut.conj (π x) := by
  ext q
  obtain ⟨y, rfl⟩ := hπ q
  simp [inducedAut_apply, MulAut.conj_apply]

theorem eq_conj_of_inducedAut_eq [Group.IsPerfect Λ] {σ : MulAut Λ} {x : Λ}
    (h : inducedAut π hπ hker σ = MulAut.conj (π x)) : σ = MulAut.conj x :=
  inducedAut_injective π hπ hker (h.trans (inducedAut_conj π hπ hker x).symm)

include hπ hker in
theorem aut_cent_of_quotient [Group.IsPerfect Λ] (E : Subgroup Λ)
    (h : ∀ α : MulAut Q, (∀ e ∈ E.map π, α e = e) → ∃ x ∈ E.map π, α = MulAut.conj x) :
    ∀ σ : MulAut Λ, (∀ e ∈ E, σ e = e) → ∃ x ∈ E, σ = MulAut.conj x := by
  intro σ hσ
  have hfix : ∀ e' ∈ E.map π, inducedAut π hπ hker σ e' = e' := by
    rintro _ ⟨e, he, rfl⟩
    rw [inducedAut_apply, hσ e he]
  obtain ⟨_, ⟨x, hx, rfl⟩, hα⟩ := h _ hfix
  exact ⟨x, hx, eq_conj_of_inducedAut_eq π hπ hker hα⟩

include hπ hker in
theorem rank_of_quotient [Group.IsPerfect Λ] (hcard : Nat.card π.ker = 2) {n : ℕ}
    (h : ∀ α : MulAut Q, α * α = 1 → (∀ q : Q, α ≠ MulAut.conj q) →
      ∀ A : Subgroup Q, (∀ a ∈ A, a ^ 2 = 1) → (∀ a ∈ A, α a = a) → Nat.card A ≤ 2 ^ n) :
    ∀ σ : MulAut Λ, σ * σ = 1 → (∀ l : Λ, σ ≠ MulAut.conj l) →
      ∀ B : Subgroup Λ, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) →
        Nat.card B ≤ 2 ^ (n + 1) := by
  intro σ hσ2 hσout B hB2 hBfix
  have hα2 : inducedAut π hπ hker σ * inducedAut π hπ hker σ = 1 := by
    rw [← map_mul, hσ2, map_one]
  have hαout : ∀ q : Q, inducedAut π hπ hker σ ≠ MulAut.conj q := by
    intro q hq
    obtain ⟨x, rfl⟩ := hπ q
    exact hσout x (eq_conj_of_inducedAut_eq π hπ hker hq)
  have hA2 : ∀ a ∈ B.map π, a ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hAfix : ∀ a ∈ B.map π, inducedAut π hπ hker σ a = a := by
    rintro _ ⟨b, hb, rfl⟩
    rw [inducedAut_apply, hBfix b hb]
  have hle := h _ hα2 hαout (B.map π) hA2 hAfix
  have : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hker_le : Nat.card (π.comp B.subtype).ker ≤ Nat.card π.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x.1 : B) : Λ), x.2⟩) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hrange : (π.comp B.subtype).range = B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hmul := Subgroup.card_ker_mul_card_range (π.comp B.subtype)
  rw [hrange] at hmul
  calc Nat.card B = Nat.card (π.comp B.subtype).ker * Nat.card (B.map π) := hmul.symm
    _ ≤ 2 * 2 ^ n := Nat.mul_le_mul (hker_le.trans hcard.le) hle
    _ = 2 ^ (n + 1) := by ring

end AutQuot

end CFSG.EvenSporadicStandard.TwoFi22.DS81
