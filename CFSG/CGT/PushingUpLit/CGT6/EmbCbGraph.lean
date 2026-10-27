module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv

private theorem cbo_exists_comm_involutions (m : ℕ) (hm : 6 ≤ m) :
    ∃ a₁ a₂ : alternatingGroup (Fin m), a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      a₁ ≠ a₂ ∧ a₁ * a₂ = a₂ * a₁ := by
  classical
  let f : Fin 6 ≃ Set.range (Fin.castLEEmb hm) :=
    Equiv.ofInjective (Fin.castLEEmb hm) (Fin.castLEEmb hm).injective
  let Φ : Perm (Fin 6) →* Perm (Fin m) := Equiv.Perm.extendDomainHom f
  have hΦ : Function.Injective Φ := Equiv.Perm.extendDomainHom_injective f
  have hsign : ∀ σ : Perm (Fin 6), Perm.sign (Φ σ) = Perm.sign σ := fun σ =>
    Equiv.Perm.sign_extendDomain σ f
  let σ₁ : Perm (Fin 6) := swap 0 1 * swap 2 3
  let σ₂ : Perm (Fin 6) := swap 0 1 * swap 4 5
  have hs₁ : Perm.sign σ₁ = 1 := by
    rw [map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]; decide
  have hs₂ : Perm.sign σ₂ = 1 := by
    rw [map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]; decide
  have m₁ : Φ σ₁ ∈ alternatingGroup (Fin m) := Perm.mem_alternatingGroup.2 ((hsign σ₁).trans hs₁)
  have m₂ : Φ σ₂ ∈ alternatingGroup (Fin m) := Perm.mem_alternatingGroup.2 ((hsign σ₂).trans hs₂)
  have c₁ : σ₁ ^ 2 = 1 := by decide
  have c₂ : σ₂ ^ 2 = 1 := by decide
  have c₃ : σ₁ ≠ 1 := by decide
  have c₄ : σ₂ ≠ 1 := by decide
  have c₅ : σ₁ ≠ σ₂ := by decide
  have c₆ : σ₁ * σ₂ = σ₂ * σ₁ := by decide
  refine ⟨⟨Φ σ₁, m₁⟩, ⟨Φ σ₂, m₂⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by show Φ σ₁ ^ 2 = 1; rw [← map_pow, c₁, map_one])
  · exact Subtype.ext (by show Φ σ₂ ^ 2 = 1; rw [← map_pow, c₂, map_one])
  · exact fun h => c₃ (hΦ ((congrArg Subtype.val h).trans (map_one Φ).symm))
  · exact fun h => c₄ (hΦ ((congrArg Subtype.val h).trans (map_one Φ).symm))
  · exact fun h => c₅ (hΦ (congrArg Subtype.val h))
  · exact Subtype.ext (by simp only [Subgroup.coe_mul]; rw [← map_mul, ← map_mul, c₆])

private theorem cbo_five_le_card {m : ℕ} (hm : 5 ≤ m) : 5 ≤ Nat.card (Fin m) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact hm

private theorem cbo_exists_inner {Γ : Type*} [Group Γ] {m : ℕ} (hm : 7 ≤ m)
    {Y₁ Y₂ : Subgroup Γ} (e₁ : ↥Y₁ ≃* alternatingGroup (Fin m))
    (e₂ : ↥Y₂ ≃* alternatingGroup (Fin m))
    (hN : ∀ y ∈ Y₂, ∀ z ∈ Y₁, y * z * y⁻¹ ∈ Y₁) :
    ∃ Z : ↥Y₂ →* ↥Y₁, ∀ (y : ↥Y₂) (x : ↥Y₁),
      (y : Γ) * x * (y : Γ)⁻¹ = (Z y : Γ) * x * (Z y : Γ)⁻¹ := by
  have hnorm : Y₂ ≤ Subgroup.normalizer (Y₁ : Set Γ) := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hN y hy z, fun hz => ?_⟩
    simpa [mul_assoc] using hN y⁻¹ (Y₂.inv_mem hy) _ hz
  let a : ↥Y₂ →* MulAut ↥Y₁ := Y₁.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have ha : ∀ (y : ↥Y₂) (x : ↥Y₁), ((a y x : ↥Y₁) : Γ) = y * x * y⁻¹ := fun y x => rfl
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m
    (by omega) (by omega)
  let Θ : Perm (Fin m) ≃* MulAut ↥Y₁ :=
    (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin m))) hbij).trans
      (MulAut.congr e₁.symm)
  let P : ↥Y₂ →* Perm (Fin m) := Θ.symm.toMonoidHom.comp a
  have hPa : ∀ y, Θ (P y) = a y := fun y => Θ.apply_symm_apply _
  have hperf : Group.IsPerfect ↥Y₂ := by
    have : Group.IsPerfect (alternatingGroup (Fin m)) :=
      ⟨commutator_alternatingGroup_eq_top (cbo_five_le_card (by omega))⟩
    exact Group.IsPerfect.ofSurjective (f := e₂.symm.toMonoidHom) e₂.symm.surjective
  have hsign : ∀ y, Perm.sign (P y) = 1 := fun y => by
    have h1 := Abelianization.commutator_subset_ker (Perm.sign.comp P)
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (Subgroup.mem_top y)
  let Z' : ↥Y₂ →* alternatingGroup (Fin m) :=
    P.codRestrict _ (fun y => Perm.mem_alternatingGroup.2 (hsign y))
  have key : ∀ (y : ↥Y₂) (x : ↥Y₁), a y x = e₁.symm (Z' y * e₁ x * (Z' y)⁻¹) := by
    intro y x
    rw [← hPa y]
    show e₁.symm (MulAut.conjNormal (P y) (e₁ x)) = _
    congr 1
  refine ⟨e₁.symm.toMonoidHom.comp Z', fun y x => ?_⟩
  have h1 := congrArg Subtype.val (key y x)
  rw [ha, Subgroup.coe_inv] at h1
  rw [h1]
  simp

theorem cbo_eq_of_normalizes {Γ : Type*} [Group Γ] {m : ℕ} (hm : 7 ≤ m)
    {Gr Y₁ Y₂ : Subgroup Γ} (hY₁ : Y₁ ≤ Gr) (hY₂ : Y₂ ≤ Gr)
    (e₁ : ↥Y₁ ≃* alternatingGroup (Fin m)) (e₂ : ↥Y₂ ≃* alternatingGroup (Fin m))
    (hN : ∀ y ∈ Y₂, ∀ z ∈ Y₁, y * z * y⁻¹ ∈ Y₁)
    (hK : ∀ a b : Γ, a ∈ Gr → b ∈ Gr → (∀ z ∈ Y₁, a * z = z * a) → (∀ z ∈ Y₁, b * z = z * b) →
      a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a → False) :
    Y₂ = Y₁ := by
  obtain ⟨Z, hZ⟩ := cbo_exists_inner hm e₁ e₂ hN
  have hc : ∀ (y : ↥Y₂) (x : ↥Y₁), ((Z y : Γ)⁻¹ * y) * x = x * ((Z y : Γ)⁻¹ * y) := by
    intro y x
    calc (Z y : Γ)⁻¹ * y * x = (Z y : Γ)⁻¹ * (y * x * (y : Γ)⁻¹) * y := by group
      _ = (Z y : Γ)⁻¹ * ((Z y : Γ) * x * (Z y : Γ)⁻¹) * y := by rw [hZ y x]
      _ = x * ((Z y : Γ)⁻¹ * y) := by group
  let φ : ↥Y₂ →* Γ := MonoidHom.mk' (fun y => (Z y : Γ)⁻¹ * y) (fun y y' => by
    have h1 : ((Z y : Γ)⁻¹ * y) * (Z y' : Γ)⁻¹ = (Z y' : Γ)⁻¹ * ((Z y : Γ)⁻¹ * y) :=
      (Commute.inv_right (hc y (Z y'))).eq
    simp only [map_mul, Subgroup.coe_mul]
    calc ((Z y : Γ) * (Z y' : Γ))⁻¹ * ((y : Γ) * y')
        = (Z y' : Γ)⁻¹ * ((Z y : Γ)⁻¹ * y) * y' := by group
      _ = ((Z y : Γ)⁻¹ * y) * (Z y' : Γ)⁻¹ * y' := by rw [h1]
      _ = ((Z y : Γ)⁻¹ * y) * ((Z y' : Γ)⁻¹ * y') := by group)
  let ψ : alternatingGroup (Fin m) →* Γ := φ.comp e₂.symm.toMonoidHom
  have hψ : ∀ s, ψ s = (Z (e₂.symm s) : Γ)⁻¹ * (e₂.symm s : Γ) := fun s => rfl
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (cbo_five_le_card (by omega))
    (N := ψ.ker) with hker | hker
  ·
    exfalso
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
    obtain ⟨a₁, a₂, ha1, ha2, ha1n, ha2n, ha12, hac⟩ := cbo_exists_comm_involutions m (by omega)
    have hmem : ∀ s, ψ s ∈ Gr := fun s => by
      rw [hψ]
      exact Gr.mul_mem (Gr.inv_mem (hY₁ (Z (e₂.symm s)).2)) (hY₂ (e₂.symm s).2)
    refine hK (ψ a₁) (ψ a₂) (hmem a₁) (hmem a₂) (fun z hz => ?_) (fun z hz => ?_) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hψ]; exact hc (e₂.symm a₁) ⟨z, hz⟩
    · rw [hψ]; exact hc (e₂.symm a₂) ⟨z, hz⟩
    · rw [← map_pow, ha1, map_one]
    · rw [← map_pow, ha2, map_one]
    · exact fun h => ha1n (hinj (h.trans (map_one ψ).symm))
    · exact fun h => ha2n (hinj (h.trans (map_one ψ).symm))
    · exact fun h => ha12 (hinj h)
    · rw [← map_mul, ← map_mul, hac]
  ·
    have hle : Y₂ ≤ Y₁ := fun y hy => by
      have h1 : ψ (e₂ ⟨y, hy⟩) = 1 := by
        have : e₂ ⟨y, hy⟩ ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_top _
        exact this
      rw [hψ, e₂.symm_apply_apply] at h1
      have h2 : (y : Γ) = (Z ⟨y, hy⟩ : Γ) := by
        have := congrArg (fun g : Γ => (Z ⟨y, hy⟩ : Γ) * g) h1
        simpa using this
      rw [h2]
      exact (Z ⟨y, hy⟩).2
    have : Finite ↥Y₁ := Finite.of_equiv _ e₁.symm.toEquiv
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv]

end CFSG.CGT.PushingUpLit.CGT6
