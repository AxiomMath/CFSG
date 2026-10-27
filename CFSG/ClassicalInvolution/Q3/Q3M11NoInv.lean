module

public import CFSG.ClassicalInvolution.Q3.Q3M11Sqrt
public import CFSG.ClassicalInvolution.Q3.Q3NMM11
public import CFSG.ClassicalInvolution.Q3.Q3T7SectA
public import CFSG.ClassicalInvolution.Asc77.AscCX4A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Normalizer

variable {H : Type} [Group H]

theorem exists_conj_of_normalizes
    (Ψ : ↥NativeSporadic.M11 →* H) (hΨ : Function.Injective Ψ) (a : H)
    (ha : ∀ x, a * Ψ x * a⁻¹ ∈ Ψ.range ∧ a⁻¹ * Ψ x * a ∈ Ψ.range) :
    ∃ k : ↥NativeSporadic.M11, ∀ x, a * Ψ x * a⁻¹ = Ψ (k * x * k⁻¹) := by
  classical
  choose f hf using fun x => (ha x).1
  choose g hg using fun x => (ha x).2
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    apply hΨ
    rw [map_mul Ψ (f x) (f y), hf, hf, hf, map_mul Ψ x y]
    group
  let φ : ↥NativeSporadic.M11 ≃* ↥NativeSporadic.M11 :=
    { toFun := f
      invFun := g
      left_inv := fun x => hΨ (by rw [hg, hf]; group)
      right_inv := fun x => hΨ (by rw [hf, hg]; group)
      map_mul' := hmul }
  obtain ⟨k, hk⟩ := Q3NM.m11_aut_inner φ
  refine ⟨k, fun x => ?_⟩
  have h1 : f x = k * x * k⁻¹ := by
    have := congrArg (fun α : MulAut ↥NativeSporadic.M11 => α x) hk
    exact this.trans (by simp [MulAut.conj_apply])
  rw [← h1, hf]

end Normalizer

section Core


theorem m11NoInverted_core {X : Type} [Group X]
    {Φ : Set (Subgroup X)} (hgen : omegaGen Φ = ⊤) (hM : Uniform.HasM11TypeU 3 1 Φ)
    {H : Type} [Group H] (ι : X →* H) (hι : Function.Injective ι) (a : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x)) (ha2 : a * a = ι z) :
    False := by
  obtain ⟨-, D, hc, i, hk⟩ := hM
  have hsub : ∀ j : Fin D.card, j = i := fun j => Fin.ext (by
    have h1 := i.2
    have h2 := j.2
    omega)
  let ψ : ↥NativeSporadic.M11 →* X := Uniform.castHom hk (D.hom i)
  have hker : ψ.ker ≤ Subgroup.center ↥NativeSporadic.M11 :=
    Uniform.castHom_ker_le_center hk (D.hom i) (D.ker_le_center i)
  have hcenter : Subgroup.center ↥NativeSporadic.M11 = ⊥ := center_m11_eq_bot m11Facts
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hker.trans hcenter.le)
  have hsurj : Function.Surjective ψ := by
    have h := Q3T7.hom_surjective_of_gen3 D hc hgen i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [Uniform.range_castHom]
    exact h
  have key : ∀ {L : Subgroup X}, L ∈ Φ → ∃ J ∈ M11ClassicalClass, L = J.map ψ := by
    intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : i = j := (hsub j).symm
    obtain ⟨R', hR', hRR⟩ := Uniform.exists_map_castHom hk (D.hom i) hR
    exact ⟨R', hR', hLR.trans hRR.symm⟩
  obtain ⟨J, ⟨w, hw⟩, rfl⟩ := key hA
  have hψw : ψ w = z := by
    have hmem : ψ w ∈ J.map ψ := Subgroup.mem_map_of_mem _ hw.mem
    have hsq : ψ w * ψ w = 1 := by
      rw [← map_mul]
      have h2 := pow_orderOf_eq_one w
      rw [hw.orderOf_eq_two] at h2
      rw [← sq, h2, map_one]
    rcases hzA.unique _ hmem hsq with h | h
    · exact absurd (hinj (h.trans ψ.map_one.symm)) hw.ne_one
    · exact h
  set Ψ : ↥NativeSporadic.M11 →* H := ι.comp ψ with hΨdef
  have hΨ : Function.Injective Ψ := hι.comp hinj
  have hrange : Ψ.range = ι.range := by
    rw [hΨdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top]
  have haΨ : ∀ x, a * Ψ x * a⁻¹ ∈ Ψ.range ∧ a⁻¹ * Ψ x * a ∈ Ψ.range := by
    intro x
    rw [hrange]
    exact ha (ψ x)
  obtain ⟨k, hkconj⟩ := exists_conj_of_normalizes Ψ hΨ a haΨ
  have hΨw : Ψ w = a * a := by
    show ι (ψ w) = a * a
    rw [hψw, ha2]
  have hkk : k * k = w := by
    have hcen : w⁻¹ * (k * k) ∈ Subgroup.center ↥NativeSporadic.M11 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : Ψ (w * y * w⁻¹) = Ψ ((k * k) * y * (k * k)⁻¹) := by
        calc Ψ (w * y * w⁻¹) = Ψ w * Ψ y * (Ψ w)⁻¹ := by rw [map_mul, map_mul, map_inv]
          _ = (a * a) * Ψ y * (a * a)⁻¹ := by rw [hΨw]
          _ = a * (a * Ψ y * a⁻¹) * a⁻¹ := by group
          _ = a * Ψ (k * y * k⁻¹) * a⁻¹ := by rw [hkconj y]
          _ = Ψ (k * (k * y * k⁻¹) * k⁻¹) := hkconj _
          _ = Ψ ((k * k) * y * (k * k)⁻¹) := by
              rw [show k * (k * y * k⁻¹) * k⁻¹ = (k * k) * y * (k * k)⁻¹ by group]
      have h2 := hΨ h1
      calc y * (w⁻¹ * (k * k)) = w⁻¹ * (w * y * w⁻¹) * (k * k) := by group
        _ = w⁻¹ * ((k * k) * y * (k * k)⁻¹) * (k * k) := by rw [h2]
        _ = (w⁻¹ * (k * k)) * y := by group
    rw [hcenter, Subgroup.mem_bot] at hcen
    exact (inv_mul_eq_one.mp hcen).symm
  have hJO : oddCoreOf J = ⊥ := by
    rw [oddCoreOf, classicalInvolutionOddCore_eq_bot_of_m11 hw, Subgroup.map_bot]
  have hAO : oddCoreOf (J.map ψ) = ⊥ := by
    let e : ↥NativeSporadic.M11 ≃* X := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
    have he : e.toMonoidHom = ψ := rfl
    have := CX.CX4.oddCoreOf_map_eq_bot e hJO
    rwa [he] at this
  have hkJ : ∀ y ∈ J, k * y = y * k := by
    intro y hy
    obtain ⟨n, hn, hny⟩ := haA (ψ y) (Subgroup.mem_map_of_mem _ hy)
    rw [hAO, Subgroup.mem_bot] at hn
    subst hn
    have h1 : Ψ (k * y * k⁻¹) = Ψ y := by
      rw [← hkconj y]
      rw [one_mul] at hny
      exact hny
    have h2 := hΨ h1
    calc k * y = (k * y * k⁻¹) * k := by group
      _ = y * k := by rw [h2]
  exact m11_no_sqrt_centralizing hw hkk hkJ

end Core

end CFSG.ClassicalInvolution.Q3
