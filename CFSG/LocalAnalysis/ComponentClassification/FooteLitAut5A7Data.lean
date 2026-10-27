module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5A7
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalanceTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5Transport

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5A7

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)
open scoped commutatorElement

theorem dihedral_four_commutator_central :
    ∀ x y z : DihedralGroup 4, ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
  decide

variable (R : Sylow 2 A7)

theorem commutator_central (a b : A7) (ha : a ∈ (R : Subgroup A7)) (hb : b ∈ (R : Subgroup A7)) :
    ∀ s ∈ (R : Subgroup A7), ⁅a, b⁆ * s = s * ⁅a, b⁆ := by
  obtain ⟨ρ⟩ := AutL2Facts.sylow_two_dihedral_a7 (MulEquiv.refl A7) R
  intro s hs
  have h := dihedral_four_commutator_central (ρ ⟨a, ha⟩) (ρ ⟨b, hb⟩) (ρ ⟨s, hs⟩)
  simp only [← map_commutatorElement, ← map_mul] at h
  exact congrArg Subtype.val (ρ.injective h)

theorem conj_centralizer_a7 (β : MulAut A7) (hβ : β ∉ innAut5 A7) (hβ2 : β * β = 1) :
    ∃ g : A7, ∀ r ∈ (R : Subgroup A7), (MulAut.conj g * β * (MulAut.conj g)⁻¹) r = r := by
  obtain ⟨g, hg⟩ := exists_conj_central R (π := autPerm β)
    (by rw [← map_mul, hβ2, map_one]) (autPerm_sign_of_not_mem hβ)
  refine ⟨g, fun r hr => Subtype.ext ?_⟩
  rw [coe_apply, map_mul, map_mul, map_inv, autPerm_conj]
  have h1 := hg r hr
  set x := (g : Perm (Fin 7)) * autPerm β * (g : Perm (Fin 7))⁻¹ with hx
  calc x * r * x⁻¹ = r * x * x⁻¹ := by rw [← h1]
    _ = r := by group

theorem field_inner_a7 (β : MulAut A7) (hβ : β ∉ innAut5 A7)
    (hβ2 : β * β = 1) (hmap : (R : Subgroup A7).map β.toMonoidHom = R) :
    ∃ r₀ ∈ (R : Subgroup A7), r₀ * r₀ = 1 ∧ ∀ r ∈ (R : Subgroup A7), β r = r₀ * r * r₀⁻¹ := by
  obtain ⟨τ, hτ, hτ2, hτR⟩ := exists_odd_central R
  have hβR : ∀ r ∈ (R : Subgroup A7), β r ∈ (R : Subgroup A7) := fun r hr => by
    rw [← hmap]
    exact mem_map_of_mem _ hr
  obtain ⟨r₀, hr₀, h | h⟩ := autPerm_eq_of_normalizes R hτ hτ2 hτR hβR
  · exfalso
    have h1 := autPerm_sign_of_not_mem hβ
    rw [h] at h1
    rw [mem_alternatingGroup.mp r₀.2] at h1
    exact absurd h1 (by decide)
  have hπ2 : autPerm β * autPerm β = 1 := by rw [← map_mul, hβ2, map_one]
  have hτr₀ := hτR r₀ hr₀
  refine ⟨r₀, hr₀, Subtype.ext ?_, fun r hr => Subtype.ext ?_⟩
  · rw [h] at hπ2
    have h2 : (r₀ : Perm (Fin 7)) * τ * ((r₀ : Perm (Fin 7)) * τ) =
        (r₀ : Perm (Fin 7)) * r₀ := by
      calc (r₀ : Perm (Fin 7)) * τ * ((r₀ : Perm (Fin 7)) * τ)
          = r₀ * (τ * r₀) * τ := by group
        _ = r₀ * (r₀ * τ) * τ := by rw [← hτr₀]
        _ = r₀ * r₀ * (τ * τ) := by group
        _ = (r₀ : Perm (Fin 7)) * r₀ := by rw [hτ2, mul_one]
    rw [Subgroup.coe_mul, ← h2, hπ2]
    rfl
  · rw [coe_apply, h]
    have h1 := hτR r hr
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (r₀ : Perm (Fin 7)) * τ * r * ((r₀ : Perm (Fin 7)) * τ)⁻¹
        = r₀ * (τ * r) * τ⁻¹ * (r₀ : Perm (Fin 7))⁻¹ := by group
      _ = r₀ * (r * τ) * τ⁻¹ * (r₀ : Perm (Fin 7))⁻¹ := by rw [h1]
      _ = r₀ * r * (r₀ : Perm (Fin 7))⁻¹ := by group

theorem center_le_a7 (X : Subgroup (MulAut A7))
    (hX : IsPGroup 2 X) (hRX : (R : Subgroup A7).map (MulAut.conj : A7 →* MulAut A7) ≤ X)
    (R₁ : Subgroup (MulAut A7)) (hR₁X : R₁ ≤ X) (hR₁ : Nonempty (R₁ ≃* (R : Subgroup A7)))
    (c : MulAut A7) (hc : c ∈ R₁) (hcZ : ∀ d ∈ R₁, c * d = d * c) :
    ∃ r ∈ (R : Subgroup A7), (∀ s ∈ (R : Subgroup A7), r * s = s * r) ∧ c = MulAut.conj r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ, hτ2, hτR⟩ := exists_odd_central R
  have hY : X.comap (MulAut.conj : A7 →* MulAut A7) = R :=
    R.3 (hX.comap_of_injective _ conj_injective) fun r hr => hRX ⟨r, hr, rfl⟩
  have hnorm : ∀ x ∈ X, ∀ r ∈ (R : Subgroup A7), x r ∈ (R : Subgroup A7) := fun x hx r hr => by
    have h1 : MulAut.conj (x r) ∈ X := by
      rw [← mulAut_conj_conj5]
      exact mul_mem (mul_mem hx (hRX ⟨r, hr, rfl⟩)) (inv_mem hx)
    have h2 : x r ∈ X.comap (MulAut.conj : A7 →* MulAut A7) := h1
    rwa [hY] at h2
  have hshape : ∀ x ∈ X, ∃ a ∈ (R : Subgroup A7), ∃ u : Perm (Fin 7), (u = 1 ∨ u = τ) ∧
      autPerm x = a * u := fun x hx => by
    obtain ⟨a, ha, h | h⟩ := autPerm_eq_of_normalizes R hτ hτ2 hτR (hnorm x hx)
    · exact ⟨a, ha, 1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨a, ha, τ, Or.inr rfl, h⟩
  have huR : ∀ u : Perm (Fin 7), (u = 1 ∨ u = τ) →
      ∀ r ∈ (R : Subgroup A7), u * (r : Perm (Fin 7)) = r * u := fun u hu r hr => by
    rcases hu with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hτR r hr).symm
  have huw : ∀ u w : Perm (Fin 7), (u = 1 ∨ u = τ) → (w = 1 ∨ w = τ) → u * w = w * u := by
    rintro u w (rfl | rfl) (rfl | rfl) <;> simp
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, ∃ z ∈ (R : Subgroup A7),
      (∀ s ∈ (R : Subgroup A7), z * s = s * z) ∧ ⁅x, y⁆ = MulAut.conj z := by
    intro x hx y hy
    obtain ⟨a, ha, u, hu, hxa⟩ := hshape x hx
    obtain ⟨b, hb, w, hw, hyb⟩ := hshape y hy
    refine ⟨⁅a, b⁆, ?_, commutator_central R a b ha hb, autPerm.injective ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · rw [map_commutatorElement, hxa, hyb, autPerm_conj,
        commutatorElement_mul_mul_eq (huR u hu b hb) (huw u w hu hw) (huR w hw a ha)]
      simp [commutatorElement_def]
  obtain ⟨e₁⟩ := hR₁
  obtain ⟨ρ⟩ := AutL2Facts.sylow_two_dihedral_a7 (MulEquiv.refl A7) R
  have hc' : c ∈ ⁅R₁, R₁⁆ := AutL2Facts.mem_commutator_of_dihedral (dvd_refl 4) (e₁.trans ρ) hc hcZ
  have hle : ⁅X, X⁆ ≤ ((R : Subgroup A7) ⊓ centralizer ((R : Subgroup A7) : Set A7)).map
      (MulAut.conj : A7 →* MulAut A7) := by
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨z, hz, hzZ, hxy⟩ := hcomm x hx y hy
    exact ⟨z, ⟨hz, mem_centralizer_iff.mpr fun s hs => (hzZ s hs).symm⟩, hxy.symm⟩
  obtain ⟨z, ⟨hz, hzC⟩, hzc⟩ := hle (commutator_mono hR₁X hR₁X hc')
  exact ⟨z, hz, fun s hs => (mem_centralizer_iff.mp hzC s hs).symm, hzc.symm⟩

theorem foote5AutData_a7 :
    Foote5AutData A7 (innAut5 A7) where
  inn_le := le_rfl
  normal := innAut5_normal A7
  sq_mem := fun _ hα => mul_mem hα hα
  commutator_mem := commutator_mem_a7
  conj_involution := conj_involution_a7
  centralizer_sylow := fun R P hP hPR => centralizer_sylow_a7 R P hP hPR
  centralizer_sylow_lin := fun R _ α hα ⟨_, hk⟩ hfix => exists_center_of_inner R α hα hk hfix
  not_commute := fun _ _ hα hαI _ _ _ _ => absurd hα hαI
  conj_centralizer := fun R β hβ hβ2 => conj_centralizer_a7 R β hβ hβ2
  pgl_fixed := fun _ _ hα hαI _ _ => absurd hα hαI
  field_inner := fun R β hβ hβ2 hmap => field_inner_a7 R β hβ hβ2 hmap
  center_le := fun R _ X hX hRX R₁ hR₁X hR₁ c hc hcZ =>
    center_le_a7 R X hX hRX R₁ hR₁X hR₁ c hc hcZ
  two_generated := fun R hab => by
    obtain ⟨a, ha, b, hb, hab'⟩ := sylow_noncomm R
    exact absurd (hab a ha b hb) hab'

theorem exists_foote5AutData_of_a7
    {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (e : 𝕊 ≃* alternatingGroup (Fin 7)) :
    ∃ Lin : Subgroup (MulAut 𝕊), Foote5AutData 𝕊 Lin :=
  ⟨_, Aut5.foote5AutData_map e.symm foote5AutData_a7⟩

end CFSG.ComponentClassification.FooteLit.Aut5A7
