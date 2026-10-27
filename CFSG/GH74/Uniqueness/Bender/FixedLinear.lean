module

public import CFSG.GH74.Uniqueness.Bender.OuterLinear
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwo

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff)

section Conjugation

variable {Γ : Type*} [Group Γ]

theorem nonempty_autFixed_mulEquiv_inf_centralizer {G : Subgroup Γ} {h₀ s : Γ} (hh₀ : h₀ ∈ G)
    (α : MulAut G)
    (hα : ∀ g : G, ((α g : G) : Γ) = (h₀ * s * h₀⁻¹) * g * (h₀ * s * h₀⁻¹)⁻¹) :
    Nonempty (autFixed α ≃* ↥(G ⊓ Subgroup.centralizer ({s} : Set Γ))) := by
  have key : ∀ x : G, α x = x ↔ (h₀⁻¹ * (x : Γ) * h₀) * s = s * (h₀⁻¹ * (x : Γ) * h₀) := by
    intro x
    rw [Subtype.ext_iff, hα x, mul_inv_eq_iff_eq_mul]
    constructor
    · intro hcomm
      calc h₀⁻¹ * (x : Γ) * h₀ * s = h₀⁻¹ * ((x : Γ) * (h₀ * s * h₀⁻¹)) * h₀ := by group
        _ = h₀⁻¹ * ((h₀ * s * h₀⁻¹) * (x : Γ)) * h₀ := by rw [hcomm]
        _ = s * (h₀⁻¹ * (x : Γ) * h₀) := by group
    · intro hcomm
      calc h₀ * s * h₀⁻¹ * (x : Γ) = h₀ * (s * (h₀⁻¹ * (x : Γ) * h₀)) * h₀⁻¹ := by group
        _ = h₀ * ((h₀⁻¹ * (x : Γ) * h₀) * s) * h₀⁻¹ := by rw [hcomm]
        _ = (x : Γ) * (h₀ * s * h₀⁻¹) := by group
  have h1 : ∀ x : autFixed α,
      h₀⁻¹ * (((x : G) : Γ)) * h₀ ∈ G ⊓ Subgroup.centralizer ({s} : Set Γ) := fun x =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh₀) x.1.2) hh₀,
      Subgroup.mem_centralizer_singleton_iff.mpr ((key x.1).mp x.2)⟩
  have h2 : ∀ y : ↥(G ⊓ Subgroup.centralizer ({s} : Set Γ)), h₀ * (y : Γ) * h₀⁻¹ ∈ G := fun y =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh₀ (Subgroup.mem_inf.mp y.2).1) (Subgroup.inv_mem _ hh₀)
  have h3 : ∀ y : ↥(G ⊓ Subgroup.centralizer ({s} : Set Γ)),
      α ⟨h₀ * (y : Γ) * h₀⁻¹, h2 y⟩ = ⟨h₀ * (y : Γ) * h₀⁻¹, h2 y⟩ := by
    intro y
    rw [key]
    have hy := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
    have e : h₀⁻¹ * (h₀ * (y : Γ) * h₀⁻¹) * h₀ = (y : Γ) := by group
    change h₀⁻¹ * (h₀ * (y : Γ) * h₀⁻¹) * h₀ * s = s * (h₀⁻¹ * (h₀ * (y : Γ) * h₀⁻¹) * h₀)
    rw [e]
    exact hy
  exact ⟨{ toFun := fun x => ⟨h₀⁻¹ * (((x : G) : Γ)) * h₀, h1 x⟩
           invFun := fun y => ⟨⟨h₀ * (y : Γ) * h₀⁻¹, h2 y⟩, h3 y⟩
           left_inv := fun x => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
           right_inv := fun y => Subtype.ext (by simp [mul_assoc])
           map_mul' := fun x y => Subtype.ext (by
             change h₀⁻¹ * (((x : G) : Γ) * ((y : G) : Γ)) * h₀ = _
             simp [mul_assoc]) }⟩

end Conjugation

section Main

open CFSG.BenderSuzuki

theorem outer_involution_coordinateG_structure {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ (2 * m)) (α : MulAut (coordinateG F)) (hα : α * α = 1)
    (hout : ¬ ∃ g : coordinateG F, ∀ x : coordinateG F, α x = g * x * g⁻¹) :
    Nonempty (autFixed α ≃* PSL2Model m) ∧
      ∀ β : MulAut (coordinateG F), (∀ x ∈ autFixed α, β x = x) → β = 1 ∨ β = α := by
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨-, a, σ, h₀, hα_apply, hh₀, hah₀, hσ1, hσσ, hσpow, k, hkset, hkcard⟩ :=
    exists_normal_form_outer_involution_coordinateG (n := 2 * m) (by omega) hF α hα hout
  have hhalf : 2 * m / 2 = m := by omega
  rw [hhalf] at hσpow hkcard
  have hσ2 : orderOf σ = 2 := by
    apply orderOf_eq_prime _ hσ1
    rw [sq]
    exact hσσ
  have hfixk : fixedField F σ = k := by
    ext x
    rw [mem_fixedField_iff]
    exact (Set.ext_iff.mp hkset x).symm
  have hcardk : Nat.card (fixedField F σ) = 2 ^ m := by rw [hfixk]; exact hkcard
  have hcomm : ∀ g : coordinateG F, ((α g : coordinateG F) : Equiv.Perm (Omega F)) =
      (h₀ * fieldExtension F σ * h₀⁻¹) * g * (h₀ * fieldExtension F σ * h₀⁻¹)⁻¹ := by
    intro g
    rw [hα_apply, hah₀]
  obtain ⟨e₁⟩ := nonempty_autFixed_mulEquiv_inf_centralizer hh₀ α hcomm
  refine ⟨⟨?_⟩, ?_⟩
  · have e₂ : ↥(coordinateG F ⊓ Subgroup.centralizer ({fieldExtension F σ} : Set _)) ≃*
        ↥(subfieldGImage (fixedField F σ)) :=
      MulEquiv.subgroupCongr (subfieldGImage_eq_centralizer hσ2).symm
    have e₃ := pslEquivSubfieldGImage (fixedField F σ)
    haveI : Fintype ↥(fixedField F σ) := Fintype.ofFinite _
    haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
    have e₄ : ↥(fixedField F σ) ≃+* GaloisField 2 m :=
      FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardk,
          GaloisField.card 2 m (by omega)])
    exact (e₁.trans e₂).trans (e₃.symm.trans (CFSG.GorensteinWalter.psl2RingEquiv e₄))
  · intro β hβ
    obtain ⟨c, -, -, hex⟩ := linear_two_automorphism_semilinear_isomorphism F
    obtain ⟨b, hb, -⟩ := hex β
    have hh₀E : h₀ ∈ coordinateE F := ((coordinateG_le_D F).trans (coordinateD_le_E F)) hh₀
    have hsqhat : fieldExtension F σ * fieldExtension F σ = 1 := by
      have := congrArg (CFSG.Wreathed.CentralSL2.fieldPerm F) hσσ
      rw [map_mul, map_one, CFSG.Wreathed.CentralSL2.fieldPerm_apply] at this
      exact this
    have hb' : h₀⁻¹ * (b : Equiv.Perm (Omega F)) * h₀ ∈
        coordinateE F ⊓ Subgroup.centralizer (subfieldGImage (fixedField F σ) : Set _) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ hh₀E) b.2) hh₀E, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [subfieldGImage_eq_centralizer hσ2] at hy
      obtain ⟨hyG, hyc⟩ := Subgroup.mem_inf.mp hy
      have hyc' := Subgroup.mem_centralizer_singleton_iff.mp hyc
      have hxG : h₀ * y * h₀⁻¹ ∈ coordinateG F :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hh₀ hyG) (Subgroup.inv_mem _ hh₀)
      have hxfix : α ⟨h₀ * y * h₀⁻¹, hxG⟩ = ⟨h₀ * y * h₀⁻¹, hxG⟩ := by
        apply Subtype.ext
        rw [hcomm]
        change (h₀ * fieldExtension F σ * h₀⁻¹) * (h₀ * y * h₀⁻¹) *
          (h₀ * fieldExtension F σ * h₀⁻¹)⁻¹ = h₀ * y * h₀⁻¹
        have e1 : (h₀ * fieldExtension F σ * h₀⁻¹) * (h₀ * y * h₀⁻¹) *
            (h₀ * fieldExtension F σ * h₀⁻¹)⁻¹ =
            h₀ * (fieldExtension F σ * y * (fieldExtension F σ)⁻¹) * h₀⁻¹ := by group
        rw [e1, mul_inv_eq_iff_eq_mul.mpr hyc'.symm]
      have hβx := hβ ⟨h₀ * y * h₀⁻¹, hxG⟩ hxfix
      have h1 := hb ⟨h₀ * y * h₀⁻¹, hxG⟩
      rw [hβx] at h1
      change h₀ * y * h₀⁻¹ = (b : Equiv.Perm (Omega F)) * (h₀ * y * h₀⁻¹) *
        (b : Equiv.Perm (Omega F))⁻¹ at h1
      have h2 : (h₀ * y * h₀⁻¹) * (b : Equiv.Perm (Omega F)) =
          (b : Equiv.Perm (Omega F)) * (h₀ * y * h₀⁻¹) := eq_mul_inv_iff_mul_eq.mp h1
      calc y * (h₀⁻¹ * (b : Equiv.Perm (Omega F)) * h₀)
          = h₀⁻¹ * ((h₀ * y * h₀⁻¹) * (b : Equiv.Perm (Omega F))) * h₀ := by group
        _ = h₀⁻¹ * ((b : Equiv.Perm (Omega F)) * (h₀ * y * h₀⁻¹)) * h₀ := by rw [h2]
        _ = (h₀⁻¹ * (b : Equiv.Perm (Omega F)) * h₀) * y := by group
    have hzp : h₀⁻¹ * (b : Equiv.Perm (Omega F)) * h₀ ∈ Subgroup.zpowers (fieldExtension F σ) := by
      rw [← inf_centralizer_subfieldGImage hm hF hσpow]
      exact hb'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have hj2 : fieldExtension F σ ^ j = 1 ∨ fieldExtension F σ ^ j = fieldExtension F σ := by
      obtain ⟨r, hr | hr⟩ := Int.even_or_odd' j
      · left
        rw [hr, zpow_mul, zpow_two, hsqhat, one_zpow]
      · right
        rw [hr, zpow_add_one, zpow_mul, zpow_two, hsqhat, one_zpow, one_mul]
    have hbconj : (b : Equiv.Perm (Omega F)) =
        h₀ * (h₀⁻¹ * (b : Equiv.Perm (Omega F)) * h₀) * h₀⁻¹ := by group
    rcases hj2 with hj1 | hj1
    · left
      have hb1 : (b : Equiv.Perm (Omega F)) = 1 := by
        rw [hbconj, ← hj, hj1]
        group
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hb g, hb1]
      simp
    · right
      have hba : (b : Equiv.Perm (Omega F)) = a := by
        rw [hbconj, ← hj, hj1, hah₀]
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hb g, hα_apply g, hba]

theorem BenderType.fixed_linear {K : Type*} [Group K] {n : ℕ} (h : BenderType K n 1 1)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    ∃ m : ℕ, n = 2 * m ∧ Nonempty (autFixed α ≃* PSL2Model m) ∧
      ∀ β : MulAut K, (∀ x ∈ autFixed α, β x = x) → β = 1 ∨ β = α := by
  obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let θ : K ≃* coordinateG (GaloisField 2 n) := e.trans (pslEquivCoordinateG (GaloisField 2 n))
  have hα' := mulAut_congr_sq_eq_one θ hα
  have hout' := not_inner_congr θ hout
  obtain ⟨hEven, -⟩ := exists_normal_form_outer_involution_coordinateG (by omega) hcard _ hα' hout'
  obtain ⟨m, hm⟩ := hEven
  have hnm : n = 2 * m := by omega
  subst hnm
  obtain ⟨⟨e₁⟩, hd1⟩ :=
    outer_involution_coordinateG_structure (m := m) (by omega) hcard (MulAut.congr θ α) hα' hout'
  refine ⟨m, rfl, ⟨(autFixedEquiv θ α).trans e₁⟩, fun β hβ => ?_⟩
  have hβ' : ∀ y ∈ autFixed (MulAut.congr θ α), MulAut.congr θ β y = y := by
    intro y hy
    have hy' := (mem_autFixed_congr_iff θ α y).mp hy
    change θ (β (θ.symm y)) = y
    rw [hβ _ hy', MulEquiv.apply_symm_apply]
  rcases hd1 (MulAut.congr θ β) hβ' with h1 | h1
  · left
    apply (MulAut.congr θ).injective
    rw [h1, map_one]
  · right
    exact (MulAut.congr θ).injective h1

end Main

end CFSG.GH74.Uniqueness.Bender
