module

public import CFSG.LinearAlgebra.RootGroupSL.ModelItemFour

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [Finite E] [CharP k 2]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma conj_mem_map_sup {S X : Type*} [Group S] [Group X] (Θ : S →* X)
    (J U : Subgroup S) {g : X} (hgJ : ∀ j ∈ J, g * Θ j * g⁻¹ = Θ j)
    (hgU : ∀ u ∈ U, g * Θ u * g⁻¹ ∈ (U.map Θ : Subgroup X)) :
    ∀ x ∈ J ⊔ U, g * Θ x * g⁻¹ ∈ ((J ⊔ U).map Θ : Subgroup X) := by
  let φ : S →* X :=
    { toFun := fun x => g * Θ x * g⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul]; group }
  have hφ : ∀ x : S, φ x = g * Θ x * g⁻¹ := fun x => rfl
  have hle : J ⊔ U ≤ (J.map Θ ⊔ U.map Θ).comap φ := by
    apply sup_le
    · intro j hj
      change φ j ∈ J.map Θ ⊔ U.map Θ
      rw [hφ j, hgJ j hj]
      exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem Θ hj)
    · intro u hu
      change φ u ∈ J.map Θ ⊔ U.map Θ
      rw [hφ u]
      exact Subgroup.mem_sup_right (hgU u hu)
  intro x hx
  have hx' : φ x ∈ J.map Θ ⊔ U.map Θ := hle hx
  rw [← Subgroup.map_sup] at hx'
  rwa [hφ x] at hx'

private lemma exists_mulAut_conj {S X : Type*} [Group S] [Group X] (Θ : S →* X)
    (hΘ : Function.Injective Θ) (H : Subgroup S) {g : X}
    (hgH : ∀ x ∈ H, g * Θ x * g⁻¹ ∈ (H.map Θ : Subgroup X))
    (hgH' : ∀ x ∈ H, g⁻¹ * Θ x * g ∈ (H.map Θ : Subgroup X)) :
    ∃ α : MulAut ↥H, ∀ x : ↥H, Θ (((α x : ↥H) : S)) = g * Θ (x : S) * g⁻¹ := by
  let e : ↥H ≃* ↥(H.map Θ) := Subgroup.equivMapOfInjective H Θ hΘ
  have he : ∀ y : ↥H, ((e y : ↥(H.map Θ)) : X) = Θ (y : S) := fun y =>
    Subgroup.coe_equivMapOfInjective_apply H Θ hΘ y
  let c : MulAut ↥(H.map Θ) :=
    { toFun := fun y => ⟨g * (y : X) * g⁻¹, by
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        rw [← hxy]
        exact hgH x hx⟩
      invFun := fun y => ⟨g⁻¹ * (y : X) * g, by
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        rw [← hxy]
        exact hgH' x hx⟩
      left_inv := by
        intro y
        apply Subtype.ext
        group
      right_inv := by
        intro y
        apply Subtype.ext
        group
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  refine ⟨e.trans (c.trans e.symm), ?_⟩
  intro x
  change Θ (((e.symm (c (e x)) : ↥H) : S)) = g * Θ (x : S) * g⁻¹
  calc Θ (((e.symm (c (e x)) : ↥H) : S))
      = ((e (e.symm (c (e x))) : ↥(H.map Θ)) : X) := (he (e.symm (c (e x)))).symm
    _ = (c (e x) : X) := by rw [MulEquiv.apply_symm_apply]
    _ = g * ((e x : ↥(H.map Θ)) : X) * g⁻¹ := rfl
    _ = g * Θ (x : S) * g⁻¹ := by rw [he x]

theorem exists_mem_centralizer_of_centralizer_normalizer (hm : 3 ≤ Module.finrank E VJ)
    (hc : 2 ≤ Module.finrank k E)
    (hcop : Nat.Coprime (Module.finrank k (VJ × V₀)) (Nat.card k - 1)) {e₀ : VJ}
    {l₀ : VJ →ₗ[E] E} (U : Subgroup (SpecialLinearGroup k (VJ × V₀)))
    (hU : (e₀ ≠ 0 ∧ U = datumU1 (modelIota (E := E) k V₀ e₀)) ∨
      (l₀ ≠ 0 ∧ U = datumU2 (modelPi k V₀ l₀)))
    {X : Type} [Group X] (Θ : SpecialLinearGroup k (VJ × V₀) →* X) (hΘ : Function.Injective Θ)
    (g : X) (hgJ : g ∈ Subgroup.centralizer (((modelJ k E VJ V₀).map Θ : Subgroup X) : Set X))
    (hgU : g ∈ Subgroup.normalizer ((U.map Θ : Subgroup X) : Set X)) :
    ∃ h : SpecialLinearGroup k (VJ × V₀),
      g * Θ h⁻¹ ∈ Subgroup.centralizer (((modelJ k E VJ V₀ ⊔ U).map Θ : Subgroup X) : Set X) := by
  have hgJeq : ∀ j ∈ modelJ k E VJ V₀, g * Θ j * g⁻¹ = Θ j := by
    intro j hj
    have hcomm : Θ j * g = g * Θ j := hgJ (Θ j) (Subgroup.mem_map_of_mem Θ hj)
    calc g * Θ j * g⁻¹ = Θ j * g * g⁻¹ := by rw [hcomm]
      _ = Θ j := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hgUmem : ∀ u ∈ U, g * Θ u * g⁻¹ ∈ (U.map Θ : Subgroup X) := by
    intro u hu
    exact (Subgroup.mem_normalizer_iff.mp hgU (Θ u)).mp (Subgroup.mem_map_of_mem Θ hu)
  have hgH : ∀ x ∈ modelJ k E VJ V₀ ⊔ U,
      g * Θ x * g⁻¹ ∈ ((modelJ k E VJ V₀ ⊔ U).map Θ : Subgroup X) :=
    conj_mem_map_sup Θ (modelJ k E VJ V₀) U hgJeq hgUmem
  have hgJinv : ∀ j ∈ modelJ k E VJ V₀, g⁻¹ * Θ j * (g⁻¹)⁻¹ = Θ j := by
    intro j hj
    have h := hgJeq j hj
    have hcomm : g * Θ j = Θ j * g := by
      have hg := congrArg (fun z => z * g) h
      simpa [mul_assoc] using hg
    calc g⁻¹ * Θ j * (g⁻¹)⁻¹ = g⁻¹ * (Θ j * g) := by group
      _ = g⁻¹ * (g * Θ j) := by rw [← hcomm]
      _ = Θ j := by group
  have hgUinv : ∀ u ∈ U, g⁻¹ * Θ u * (g⁻¹)⁻¹ ∈ (U.map Θ : Subgroup X) := by
    intro u hu
    have hginv : g⁻¹ ∈ Subgroup.normalizer ((U.map Θ : Subgroup X) : Set X) :=
      (Subgroup.normalizer ((U.map Θ : Subgroup X) : Set X)).inv_mem hgU
    exact (Subgroup.mem_normalizer_iff.mp hginv (Θ u)).mp (Subgroup.mem_map_of_mem Θ hu)
  have hgHinv : ∀ x ∈ modelJ k E VJ V₀ ⊔ U,
      g⁻¹ * Θ x * (g⁻¹)⁻¹ ∈ ((modelJ k E VJ V₀ ⊔ U).map Θ : Subgroup X) :=
    conj_mem_map_sup Θ (modelJ k E VJ V₀) U hgJinv hgUinv
  obtain ⟨α, hα⟩ := exists_mulAut_conj Θ hΘ (modelJ k E VJ V₀ ⊔ U) hgH
    (fun x hx => by simpa only [inv_inv] using hgHinv x hx)
  have hαJ : ∀ j : ↥(modelJ k E VJ V₀ ⊔ U),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → α j = j := by
    intro j hj
    apply Subtype.ext
    apply hΘ
    rw [hα j, hgJeq (j : SpecialLinearGroup k (VJ × V₀)) hj]
  obtain ⟨h, hh⟩ := exists_conj_of_mulAut_sup hm hc hcop U hU α hαJ
  refine ⟨h, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (Subgroup.mem_map (f := Θ) (K := modelJ k E VJ V₀ ⊔ U)).mp hy
  let xh : ↥(modelJ k E VJ V₀ ⊔ U) := ⟨x, hx⟩
  rw [← hxy] at ⊢
  have hpre : ∀ z : ↥(modelJ k E VJ V₀ ⊔ U),
      g * Θ ((α.symm z : ↥(modelJ k E VJ V₀ ⊔ U)) :
          SpecialLinearGroup k (VJ × V₀)) * g⁻¹ =
        Θ (z : SpecialLinearGroup k (VJ × V₀)) := by
    intro z
    have hz := hα (α.symm z)
    rw [MulEquiv.apply_symm_apply] at hz
    exact hz.symm
  have hkey : (g * (Θ h)⁻¹) * Θ x * (g * (Θ h)⁻¹)⁻¹ = Θ x := by
    have harg : h⁻¹ * x * h = ((α.symm xh : ↥(modelJ k E VJ V₀ ⊔ U)) :
        SpecialLinearGroup k (VJ × V₀)) := by
      have hx' := hh (α.symm xh)
      rw [MulEquiv.apply_symm_apply] at hx'
      rw [show (xh : SpecialLinearGroup k (VJ × V₀)) = x from rfl] at hx'
      rw [hx']
      group
    calc (g * (Θ h)⁻¹) * Θ x * (g * (Θ h)⁻¹)⁻¹
        = g * ((Θ h)⁻¹ * Θ x * Θ h) * g⁻¹ := by group
      _ = g * Θ (h⁻¹ * x * h) * g⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
      _ = g * Θ (((α.symm xh : ↥(modelJ k E VJ V₀ ⊔ U)) :
            SpecialLinearGroup k (VJ × V₀))) * g⁻¹ := by rw [harg]
      _ = Θ x := hpre xh
  have hcomm : (g * (Θ h)⁻¹) * Θ x = Θ x * (g * (Θ h)⁻¹) := by
    calc (g * (Θ h)⁻¹) * Θ x
        = (g * (Θ h)⁻¹) * Θ x * (g * (Θ h)⁻¹)⁻¹ * (g * (Θ h)⁻¹) := by group
      _ = Θ x * (g * (Θ h)⁻¹) := by rw [hkey]
  simpa only [map_inv] using hcomm.symm

end CFSG.LinearAlgebra.RootGroupSL
