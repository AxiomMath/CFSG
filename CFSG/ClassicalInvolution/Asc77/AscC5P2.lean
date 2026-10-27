module

public import CFSG.ClassicalInvolution.Asc77.AscC5P1
public import CFSG.ClassicalInvolution.Asc77.AscCX9P
public import CFSG.ClassicalInvolution.Asc77.AscC5OM26
public import CFSG.ClassicalInvolution.Asc77.AscC5OM3

public section

namespace CFSG.ClassicalInvolution.Asc77.C5P

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

@[expose] def TwoClasses (p : ℕ) (H : Type) [Group H] : Prop :=
  ∀ u v w : H, orderOf u = p → orderOf v = p → orderOf w = p →
    (∃ g, v = g * u * g⁻¹) ∨ (∃ g, w = g * u * g⁻¹) ∨ (∃ g, w = g * v * g⁻¹)

theorem twoClasses_of_mulEquiv {p : ℕ} {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (h : TwoClasses p H') : TwoClasses p H := by
  intro u v w hu hv hw
  have hu' : orderOf (e u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
  have hv' : orderOf (e v) = p := by rw [MulEquiv.orderOf_eq]; exact hv
  have hw' : orderOf (e w) = p := by rw [MulEquiv.orderOf_eq]; exact hw
  have pull : ∀ x y : H, (∃ g, e y = g * e x * g⁻¹) → ∃ g, y = g * x * g⁻¹ := by
    rintro x y ⟨g, hg⟩
    refine ⟨e.symm g, e.injective ?_⟩
    rw [hg, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rcases h _ _ _ hu' hv' hw' with h1 | h1 | h1
  · exact Or.inl (pull _ _ h1)
  · exact Or.inr (Or.inl (pull _ _ h1))
  · exact Or.inr (Or.inr (pull _ _ h1))

theorem twoClasses_sl2 {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    TwoClasses (ringChar F) (SL(2, F)) :=
  fun _ _ _ hu hv hw => sl2_two_classes h2 hu hv hw

theorem not_conj_of_not_diagTriv {p : ℕ} {H : Type} [Group H] (h : TwoClasses p H)
    {α : H ≃* H} (hα : ¬ CX.DiagTriv p α) {w : H} (hw : orderOf w = p) :
    ¬ ∃ g, α w = g * w * g⁻¹ := by
  unfold CX.DiagTriv at hα
  push Not at hα
  obtain ⟨u, hu, hun⟩ := hα
  rintro ⟨k, hk⟩
  have hau : orderOf (α u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
  rcases h u (α u) w hu hau hw with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hun g hg
  ·
    apply hun ((α g)⁻¹ * k * g)
    have e1 : α w = α g * α u * (α g)⁻¹ := by rw [hg, map_mul, map_mul, map_inv]
    calc α u = (α g)⁻¹ * α w * α g := by rw [e1]; group
      _ = (α g)⁻¹ * k * g * u * ((α g)⁻¹ * k * g)⁻¹ := by rw [hk, hg]; group
  ·
    have e1 : α w = α g * α (α u) * (α g)⁻¹ := by rw [hg, map_mul, map_mul, map_inv]
    have e2 : α (α u) = ((α g)⁻¹ * k * g) * α u * ((α g)⁻¹ * k * g)⁻¹ := by
      calc α (α u) = (α g)⁻¹ * α w * α g := by rw [e1]; group
        _ = ((α g)⁻¹ * k * g) * α u * ((α g)⁻¹ * k * g)⁻¹ := by rw [hk, hg]; group
    apply hun (α.symm ((α g)⁻¹ * k * g))
    apply α.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, e2]

theorem diagTriv_trans_of_not {p : ℕ} {H : Type} [Group H] (h : TwoClasses p H)
    {α β : H ≃* H} (hα : ¬ CX.DiagTriv p α) (hβ : ¬ CX.DiagTriv p β) :
    CX.DiagTriv p (α.trans β) := by
  intro w hw
  have haw : orderOf (α w) = p := by rw [MulEquiv.orderOf_eq]; exact hw
  have hbaw : orderOf (β (α w)) = p := by rw [MulEquiv.orderOf_eq]; exact haw
  rcases h w (α w) (β (α w)) hw haw hbaw with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · exact absurd ⟨g, hg⟩ (not_conj_of_not_diagTriv h hα hw)
  · exact ⟨g, hg⟩
  · exact absurd ⟨g, hg⟩ (not_conj_of_not_diagTriv h hβ haw)

variable {p f : ℕ} [Fact p.Prime]

theorem exists_sl2_equiv_of_isOm5 {K₀ K₀' : Type} [Group K₀] [Group K₀']
    {L : CX.TwinGroup K₀ K₀'} (hL : CX.IsOm5 p f L) :
    Nonempty (K₀ ≃* SL(2, GaloisField p f)) ∧ Nonempty (K₀' ≃* SL(2, GaloisField p f)) := by
  obtain ⟨Φ, z', a₀, b₀, hD⟩ := hL
  obtain ⟨fr⟩ := C5O.M.exists_frame hD
  have h2 : (2 : GaloisField p f) ≠ 0 := C5O.M.two_ne_zero_gf f hD.odd
  have key : ∀ (k : Fin 2) (B : Subgroup L.X),
      B = (longRootSp2 (GaloisField p f) 2 k).map fr.ψ →
        Nonempty (SL(2, GaloisField p f) ≃* B) := by
    intro k B hB
    have hinj : Function.Injective (fr.ψ.comp (longBlock (GaloisField p f) 2 k)) := by
      intro x y hxy
      apply longBlock_injective k
      exact fr.injOn_L h2 k ⟨x, rfl⟩ ⟨y, rfl⟩ hxy
    have hrange : (fr.ψ.comp (longBlock (GaloisField p f) 2 k)).range = B := by
      rw [hB, MonoidHom.range_comp]
      rfl
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩
  obtain ⟨eA⟩ := key 0 L.A fr.hA
  obtain ⟨eA'⟩ := key 1 L.A' fr.hA'
  exact ⟨⟨L.ι.trans eA.symm⟩, ⟨L.ι'.trans eA'.symm⟩⟩

theorem exists_twin_iso {K₀ K₀' : Type} [Group K₀] [Group K₀']
    {L₁ L₂ : CX.TwinGroup K₀ K₀'} (h₁ : CX.IsOm5 p f L₁) (h₂ : CX.IsOm5 p f L₂) :
    ∃ φ : L₁.X ≃* L₂.X, L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A ∧
      L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A' := by
  obtain ⟨Φ₁, z₁, a₁, b₁, hD₁⟩ := h₁
  obtain ⟨Φ₂, z₂, a₂, b₂, hD₂⟩ := h₂
  obtain ⟨fr₁⟩ := C5O.M.exists_frame hD₁
  obtain ⟨fr₂⟩ := C5O.M.exists_frame hD₂
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective fr₁.ψ fr₁.surj
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective fr₂.ψ fr₂.surj
  let e := QuotientGroup.quotientMulEquivOfEq (fr₁.ker.trans fr₂.ker.symm)
  let φ : L₁.X ≃* L₂.X := e₁.symm.trans (e.trans e₂)
  have hφ : ∀ s, φ (fr₁.ψ s) = fr₂.ψ s := by
    intro s
    have h1 : e₁.symm (fr₁.ψ s) = QuotientGroup.mk s := by
      rw [MulEquiv.symm_apply_eq]; rfl
    show e₂ (e (e₁.symm (fr₁.ψ s))) = fr₂.ψ s
    rw [h1]
    rfl
  have hmap : ∀ k : Fin 2, ((longRootSp2 (GaloisField p f) 2 k).map fr₁.ψ).map
      (φ : L₁.X →* L₂.X) = (longRootSp2 (GaloisField p f) 2 k).map fr₂.ψ := by
    intro k
    rw [Subgroup.map_map]
    congr 1
    ext s
    exact hφ s
  exact ⟨φ, by rw [fr₁.hA, fr₂.hA, hmap], by rw [fr₁.hA', fr₂.hA', hmap]⟩

end CFSG.ClassicalInvolution.Asc77.C5P

namespace CFSG.ClassicalInvolution.Asc77.CX

open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem diagThree_proved : DiagThree p f := by
  classical
  intro K₀ K₀' _ _ L₁ L₂ L₃ h₁ h₂ h₃
  obtain ⟨⟨eK⟩, ⟨eK'⟩⟩ := C5P.exists_sl2_equiv_of_isOm5 h₁
  have hp2 : p ≠ 2 := by
    obtain ⟨Φ, z', a₀, b₀, hD⟩ := h₁
    exact hD.odd
  have h2 : (2 : GaloisField p f) ≠ 0 := C5O.M.two_ne_zero_gf f hp2
  have hchar : ringChar (GaloisField p f) = p := ringChar.eq (GaloisField p f) p
  have hTC : C5P.TwoClasses p K₀ := by
    have := C5P.twoClasses_of_mulEquiv eK (C5P.twoClasses_sl2 h2)
    rwa [hchar] at this
  have hTC' : C5P.TwoClasses p K₀' := by
    have := C5P.twoClasses_of_mulEquiv eK' (C5P.twoClasses_sl2 h2)
    rwa [hchar] at this
  obtain ⟨φ₁₂, hA₁₂, hA'₁₂⟩ := C5P.exists_twin_iso h₁ h₂
  obtain ⟨φ₂₃, hA₂₃, hA'₂₃⟩ := C5P.exists_twin_iso h₂ h₃
  by_cases h12 : DiagRel p L₁ L₂
  · exact Or.inl h12
  by_cases h23 : DiagRel p L₂ L₃
  · exact Or.inr (Or.inr h23)
  refine Or.inr (Or.inl ⟨φ₁₂.trans φ₂₃, TwinGroup.map_trans φ₁₂ φ₂₃ hA₁₂ hA₂₃,
    TwinGroup.map_trans φ₁₂ φ₂₃ hA'₁₂ hA'₂₃, ?_⟩)
  have n12 : ¬ (DiagTriv p (TwinGroup.restr φ₁₂ hA₁₂) ↔
      DiagTriv p (TwinGroup.restr' φ₁₂ hA'₁₂)) := fun h => h12 ⟨φ₁₂, hA₁₂, hA'₁₂, h⟩
  have n23 : ¬ (DiagTriv p (TwinGroup.restr φ₂₃ hA₂₃) ↔
      DiagTriv p (TwinGroup.restr' φ₂₃ hA'₂₃)) := fun h => h23 ⟨φ₂₃, hA₂₃, hA'₂₃, h⟩
  rw [TwinGroup.restr_trans φ₁₂ φ₂₃ hA₁₂ hA₂₃,
    TwinGroup.restr'_trans φ₁₂ φ₂₃ hA'₁₂ hA'₂₃]
  have flip1 : ∀ {P Q : Prop}, ¬ (P ↔ Q) → P → ¬ Q := fun h hP hQ => h ⟨fun _ => hQ, fun _ => hP⟩
  have flip2 : ∀ {P Q : Prop}, ¬ (P ↔ Q) → ¬ P → Q := fun h hP => by
    by_contra hQ; exact h ⟨fun h' => absurd h' hP, fun h' => absurd h' hQ⟩
  by_cases ha : DiagTriv p (TwinGroup.restr φ₁₂ hA₁₂) <;>
    by_cases hb : DiagTriv p (TwinGroup.restr φ₂₃ hA₂₃)
  · have ha' := flip1 n12 ha
    have hb' := flip1 n23 hb
    exact ⟨fun _ => C5P.diagTriv_trans_of_not hTC' ha' hb',
      fun _ => (diagTriv_trans_iff_left hb).mpr ha⟩
  · have ha' := flip1 n12 ha
    have hb' := flip2 n23 hb
    rw [diagTriv_trans_iff_right ha, diagTriv_trans_iff_left hb']
    exact ⟨fun h => absurd h hb, fun h => absurd h ha'⟩
  · have ha' := flip2 n12 ha
    have hb' := flip1 n23 hb
    rw [diagTriv_trans_iff_left hb, diagTriv_trans_iff_right ha']
    exact ⟨fun h => absurd h ha, fun h => absurd h hb'⟩
  · have ha' := flip2 n12 ha
    have hb' := flip2 n23 hb
    exact ⟨fun _ => (diagTriv_trans_iff_left hb').mpr ha',
      fun _ => C5P.diagTriv_trans_of_not hTC ha hb⟩

end CFSG.ClassicalInvolution.Asc77.CX
