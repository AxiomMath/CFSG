module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X16
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YM01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YO01
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section


set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Asc77.CX (TwinGroup DiagTriv DiagRel TwinIso centTG fixSubgroup twinIso_of_compat)

section Swap

variable {K₀ K₀' : Type} [Group K₀] [Group K₀']

@[expose] def twinSwap (L : TwinGroup K₀ K₀') : TwinGroup K₀' K₀ where
  X := L.X
  instGroup := L.instGroup
  instFinite := L.instFinite
  A := L.A'
  A' := L.A
  ι := L.ι'
  ι' := L.ι

end Swap


section Lift

variable {K₀ K₀' : Type} [Group K₀] [Group K₀']

theorem isOm5_twinSwap {L : TwinGroup K₀ K₀'}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 L) :
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (twinSwap L) := by
  obtain ⟨Φ, z', a₀, b₀, hd⟩ := h
  refine ⟨Φ, z', b₀, a₀, ⟨hd.lie, ?_, hd.conj⟩⟩
  have t := hd.twin
  exact ⟨t.hA', t.hA, t.ne.symm, t.hzA', t.hzA, t.hb₀, t.ha₀, t.hb₀sq, t.ha₀sq, t.nbA', t.nbA⟩

theorem cq_abstract (hom5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om5StabDiag)
    (hcent5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C25W.Cent5) (L : TwinGroup K₀ K₀')
    (h5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 L) (eA : K₀ ≃* SL(2, ZMod 3))
    {c : L.X} (hnorm : ∀ a ∈ L.A, c * a * c⁻¹ ∈ L.A) (hc' : ∀ a ∈ L.A', c * a = a * c)
    (hAA' : ∀ a ∈ L.A, ∀ a' ∈ L.A', a * a' = a' * a) : c ∈ L.A := by
  classical
  obtain ⟨Φ₂, z₂, a₂, b₂, hd⟩ := h5
  have hsimple : IsSimpleGroup L.X :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.isSimpleGroup_of_om5Data hd
  have hcenter : Subgroup.center L.X = ⊥ := by
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L.X) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ x y : L.X, x * y = y * x := fun x y => by
        have : x ∈ Subgroup.center L.X := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.mp this y).symm
      apply CFSG.ClassicalInvolution.Q3.sl2Three_not_comm
      intro a b
      have h1 := hcomm (L.ι (eA.symm a) : L.X) (L.ι (eA.symm b) : L.X)
      have h2 : L.ι (eA.symm a * eA.symm b) = L.ι (eA.symm b * eA.symm a) := by
        rw [map_mul, map_mul]
        exact Subtype.ext h1
      have h3 := L.ι.injective h2
      rw [← map_mul, ← map_mul] at h3
      exact eA.symm.injective h3
  have central : ∀ c' : L.X, (∀ y : L.X, c' * y * c'⁻¹ = y) → c' = 1 := by
    intro c' hc'
    have : c' ∈ Subgroup.center L.X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := hc' y
      calc y * c' = (c' * y * c'⁻¹) * c' := by rw [this]
        _ = c' * y := by group
    rwa [hcenter, Subgroup.mem_bot] at this
  set s : L.X ≃* L.X := MulAut.conj c with hs
  have hle : L.A.map (s : L.X →* L.X) ≤ L.A := by
    rintro _ ⟨a, ha, rfl⟩
    exact hnorm a ha
  have hAmap : L.A.map (s : L.X →* L.X) = L.A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective s.injective])
  have hsfix : ∀ a ∈ L.A', s a = a := fun a ha => by
    rw [hs, MulAut.conj_apply, hc' a ha]
    group
  have hA'map : L.A'.map (s : L.X →* L.X) = L.A' := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      show s a ∈ L.A'
      rw [hsfix a ha]
      exact ha
    · intro hy
      exact ⟨y, hy, hsfix y hy⟩
  have hrestr' : TwinGroup.restr' s hA'map = MulEquiv.refl K₀' := by
    ext k
    apply L.ι'.injective
    apply Subtype.ext
    rw [TwinGroup.restr'_apply]
    exact hsfix _ (L.ι' k).2
  have hdt' : DiagTriv 3 (TwinGroup.restr' s hA'map) := by
    rw [hrestr']
    intro u _
    exact ⟨1, by simp⟩
  have hdt : DiagTriv 3 (TwinGroup.restr s hAmap) :=
    (hom5 K₀ K₀' L ⟨Φ₂, z₂, a₂, b₂, hd⟩ s hAmap hA'map).mpr hdt'
  obtain ⟨g, hg⟩ := diagTriv_inner_of_equiv eA (TwinGroup.restr s hAmap) hdt
  set a : L.X := (L.ι g : L.X) with ha
  have haA : a ∈ L.A := (L.ι g).2
  have hconj : ∀ x ∈ L.A, c * x * c⁻¹ = a * x * a⁻¹ := by
    intro x hx
    obtain ⟨k, hk⟩ := L.ι.surjective ⟨x, hx⟩
    have e1 : ((L.ι (TwinGroup.restr s hAmap k) : L.A) : L.X) = s (L.ι k : L.X) :=
      TwinGroup.restr_apply s hAmap k
    rw [hg k, map_mul, map_mul, map_inv] at e1
    rw [hk] at e1
    simpa [hs, MulAut.conj_apply, ha] using e1.symm
  set c' : L.X := a⁻¹ * c with hc'def
  have hcA : ∀ x ∈ L.A, c' * x * c'⁻¹ = x := by
    intro x hx
    have := hconj x hx
    calc c' * x * c'⁻¹ = a⁻¹ * (c * x * c⁻¹) * a := by rw [hc'def]; group
      _ = x := by rw [this]; group
  have hcA' : ∀ x ∈ L.A', c' * x * c'⁻¹ = x := by
    intro x hx
    have h1 : c * x * c⁻¹ = x := by rw [hc' x hx]; group
    have h2 : a * x = x * a := hAA' a haA x hx
    calc c' * x * c'⁻¹ = a⁻¹ * (c * x * c⁻¹) * a := by rw [hc'def]; group
      _ = a⁻¹ * x * a := by rw [h1]
      _ = x := by
        calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
          _ = a⁻¹ * (a * x) := by rw [h2]
          _ = x := by group
  obtain ⟨D, hD1, i, hi⟩ := hd.lie
  have hfixA : ∀ x ∈ L.A, (MulAut.conj c' : L.X ≃* L.X) x = x := fun x hx => by
    rw [MulAut.conj_apply]; exact hcA x hx
  have hfixA' : ∀ x ∈ L.A', (MulAut.conj c' : L.X ≃* L.X) x = x := fun x hx => by
    rw [MulAut.conj_apply]; exact hcA' x hx
  have hmem : c = a * c' := by rw [hc'def]; group
  rcases hcent5 L.X Φ₂ D L.A L.A' z₂ a₂ b₂ hD1 ⟨i, hi⟩ hd.twin (MulAut.conj c') hfixA hfixA' with h | h
  · have h1 : c' = 1 := central c' fun y => by
      have := congrArg (fun φ : L.X ≃* L.X => φ y) h
      simpa [MulAut.conj_apply] using this
    rw [hmem, h1, mul_one]
    exact haA
  · have hz₂ : z₂ ∈ L.A := hd.twin.hzA.mem
    have h1 : z₂⁻¹ * c' = 1 := central _ fun y => by
      have := h y
      rw [MulAut.conj_apply] at this
      calc z₂⁻¹ * c' * y * (z₂⁻¹ * c')⁻¹ = z₂⁻¹ * (c' * y * c'⁻¹) * z₂ := by group
        _ = y := by rw [this]; group
    have h2 : c' = z₂ := by
      calc c' = z₂ * (z₂⁻¹ * c') := by group
        _ = z₂ := by rw [h1, mul_one]
    rw [hmem, h2]
    exact L.A.mul_mem haA hz₂

end Lift

section Face

variable {K₁ K₁' K₂ K₂' : Type} [Group K₁] [Group K₁'] [Group K₂] [Group K₂']

@[expose] def restrTo (L₁ : TwinGroup K₁ K₁') (L₂ : TwinGroup K₂ K₂') (φ : L₁.X ≃* L₂.X)
    (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A) : K₁ ≃* K₂ :=
  L₁.ι.trans ((φ.subgroupMap L₁.A).trans ((MulEquiv.subgroupCongr hA).trans L₂.ι.symm))

@[expose] def restrTo' (L₁ : TwinGroup K₁ K₁') (L₂ : TwinGroup K₂ K₂') (φ : L₁.X ≃* L₂.X)
    (hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A') : K₁' ≃* K₂' :=
  L₁.ι'.trans ((φ.subgroupMap L₁.A').trans ((MulEquiv.subgroupCongr hA').trans L₂.ι'.symm))

theorem restrTo_apply (L₁ : TwinGroup K₁ K₁') (L₂ : TwinGroup K₂ K₂') (φ : L₁.X ≃* L₂.X)
    (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A) (k : K₁) :
    ((L₂.ι (restrTo L₁ L₂ φ hA k) : L₂.A) : L₂.X) = φ (L₁.ι k : L₁.X) := by
  simp only [restrTo, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem restrTo'_apply (L₁ : TwinGroup K₁ K₁') (L₂ : TwinGroup K₂ K₂') (φ : L₁.X ≃* L₂.X)
    (hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A') (k : K₁') :
    ((L₂.ι' (restrTo' L₁ L₂ φ hA' k) : L₂.A') : L₂.X) = φ (L₁.ι' k : L₁.X) := by
  simp only [restrTo', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

end Face

section FaceAbstract

theorem false_of_face_abstract (h1 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.DiagThree)
    {K₀ K₀' K₂ K₂' K₃ K₃' : Type} [Group K₀] [Group K₀'] [Group K₂] [Group K₂'] [Group K₃] [Group K₃']
    (L₁₂ L₁₃ : TwinGroup K₀ K₀') (L₂₁ L₂₃ : TwinGroup K₂ K₂') (L₃₁ L₃₂ : TwinGroup K₃ K₃')
    (h5₁₂ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 L₁₂)
    (h5₁₃ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 L₁₃)
    (h5₂₃ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 L₂₃)
    (n₁ : ¬ DiagRel 3 L₁₂ L₁₃) (n₂ : ¬ DiagRel 3 L₂₁ L₂₃) (n₃ : ¬ DiagRel 3 L₃₁ L₃₂)
    (ψ₁₂ : L₁₂.X ≃* L₂₁.X) (hA₁₂ : L₁₂.A.map (ψ₁₂ : L₁₂.X →* L₂₁.X) = L₂₁.A)
    (hA'₁₂ : L₁₂.A'.map (ψ₁₂ : L₁₂.X →* L₂₁.X) = L₂₁.A')
    (ψ₁₃ : L₁₃.X ≃* L₃₁.X) (hA₁₃ : L₁₃.A.map (ψ₁₃ : L₁₃.X →* L₃₁.X) = L₃₁.A)
    (hA'₁₃ : L₁₃.A'.map (ψ₁₃ : L₁₃.X →* L₃₁.X) = L₃₁.A')
    (ψ₂₃ : L₂₃.X ≃* L₃₂.X) (hA₂₃ : L₂₃.A.map (ψ₂₃ : L₂₃.X →* L₃₂.X) = L₃₂.A)
    (hA'₂₃ : L₂₃.A'.map (ψ₂₃ : L₂₃.X →* L₃₂.X) = L₃₂.A')
    (cocycle : ∀ k : K₀, restrTo L₂₃ L₃₂ ψ₂₃ hA₂₃ (restrTo L₁₂ L₂₁ ψ₁₂ hA₁₂ k) =
      restrTo L₁₃ L₃₁ ψ₁₃ hA₁₃ k)
    (cocycle' : ∀ k : K₀', restrTo' L₂₃ L₃₂ ψ₂₃ hA'₂₃ (restrTo' L₁₂ L₂₁ ψ₁₂ hA'₁₂ k) =
      restrTo' L₁₃ L₃₁ ψ₁₃ hA'₁₃ k) : False := by
  classical
  set κ₂ := restrTo L₁₂ L₂₁ ψ₁₂ hA₁₂ with hκ₂
  set κ₂' := restrTo' L₁₂ L₂₁ ψ₁₂ hA'₁₂ with hκ₂'
  set κ₃ := restrTo L₁₃ L₃₁ ψ₁₃ hA₁₃ with hκ₃
  set κ₃' := restrTo' L₁₃ L₃₁ ψ₁₃ hA'₁₃ with hκ₃'
  have I₁₂ : TwinIso 3 L₁₂ (L₂₁.rebase κ₂ κ₂') :=
    twinIso_of_compat ψ₁₂ (fun k => (restrTo_apply L₁₂ L₂₁ ψ₁₂ hA₁₂ k).symm)
      (fun k => (restrTo'_apply L₁₂ L₂₁ ψ₁₂ hA'₁₂ k).symm)
  have I₁₃ : TwinIso 3 L₁₃ (L₃₁.rebase κ₃ κ₃') :=
    twinIso_of_compat ψ₁₃ (fun k => (restrTo_apply L₁₃ L₃₁ ψ₁₃ hA₁₃ k).symm)
      (fun k => (restrTo'_apply L₁₃ L₃₁ ψ₁₃ hA'₁₃ k).symm)
  have I₂₃ : TwinIso 3 (L₂₃.rebase κ₂ κ₂') (L₃₂.rebase κ₃ κ₃') := by
    refine twinIso_of_compat ψ₂₃ (fun k => ?_) (fun k => ?_)
    · have := restrTo_apply L₂₃ L₃₂ ψ₂₃ hA₂₃ (κ₂ k)
      rw [cocycle k] at this
      exact this.symm
    · have := restrTo'_apply L₂₃ L₃₂ ψ₂₃ hA'₂₃ (κ₂' k)
      rw [cocycle' k] at this
      exact this.symm
  rcases h1 K₀ K₀' L₁₂ L₁₃ (L₂₃.rebase κ₂ κ₂') h5₁₂ h5₁₃
    ((CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.isOm5_rebase_iff L₂₃ κ₂ κ₂').mpr h5₂₃) with d | d | d
  · exact n₁ d
  · exact n₂ ((CFSG.ClassicalInvolution.Asc77.CX.diagRel_rebase_iff κ₂ κ₂').mp
      (I₁₂.symm.trans_diagRel d))
  · exact n₃ ((CFSG.ClassicalInvolution.Asc77.CX.diagRel_rebase_iff κ₃ κ₃').mp
      (I₁₃.symm.trans_diagRel (d.trans_twinIso I₂₃)))

end FaceAbstract

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
