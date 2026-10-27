module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoWr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossSetting

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

structure AEData (Q : Type) [Group Q] (Φ : Set (Subgroup Q)) where
  φ : Q →* AEQ 6
  range_eq : φ.range = TwinThinPf8.Hn 6
  ker_le : φ.ker ≤ Subgroup.center Q
  label : ∀ L ∈ Φ, ∃ (β : Finset (Fin 6)) (h : β.card = 4) (b : Bool), L.map φ = memBar β h b
  label_surj : ∀ (β : Finset (Fin 6)) (h : β.card = 4) (b : Bool), ∃ L ∈ Φ, L.map φ = memBar β h b

namespace AEData

variable {Q : Type} [Group Q] {Φ : Set (Subgroup Q)} (D : AEData Q Φ)

@[expose] def Acts (σ : Q → Q) (w : Wr 6) : Prop :=
  ∀ x : Q, D.φ (σ x) = mkQ 6 w * D.φ x * (mkQ 6 w)⁻¹

theorem acts_perm_unique {σ : Q → Q} {w₁ w₂ : Wr 6} (h₁ : D.Acts σ w₁) (h₂ : D.Acts σ w₂) :
    w₁.perm = w₂.perm := by
  have hc : ∀ y ∈ TwinThinPf8.Hn 6, mkQ 6 (w₁⁻¹ * w₂) * y * (mkQ 6 (w₁⁻¹ * w₂))⁻¹ = y := by
    intro y hy
    rw [← D.range_eq] at hy
    obtain ⟨x, rfl⟩ := hy
    have e1 := h₁ x
    have e2 := h₂ x
    rw [e1] at e2
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    calc (mkQ 6 w₁)⁻¹ * mkQ 6 w₂ * D.φ x * ((mkQ 6 w₂)⁻¹ * mkQ 6 w₁)
        = (mkQ 6 w₁)⁻¹ * (mkQ 6 w₂ * D.φ x * (mkQ 6 w₂)⁻¹) * mkQ 6 w₁ := by group
      _ = (mkQ 6 w₁)⁻¹ * (mkQ 6 w₁ * D.φ x * (mkQ 6 w₁)⁻¹) * mkQ 6 w₁ := by rw [e2]
      _ = D.φ x := by group
  have := perm_eq_one_of_centralizes _ hc
  rw [mul_perm, inv_perm, inv_mul_eq_one] at this
  exact this

theorem acts_id : D.Acts id 1 := fun x => by simp

theorem Acts.comp {σ τ : Q → Q} {w₁ w₂ : Wr 6} (h₁ : D.Acts σ w₁) (h₂ : D.Acts τ w₂) :
    D.Acts (σ ∘ τ) (w₁ * w₂) := by
  intro x
  show D.φ (σ (τ x)) = _
  rw [h₁, h₂]
  simp only [map_mul, mul_inv_rev]
  group

theorem center_le_ker : Subgroup.center Q ≤ D.φ.ker := by
  intro z hz
  have hZ : Subgroup.center ↥D.φ.range = ⊥ :=
    TwinThin.center_eq_bot_of_eq D.range_eq (TwinThin.center_Hn (by norm_num))
  have hr : D.φ.rangeRestrict z ∈ Subgroup.center ↥D.φ.range := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := D.φ.rangeRestrict_surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
  rw [hZ, Subgroup.mem_bot] at hr
  rw [MonoidHom.mem_ker]
  have := congrArg Subtype.val hr
  simpa using this

theorem ker_eq_center : D.φ.ker = Subgroup.center Q := le_antisymm D.ker_le D.center_le_ker

theorem ker_invariant (σ : Q ≃* Q) {x : Q} (hx : x ∈ D.φ.ker) : σ x ∈ D.φ.ker := by
  rw [D.ker_eq_center] at hx ⊢
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  have := hx (σ.symm g)
  have h2 := congrArg σ this
  simpa using h2

variable [Finite Q]

theorem exists_wr (σ : Q ≃* Q)
    (hσ : ∀ L ∈ Φ, L.map σ.toMonoidHom ∈ Φ) : ∃ w : Wr 6, D.Acts σ w := by
  let f : Q →* ↥D.φ.range := D.φ.rangeRestrict.comp σ.toMonoidHom
  have hfk : D.φ.ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have : σ x ∈ D.φ.ker := D.ker_invariant σ hx
    rw [MonoidHom.mem_ker] at this
    apply Subtype.ext
    simpa [f] using this
  let σ' : ↥D.φ.range →* ↥D.φ.range :=
    MonoidHom.liftOfRightInverse D.φ.rangeRestrict (Function.surjInv D.φ.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _)
      ⟨f, fun x hx => by
        have hxk : x ∈ D.φ.ker := by
          rw [← MonoidHom.ker_rangeRestrict]
          exact hx
        exact hfk hxk⟩
  have hσ'app : ∀ x : Q, σ' (D.φ.rangeRestrict x) = D.φ.rangeRestrict (σ x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hsurj : Function.Surjective σ' := by
    intro r
    obtain ⟨x, rfl⟩ := D.φ.rangeRestrict_surjective r
    exact ⟨D.φ.rangeRestrict (σ.symm x), by rw [hσ'app]; simp⟩
  have hbij : Function.Bijective σ' := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hperm : TwinThinPf8.PermMembers D.φ.range σ' := by
    intro β hβ cb
    obtain ⟨L, hL, hLlab⟩ := D.label_surj β hβ cb
    obtain ⟨β', hβ', cb', hlab'⟩ := D.label _ (hσ L hL)
    refine ⟨β', hβ', cb', fun x hx => ?_⟩
    have hx' : (x : AEQ 6) ∈ L.map D.φ := by rw [hLlab]; exact hx
    obtain ⟨l, hl, hlx⟩ := hx'
    have hxe : x = D.φ.rangeRestrict l := Subtype.ext hlx.symm
    rw [hxe, hσ'app, ← hlab']
    exact ⟨σ l, ⟨l, hl, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := TwinThin.Cross.aeAut_of_five_le (by norm_num : 5 ≤ 6) D.φ.range D.range_eq σ'
    hbij hperm
  refine ⟨w, fun x => ?_⟩
  have := hw (D.φ.rangeRestrict x)
  rw [hσ'app] at this
  exact this

theorem exists_rho {Γ : Type*} [Group Γ] (α : Γ →* (Q ≃* Q))
    (hα : ∀ g : Γ, ∀ L ∈ Φ, L.map (α g).toMonoidHom ∈ Φ) :
    ∃ ρ : Γ →* Equiv.Perm (Fin 6), ∀ g : Γ,
      ∃ w : Wr 6, w.perm = ρ g ∧ D.Acts (α g) w := by
  choose w hw using fun g : Γ => D.exists_wr (α g) (hα g)
  refine ⟨
    { toFun := fun g => (w g).perm
      map_one' := by
        have h1 : D.Acts (α 1) (1 : Wr 6) := by
          rw [map_one]
          exact D.acts_id
        have := D.acts_perm_unique (hw 1) h1
        rw [one_perm] at this
        exact this
      map_mul' := fun g h => by
        have h1 : D.Acts (α (g * h)) (w g * w h) := by
          rw [map_mul]
          exact (hw g).comp D (hw h)
        have := D.acts_perm_unique (hw (g * h)) h1
        simpa [mul_perm] using this }, fun g => ⟨w g, rfl, hw g⟩⟩

theorem sign_eq_one_of_inner (q₀ : Q) {w : Wr 6} (hw : D.Acts (fun x => q₀ * x * q₀⁻¹) w) :
    Equiv.Perm.sign w.perm = 1 := by
  have hq : D.φ q₀ ∈ TwinThinPf8.Hn 6 := by
    rw [← D.range_eq]
    exact ⟨q₀, rfl⟩
  obtain ⟨a, ha, haq⟩ := hq
  have hAct : D.Acts (fun x => q₀ * x * q₀⁻¹) a := by
    intro x
    rw [map_mul, map_mul, map_inv, ← haq]
  rw [D.acts_perm_unique hw hAct]
  exact ha.2

theorem exists_inner_perm (s : Equiv.Perm (Fin 6)) (hs : Equiv.Perm.sign s = 1) :
    ∃ q₀ : Q, D.Acts (fun x => q₀ * x * q₀⁻¹) (ofPerm s) := by
  have hmem : mkQ 6 (ofPerm s) ∈ D.φ.range := by
    rw [D.range_eq]
    refine ⟨ofPerm s, ⟨?_, ?_⟩, rfl⟩
    · show ∑ i, (0 : Fin 6 → ZMod 2) i = 0
      simp
    · exact hs
  obtain ⟨q₀, hq₀⟩ := hmem
  refine ⟨q₀, fun x => ?_⟩
  rw [map_mul, map_mul, map_inv, hq₀]

end AEData

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
