module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

variable {G : Type} [Group G] {E B : Subgroup G}

@[expose] def embB (hBE : B ≤ E) (b : ↥B) : ↥E := ⟨(b : G), hBE b.2⟩

theorem embB_mul (hBE : B ≤ E) (b₁ b₂ : ↥B) :
    embB hBE (b₁ * b₂) = embB hBE b₁ * embB hBE b₂ := rfl

theorem preserves_B (u : MulAut ↥E) (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B) (g : MulAut ↥E)
    (hg : g * u = u * g) : ∀ e : ↥E, (e : G) ∈ B → ((g e : ↥E) : G) ∈ B := by
  intro e he
  have happ : g (u e) = u (g e) := by
    have h := congrArg (fun f : MulAut ↥E => f e) hg
    simpa [MulAut.mul_apply] using h
  have hue : u e = e := (hfix e).mpr he
  have hfixa : u (g e) = g e := by rw [← happ, hue]
  simpa using (hfix (g e)).mp hfixa

noncomputable def resB (hBE : B ≤ E) (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B) (g : MulAut ↥E) (hg : g * u = u * g) :
    MulAut ↥B := by
  have hg' : g⁻¹ * u = u * g⁻¹ := by
    have h := congrArg (fun f : MulAut ↥E => g⁻¹ * f * g⁻¹) hg
    simpa [mul_assoc] using h.symm
  refine MulEquiv.mk'
    { toFun := fun b => ⟨(g (embB hBE b) : G), preserves_B u hfix g hg (embB hBE b) b.2⟩
      invFun := fun b => ⟨(g⁻¹ (embB hBE b) : G), preserves_B u hfix g⁻¹ hg' (embB hBE b) b.2⟩
      left_inv := ?_
      right_inv := ?_ }
    ?_
  · intro b
    apply Subtype.ext
    change ((g⁻¹ (g (embB hBE b)) : ↥E) : G) = (embB hBE b : G)
    have hc : g⁻¹ (g (embB hBE b)) = embB hBE b := by
      have h := congrArg (fun f : MulAut ↥E => f (embB hBE b)) (inv_mul_cancel g)
      simpa [MulAut.mul_apply] using h
    exact congrArg Subtype.val hc
  · intro b
    apply Subtype.ext
    change ((g (g⁻¹ (embB hBE b)) : ↥E) : G) = (embB hBE b : G)
    have hc : g (g⁻¹ (embB hBE b)) = embB hBE b := by
      have h := congrArg (fun f : MulAut ↥E => f (embB hBE b)) (mul_inv_cancel g)
      simpa [MulAut.mul_apply] using h
    exact congrArg Subtype.val hc
  · intro b₁ b₂
    apply Subtype.ext
    change ((g (embB hBE (b₁ * b₂)) : ↥E) : G) =
      (((g (embB hBE b₁)) * (g (embB hBE b₂)) : ↥E) : G)
    rw [embB_mul]
    exact congrArg Subtype.val (map_mul g (embB hBE b₁) (embB hBE b₂))

theorem embB_resB (hBE : B ≤ E) (u : MulAut ↥E) (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (g : MulAut ↥E) (hg : g * u = u * g) (b : ↥B) :
    embB hBE (resB hBE u hfix g hg b) = g (embB hBE b) := by
  rfl

theorem resB_mul (hBE : B ≤ E) (u : MulAut ↥E) (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (g₁ g₂ : MulAut ↥E) (h₁ : g₁ * u = u * g₁) (h₂ : g₂ * u = u * g₂)
    (h₁₂ : (g₁ * g₂) * u = u * (g₁ * g₂)) :
    resB hBE u hfix (g₁ * g₂) h₁₂ = resB hBE u hfix g₁ h₁ * resB hBE u hfix g₂ h₂ := by
  refine MulEquiv.ext (fun b => ?_)
  apply Subtype.ext
  change (((g₁ * g₂) (embB hBE b) : ↥E) : G) = ((g₁ (g₂ (embB hBE b)) : ↥E) : G)
  rw [MulAut.mul_apply]

noncomputable def resHom (hBE : B ≤ E) (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B) (A : Subgroup (MulAut ↥E))
    (hAu : ∀ a ∈ A, a * u = u * a) : ↥A →* MulAut ↥B := by
  exact MonoidHom.mk' (fun a => resB hBE u hfix (a : MulAut ↥E) (hAu a a.2))
    (fun a₁ a₂ => resB_mul hBE u hfix (a₁ : MulAut ↥E) (a₂ : MulAut ↥E)
      (hAu a₁ a₁.2) (hAu a₂ a₂.2) (hAu (a₁ * a₂) (a₁ * a₂).2))

theorem resHom_apply (hBE : B ≤ E) (u : MulAut ↥E) (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A : Subgroup (MulAut ↥E)) (hAu : ∀ a ∈ A, a * u = u * a) (a : ↥A) :
    resHom hBE u hfix A hAu a = resB hBE u hfix (a : MulAut ↥E) (hAu a a.2) := by
  rfl

private theorem resHom_coe (hBE : B ≤ E) (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B) (A : Subgroup (MulAut ↥E))
    (hAu : ∀ a ∈ A, a * u = u * a) (a : ↥A) (b : ↥B) :
    ((resHom hBE u hfix A hAu a) b : G) = ((a : MulAut ↥E) (embB hBE b) : G) := by
  rw [resHom_apply]
  exact congrArg Subtype.val (embB_resB hBE u hfix (a : MulAut ↥E) (hAu a a.2) b)

theorem resHom_injective (hBE : B ≤ E) (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B) (A : Subgroup (MulAut ↥E))
    (hAu : ∀ a ∈ A, a * u = u * a)
    (hAf : ∀ a ∈ A, (∀ e : ↥E, (e : G) ∈ B → a e = e) → a = 1) :
    Function.Injective (resHom hBE u hfix A hAu) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply Subtype.ext
  refine hAf (a : MulAut ↥E) a.2 (fun e he => ?_)
  have hb : (resHom hBE u hfix A hAu a) (⟨(e : G), he⟩ : ↥B) = (⟨(e : G), he⟩ : ↥B) := by
    rw [ha, MulAut.one_apply]
  have hcoe := congrArg Subtype.val hb
  have hemb : embB hBE (⟨(e : G), he⟩ : ↥B) = e := Subtype.ext rfl
  exact Subtype.ext (by simpa [resHom_coe, hemb] using hcoe)

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
