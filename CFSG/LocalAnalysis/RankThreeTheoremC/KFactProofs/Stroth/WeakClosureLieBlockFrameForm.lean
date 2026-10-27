module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame
public import CFSG.GroupTheory.WeirSylow.FormSpace

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow

section FormSpace

variable {K : Type} [Field K] {R : Type} [AddCommMonoid R]

private def formPermHom (S₀ : FormSpace K R) (r : ℕ) :
    Equiv.Perm (Fin r) →* (FormSpace.pi fun _ : Fin r => S₀).isom where
  toFun σ := ⟨LinearEquiv.funCongrLeft K S₀.V σ⁻¹, fun x y =>
    Equiv.sum_comp σ⁻¹ (fun i => S₀.F (x i) (y i))⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun v => funext fun i => rfl)
  map_mul' σ τ := Subtype.ext (LinearEquiv.ext fun v => funext fun i => by
    change v ((σ * τ)⁻¹ i) = v (τ⁻¹ (σ⁻¹ i))
    rw [mul_inv_rev, Equiv.Perm.mul_apply])

private def formTorusHom {C : Type} [Group C] (S₀ : FormSpace K R) (ρ : C →* S₀.isom) (r : ℕ) :
    (Fin r → C) →* (FormSpace.pi fun _ : Fin r => S₀).isom :=
  (piIsometryHom K (fun _ : Fin r => S₀.F)).comp (MonoidHom.piMap fun _ => ρ)

private theorem formTorusHom_injective {C : Type} [Group C] (S₀ : FormSpace K R)
    {ρ : C →* S₀.isom} (hρ : Function.Injective ρ) (r : ℕ) :
    Function.Injective (formTorusHom S₀ ρ r) := by
  have h1 : Function.Injective (piIsometryHom K (fun _ : Fin r => S₀.F)) :=
    piIsometryHom_injective K _
  have h2 : Function.Injective (MonoidHom.piMap fun _ : Fin r => ρ) := by
    intro a b h
    funext i
    exact hρ (congrFun h i)
  exact h1.comp h2

theorem nonempty_blockFrame_pi (S₀ : FormSpace K R) {C : Type} [CommGroup C]
    (ρ : C →* S₀.isom) (hρ : Function.Injective ρ) (J₀ : S₀.isom)
    (hJ : ∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹) (r : ℕ) :
    Nonempty (BlockFrame C r (FormSpace.pi fun _ : Fin r => S₀).isom) := by
  have hJc : ∀ (c : C) (w : S₀.V), J₀.1 ((ρ c).1 w) = (ρ c⁻¹).1 (J₀.1 w) := by
    intro c w
    have h2 : J₀ * ρ c = ρ c⁻¹ * J₀ := by
      rw [← hJ c, inv_mul_cancel_right]
    exact congrArg (fun φ : S₀.isom => (φ : S₀.V ≃ₗ[K] S₀.V) w) h2
  have hS_conj : ∀ (σ : Equiv.Perm (Fin r)) (c : Fin r → C),
      formPermHom S₀ r σ * formTorusHom S₀ ρ r c * (formPermHom S₀ r σ)⁻¹ =
        formTorusHom S₀ ρ r (c ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin r))) := by
    intro σ c
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (LinearEquiv.ext fun v => funext fun j => rfl)
  have hexists : ∀ i : Fin r, ∃ g : (FormSpace.pi fun _ : Fin r => S₀).isom,
      ∀ c : Fin r → C, g * formTorusHom S₀ ρ r c * g⁻¹ =
        formTorusHom S₀ ρ r (Function.update c i (c i)⁻¹) := by
    intro i
    refine ⟨piIsometryHom K (fun _ : Fin r => S₀.F) (Pi.mulSingle i J₀), fun c => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    refine Subtype.ext (LinearEquiv.ext fun v => funext fun j => ?_)
    change ((Pi.mulSingle i J₀ : Fin r → S₀.isom) j).1 ((ρ (c j)).1 (v j)) =
      (ρ (Function.update c i (c i)⁻¹ j)).1
        (((Pi.mulSingle i J₀ : Fin r → S₀.isom) j).1 (v j))
    by_cases hji : j = i
    · subst hji
      simp only [Pi.mulSingle_eq_same, Function.update_self]
      exact hJc _ _
    · simp only [Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]
      rfl
  exact ⟨{ T := formTorusHom S₀ ρ r
           S := formPermHom S₀ r
           T_injective := formTorusHom_injective S₀ hρ r
           S_conj := hS_conj
           exists_inv := hexists }⟩

private def formProdHom (S T₀ : FormSpace K R) : S.isom →* (FormSpace.prod S T₀).isom :=
  (prodIsometryHom K S.F T₀.F).comp ((MonoidHom.id S.isom).prod (1 : S.isom →* T₀.isom))

theorem nonempty_blockFrame_prod (S T₀ : FormSpace K R) {C : Type} [Group C] {r : ℕ}
    (F : BlockFrame C r S.isom) : Nonempty (BlockFrame C r (FormSpace.prod S T₀).isom) := by
  have hinj : Function.Injective ((formProdHom S T₀).comp F.T) := by
    intro c d hcd
    exact F.T_injective (congrArg Prod.fst (prodIsometryHom_injective K S.F T₀.F hcd))
  exact ⟨F.map (formProdHom S T₀) hinj⟩

end FormSpace

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
