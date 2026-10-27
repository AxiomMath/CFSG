module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Corr
public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

variable {Y Z : Type} [Group Y] [Group Z]

theorem exists_vertexIso {P : Set (Subgroup Y)} {V : Subgroup Y} {W : Subgroup Z} (A : AEIdent P 8)
    (hspan : pSpan P = V) (hker : A.φ.ker = ⊥) (ρ : ↥((AE.aeSub 8).map (AE.mkQ 8)) ≃* ↥W)
    {P' : Set (Subgroup Z)}
    (hρ₁ : ∀ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool), ∃ J ∈ P',
      ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔ ((ρ x : ↥W) : Z) ∈ J)
    (hρ₂ : ∀ J ∈ P', ∃ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
      ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔ ((ρ x : ↥W) : Z) ∈ J) :
    ∃ ψ : ↥V ≃* ↥W, Carries ψ P P' := by
  have hinj : Function.Injective A.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  let e : ↥V ≃* ↥W := (MulEquiv.subgroupCongr hspan).symm.trans ((MonoidHom.ofInjective hinj).trans
    ((MulEquiv.subgroupCongr A.range_eq).trans ρ))
  have hmem : ∀ g : ↥V, (g : Y) ∈ pSpan P := fun g => hspan ▸ g.2
  let x : ↥V → ↥((AE.aeSub 8).map (AE.mkQ 8)) := fun g =>
    ⟨A.φ ⟨(g : Y), hmem g⟩, by rw [← A.range_eq]; exact ⟨_, rfl⟩⟩
  have hx : ∀ g : ↥V, e g = ρ (x g) := fun g => rfl
  have key : ∀ (J : Subgroup Y) (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
      (J.subgroupOf (pSpan P)).map A.φ = AE.memBar α h b → ∀ g : ↥V,
        (g : Y) ∈ J ↔ (x g : AE.AEQ 8) ∈ AE.memBar α h b := by
    intro J α h b hlab g
    rw [← hlab]
    change _ ↔ A.φ ⟨(g : Y), hmem g⟩ ∈ (J.subgroupOf (pSpan P)).map A.φ
    rw [Subgroup.mem_map_iff_mem hinj]
    exact Iff.rfl
  refine ⟨e, ?_, ?_⟩
  · intro J hJ
    obtain ⟨α, h, b, hlab⟩ := A.label J hJ
    obtain ⟨J', hJ', hρ⟩ := hρ₁ α h b
    refine ⟨J', hJ', fun g => ?_⟩
    rw [key J α h b hlab g, hx g]
    exact hρ (x g)
  · intro J' hJ'
    obtain ⟨α, h, b, hρ⟩ := hρ₂ J' hJ'
    obtain ⟨J, hJ, hlab⟩ := A.label_surj α h b
    refine ⟨J, hJ, fun g => ?_⟩
    rw [key J α h b hlab g, hx g]
    exact hρ (x g)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
