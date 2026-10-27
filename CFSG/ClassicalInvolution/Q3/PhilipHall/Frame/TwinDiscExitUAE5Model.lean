module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117
public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinDisc

namespace AE5

theorem aut_dichotomy (β : MulAut ↥(TL4.aeModel 5))
    (hperm : ∀ (γ : Finset (Fin 5)) (h : γ.card = 4) (b : Bool),
      ∃ (γ' : Finset (Fin 5)) (h' : γ'.card = 4) (b' : Bool),
        ((memBar γ h b).subgroupOf (TL4.aeModel 5)).map β.toMonoidHom =
          (memBar γ' h' b').subgroupOf (TL4.aeModel 5))
    (α : Finset (Fin 5)) (hα : α.card = 4)
    (hfixt : ∀ y (hy : y ∈ memBar α hα true), β ⟨y, memBar_le_aeModel α hα true hy⟩ =
      ⟨y, memBar_le_aeModel α hα true hy⟩)
    (hfixf : ∀ y (hy : y ∈ memBar α hα false), β ⟨y, memBar_le_aeModel α hα false hy⟩ =
      ⟨y, memBar_le_aeModel α hα false hy⟩) :
    β = 1 ∨ ∀ g : ↥(TL4.aeModel 5), ((β g : ↥(TL4.aeModel 5)) : AEQ 5) =
      zBar α hα * g * (zBar α hα)⁻¹ := by
  obtain ⟨x, hx⟩ := model117_proved 5 le_rfl (by norm_num) β hperm
  have hc : ∀ y ∈ memBar α hα true, x * y * x⁻¹ = y := fun y hy => by
    have := hfixt y hy
    have h2 := hx ⟨y, memBar_le_aeModel α hα true hy⟩
    rw [this] at h2
    exact h2.symm
  have hc' : ∀ y ∈ memBar α hα false, x * y * x⁻¹ = y := fun y hy => by
    have := hfixf y hy
    have h2 := hx ⟨y, memBar_le_aeModel α hα false hy⟩
    rw [this] at h2
    exact h2.symm
  have hcomm : ∀ y ∈ memBar α hα true, x * y = y * x := fun y hy => by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hc y hy]
  have hcomm' : ∀ y ∈ memBar α hα false, x * y = y * x := fun y hy => by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hc' y hy]
  rcases cent_pair (emb α hα)
    (fun a ha => hcomm _ ⟨embed (emb α hα) a, ⟨a, ha, rfl⟩, rfl⟩)
    (fun a ha => hcomm' _ ⟨embed (emb α hα) a, ⟨a, ha, rfl⟩, rfl⟩) with h1 | h1
  · left
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.one_apply]
    have := hx g
    rw [h1] at this
    simpa using this
  · right
    intro g
    rw [hx g, h1]
    rfl

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
