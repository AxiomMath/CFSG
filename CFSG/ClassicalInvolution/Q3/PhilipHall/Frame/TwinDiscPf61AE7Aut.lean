module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Cent
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117
public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinDisc

namespace AE5

theorem aut_sq7 (β : MulAut ↥(TL4.aeModel 7))
    (hperm : ∀ (γ : Finset (Fin 7)) (h : γ.card = 4) (b : Bool),
      ∃ (γ' : Finset (Fin 7)) (h' : γ'.card = 4) (b' : Bool),
        ((memBar γ h b).subgroupOf (TL4.aeModel 7)).map β.toMonoidHom =
          (memBar γ' h' b').subgroupOf (TL4.aeModel 7))
    (hβ4 : ∀ g, β (β (β (β g))) = g)
    (α : Finset (Fin 7)) (hα : α.card = 4)
    (hfixt : ∀ y (hy : y ∈ memBar α hα true), β ⟨y, memBar_le_aeModel α hα true hy⟩ =
      ⟨y, memBar_le_aeModel α hα true hy⟩)
    (hfixf : ∀ y (hy : y ∈ memBar α hα false), β ⟨y, memBar_le_aeModel α hα false hy⟩ =
      ⟨y, memBar_le_aeModel α hα false hy⟩) :
    (∀ g, β (β g) = g) ∨ ∃ p q : Fin 7, p ≠ q ∧ p ∉ α ∧ q ∉ α ∧
      ∀ g : ↥(TL4.aeModel 7), ((β (β g) : ↥(TL4.aeModel 7)) : AEQ 7) =
        vbar 7 (pairVec p q) * g * (vbar 7 (pairVec p q))⁻¹ := by
  obtain ⟨x, hx⟩ := model117_proved 7 (by norm_num) (by norm_num) β hperm
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
  have hx4 : Mdl117.permQ 7 (x * x * (x * x)) = 1 := by
    refine Mdl117.permQ_eq_one_of_comm (by norm_num) (by norm_num) fun γ hγ => ?_
    set g : ↥(TL4.aeModel 7) := ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩ with hg
    have e1 := hx g
    have e2 := hx (β g)
    have e3 := hx (β (β g))
    have e4 := hx (β (β (β g)))
    have h4 := congrArg Subtype.val (hβ4 g)
    rw [e4, e3, e2, e1] at h4
    have key : (x * x * (x * x)) * zBar γ hγ * (x * x * (x * x))⁻¹ = zBar γ hγ := by
      calc (x * x * (x * x)) * zBar γ hγ * (x * x * (x * x))⁻¹
          = x * (x * (x * (x * zBar γ hγ * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ := by group
        _ = zBar γ hγ := h4
    calc (x * x * (x * x)) * zBar γ hγ
        = ((x * x * (x * x)) * zBar γ hγ * (x * x * (x * x))⁻¹) * (x * x * (x * x)) := by group
      _ = zBar γ hγ * (x * x * (x * x)) := by rw [key]
  have hsq := cent_sq7_aux hα
    (fun a ha => hcomm _ ⟨embed (emb α hα) a, ⟨a, ha, rfl⟩, rfl⟩)
    (fun a ha => hcomm' _ ⟨embed (emb α hα) a, ⟨a, ha, rfl⟩, rfl⟩) hx4
  have hββ : ∀ g : ↥(TL4.aeModel 7), ((β (β g) : ↥(TL4.aeModel 7)) : AEQ 7) =
      (x * x) * g * (x * x)⁻¹ := by
    intro g
    rw [hx (β g), hx g]
    group
  rcases hsq with h1 | ⟨p, q, hpq, hpα, hqα, h1⟩
  · left
    intro g
    apply Subtype.ext
    rw [hββ, h1]
    group
  · right
    refine ⟨p, q, hpq, hpα, hqα, fun g => ?_⟩
    rw [hββ, h1]

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
