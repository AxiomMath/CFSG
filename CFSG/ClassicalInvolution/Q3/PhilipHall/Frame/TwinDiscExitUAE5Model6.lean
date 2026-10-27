module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent6
public import CFSG.ClassicalInvolution.Q3.TL3T36
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinDisc

namespace AE5

theorem cent_sq {n : ℕ} (hn : n = 5 ∨ n = 6) {α : Finset (Fin n)} (hα : α.card = 4) {x : AEQ n}
    (ht : ∀ a ∈ kList, x * mkQ n (embed (emb α hα) a) = mkQ n (embed (emb α hα) a) * x)
    (hs : ∀ a ∈ kStarList, x * mkQ n (embed (emb α hα) a) = mkQ n (embed (emb α hα) a) * x) :
    x * x = 1 ∨ x * x = zBar α hα := by
  rcases hn with rfl | rfl
  · rcases cent_pair (emb α hα) ht hs with h1 | h1
    · left; rw [h1, mul_one]
    · left
      rw [h1]
      exact zBar_mul_self α hα
  · exact cent_sq6 (emb α hα) ht hs

theorem aut_sq {n : ℕ} (hn : n = 5 ∨ n = 6) (β : MulAut ↥(TL4.aeModel n))
    (hperm : ∀ (γ : Finset (Fin n)) (h : γ.card = 4) (b : Bool),
      ∃ (γ' : Finset (Fin n)) (h' : γ'.card = 4) (b' : Bool),
        ((memBar γ h b).subgroupOf (TL4.aeModel n)).map β.toMonoidHom =
          (memBar γ' h' b').subgroupOf (TL4.aeModel n))
    (α : Finset (Fin n)) (hα : α.card = 4)
    (hfixt : ∀ y (hy : y ∈ memBar α hα true), β ⟨y, memBar_le_aeModel α hα true hy⟩ =
      ⟨y, memBar_le_aeModel α hα true hy⟩)
    (hfixf : ∀ y (hy : y ∈ memBar α hα false), β ⟨y, memBar_le_aeModel α hα false hy⟩ =
      ⟨y, memBar_le_aeModel α hα false hy⟩) :
    (∀ g, β (β g) = g) ∨ ∀ g : ↥(TL4.aeModel n), ((β (β g) : ↥(TL4.aeModel n)) : AEQ n) =
      zBar α hα * g * (zBar α hα)⁻¹ := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn7 : n ≤ 7 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨x, hx⟩ := model117_proved n hn5 hn7 β hperm
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
  have hsq := cent_sq hn hα
    (fun a ha => hcomm _ ⟨embed (emb α hα) a, ⟨a, ha, rfl⟩, rfl⟩)
    (fun a ha => hcomm' _ ⟨embed (emb α hα) a, ⟨a, ha, rfl⟩, rfl⟩)
  have hββ : ∀ g : ↥(TL4.aeModel n), ((β (β g) : ↥(TL4.aeModel n)) : AEQ n) =
      (x * x) * g * (x * x)⁻¹ := by
    intro g
    rw [hx (β g), hx g]
    group
  rcases hsq with h1 | h1
  · left
    intro g
    apply Subtype.ext
    rw [hββ, h1]
    group
  · right
    intro g
    rw [hββ, h1]

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
