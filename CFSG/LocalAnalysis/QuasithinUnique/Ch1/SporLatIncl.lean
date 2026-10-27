module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

namespace LatCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem Y_le_iff {j jj : ℕ} (hj : j < C.J) (hjj : jj < C.J) :
    C.Y j ≤ C.Y jj ↔ GensIn C.A.act C.Δ C.D j jj := by
  refine ⟨fun h t ht => ?_, C.gensIn_le hj hjj⟩
  have h1 : t ∈ genTabs n (C.gens j) := by rw [C.gens_tabs hj]; exact ht
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h1
  obtain ⟨x, hx, hxe⟩ := (C.Y_mem_iff hjj g).mp (h (C.gens_mem_Y g hg))
  exact ⟨x, hx, hxe.symm⟩

theorem Y_sup_le_iff {j₁ j₂ j : ℕ} (h₁ : j₁ < C.J) (h₂ : j₂ < C.J) (hj : j < C.J) :
    C.Y j₁ ⊔ C.Y j₂ ≤ C.Y j ↔
      GensIn C.A.act C.Δ C.D j₁ j ∧ GensIn C.A.act C.Δ C.D j₂ j := by
  rw [_root_.sup_le_iff, C.Y_le_iff h₁ hj, C.Y_le_iff h₂ hj]

end LatCtx

end CFSG.QuasithinUnique.Ch1.SporLat
