module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.FixedSpaceDim
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TailTrivialThree

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem fixed_space_dim_of_perfect (h : UnitaryFieldData 2 1 K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBs : B.SeparatingLeft)
    {s : ℕ} (hs : 1 ≤ s) {W : ℕ → Submodule K V} (hW0 : W 0 = ⊥)
    (hmono : ∀ j, W j ≤ W (j + 1))
    (hWiso : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, ∀ w ∈ W j, B v w = 0)
    (Δ : Subgroup (LinearMap.GeneralLinearGroup K V)) (hperf : ⁅Δ, Δ⁆ = Δ)
    (hΔiso : ∀ d ∈ Δ, ∀ v w, B ((d : Module.End K V) v) ((d : Module.End K V) w) = B v w)
    (hΔst : ∀ d ∈ Δ, ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (d : Module.End K V) v ∈ W j)
    {x : LinearMap.GeneralLinearGroup K V} (hxΔ : x ∈ Δ) (hx : x ^ 3 = 1)
    {j₀ : ℕ} (hj₀ : 1 ≤ j₀) (hj₀s : j₀ ≤ s)
    (hdim : finrank K (PieceQ (W (j₀ - 1)) (W j₀)) = 2)
    (hline : ∀ j, 1 ≤ j → j ≤ s → j ≠ j₀ → finrank K (PieceQ (W (j - 1)) (W j)) = 1)
    (htail : finrank K (PieceQ (W s) ((W s).orthogonalBilin B)) ≤ 3) :
    finrank K V - 4 ≤ finrank K (LinearMap.ker ((x : Module.End K V) - 1)) := by
  have := h.charP
  have hW : ∀ d ∈ Δ, ∀ a, a ≤ s → ∀ v ∈ W a, (d : Module.End K V) v ∈ W a := by
    intro d hd a ha v hv
    rcases Nat.eq_zero_or_pos a with rfl | h0
    · rw [hW0, Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact hΔst d hd a h0 ha v hv
  refine fixed_space_dim (fun c => ⟨h.bar c, h.bar_bar c⟩) hBs hs hW0 hmono hWiso hx
    (hΔiso x hxΔ) (hΔst x hxΔ) hj₀ hj₀s ?_ ?_ ?_
  · have := finrank_pieceQ_add (hmono (j₀ - 1))
    rw [show j₀ - 1 + 1 = j₀ by omega] at this
    omega
  · intro j hj1 hjs hne v hv
    exact perfect_trivial_on_line_piece (hline j hj1 hjs hne) Δ hperf
      (fun d hd => hW d hd (j - 1) (by omega)) (fun d hd => hW d hd j hjs) x hxΔ v hv
  · intro v hv
    exact isometry_perfect_trivial_on_tail' h hB hBs (hWiso s hs le_rfl) htail Δ
      (fun d hd => ⟨hΔiso d hd, hW d hd s le_rfl⟩) hperf x hxΔ v
      (Submodule.mem_orthogonalBilin.mpr hv)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
