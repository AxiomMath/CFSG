module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianLayer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup

theorem sp6_lagrangian_full_odd_core_of
    (hD : CFSG.LocalAnalysis.SteinbergBV.DirectSimpleInvolutionCentralizerLayerStmt) :
    Sp6LagrangianFullOddCoreStmt := by
  intro G _ _ hsimple hnonab hKP hG L hL hLn hZ hmodel T hT z hzT hz hH V _ _ _ b hb hnd hV φ e
    he hfull u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂ I₂ F₂ A₁ b₁ I₁ B₁ N₁ D₁ F₁ J J₀ κ₂ lam hκ hlam
  obtain ⟨hκ0, C₁, E₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, ν₂, ε, hν, hsq, hε⟩ :=
    standard_binary_symplectic_six_elementary_lagrangian_next_normalizer hG hL hLn hZ hmodel T hT
      hzT hz hH hb hnd hV φ e he hfull κ₂ lam hκ hlam
  have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂, h13, h14, h15⟩
  have hE : E₂ = sp6E₂ φ he z := (h16 _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE
  have hzC : z ∈ centralizer (L : Set G) := map_subtype_le _ hzT
  refine ⟨hκ0, C₁, sp6E₂ φ he z, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, ν₂, ε, hν, hsq,
    fun hε0 => ?_⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35⟩ := hε hε0
  obtain ⟨hzX, -, hN₂X, ⟨ψ, hψ⟩, hsyl, -⟩ := id g21
  obtain ⟨κ, hκ₁, hκ₂⟩ := id g28
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35,
    sp6_lagrangian_layer_conclusion_of φ he z hD hsimple hnonab hKP hzC hz _ h19 g29 hN₂X g16 g18
      hzX ψ hψ hsyl g24 g26 κ hκ₁ hκ₂⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
