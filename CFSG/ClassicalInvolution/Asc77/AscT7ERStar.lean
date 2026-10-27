module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRS
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7ER

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_subset_omegaNbr_of_E4 {K K₁ : Subgroup G} (hs : AscStand p f Ω K)
    {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) (hK₁ : K₁ ∈ Ω) :
    omegaStarNbr Ω K₁ ⊆ omegaNbr Ω K₁ := by
  intro J hJ
  by_contra hnot
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  obtain ⟨W, hW, R, hR, T, hT, hRK, hTJ⟩ :=
    Thompson.exists_W_of_mem_omegaStarNbr hp hq hΩ hK₁ hJ
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hp hq hΩ hW hK₁ hRK hR
  obtain ⟨σ, hσK, hσR⟩ := T7D.exists_rep hp hq hΩ hW hJΩ hTJ hT
  have hc : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hs hW
  have hne : ρ.K ≠ σ.K := by
    rw [hρK, hσK]
    exact fun h => hJ.2.1 h.symm
  have hnot' : σ.K ∉ omegaNbr Ω ρ.K := by
    rw [hρK, hσK]
    exact hnot
  have hncomm := hc.noncomm ρ σ hne hnot'
  obtain ⟨e⟩ := l7_5_2_proved p f hp hq G Ω hΩ W hW W₀ hW₀
  have hab : ∀ a b : ↥(muGroup Ω W), a * b = b * a := fun a b => by
    apply e.injective
    simp only [map_mul]
    exact T7D.muGroup_comm_of_E4 hE4 (e a) (e b)
  exact hncomm (congrArg Subtype.val
    (hab ⟨ρ.img, T7D.rep_img_mem ρ⟩ ⟨σ.img, T7D.rep_img_mem σ⟩))

end T7ER

end CFSG.ClassicalInvolution.Asc77
