module

public import CFSG.ClassicalInvolution.Asc77.AscBSE0
public import CFSG.ClassicalInvolution.Asc77.AscBSE2
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.BSC.BSD
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem false_of_g2_of_aEmpty {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hG2 : C.D.tag b = .G2) (hcard : 3 ≤ C.D.card) (hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M) : False := by
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  obtain ⟨N, m, hinj, hN⟩ := exists_conj_twins hno hb
  obtain ⟨j₀, hj₀, -⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b (by omega : 2 < C.D.card)
  let i₀ : {j : Fin C.D.card // j ≠ b} := ⟨j₀, hj₀b⟩
  let i₁ : {j : Fin C.D.card // j ≠ b} := ⟨e, heb⟩
  have h01 : N i₁ ≠ N i₀ := fun h => hej (congrArg Subtype.val (hinj h))
  obtain ⟨h0tq, h0cl, R₀, hR₀, himg₀, -⟩ := hN i₀
  obtain ⟨h1tq, h1cl, R₁, hR₁, himg₁, -⟩ := hN i₁
  exact g2d4VertexExcl_proved (p := p) (f := f) G (𝒞 K) C.hΩ hA z C.hc2 C.D b (Or.inl hG2)
    (N i₀) (N i₁) m h0tq h1tq h0cl h1cl h01 (himg₀ ▸ Subgroup.map_le_range _ _)
    (himg₁ ▸ Subgroup.map_le_range _ _)

theorem bootNoG2Twin_of_three (h : BootNoG2TwinThree p f) : BootNoG2Twin p f := by
  intro G _ _ _ K z hS D i hG2 hcard
  by_cases h3 : D.card = 3
  · exact h G K z hS D i hG2 h3
  · have hno := noFuzzyFrame hS
    let C := NDB.Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
    have hcard' : 3 < C.D.card := by
      show 3 < D.card
      omega
    exact false_of_g2_of_card (C := C) hno (b := i) (hG2 : C.D.tag i = .G2) hcard'

theorem bootNoG2TwinThree_of_aEmpty (hA : AEmptyG2Twin p f) : BootNoG2TwinThree p f := by
  intro G _ _ _ K z hS D i hG2 hcard
  have hno := noFuzzyFrame hS
  let C := NDB.Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hcard' : 3 ≤ C.D.card := by
    show 3 ≤ D.card
    omega
  exact false_of_g2_of_aEmpty (C := C) hno (b := i) (hG2 : C.D.tag i = .G2) hcard'
    (hA G K z hS D i hG2 hcard)

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
