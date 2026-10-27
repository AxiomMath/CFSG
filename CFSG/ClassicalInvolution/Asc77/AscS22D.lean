module

public import CFSG.ClassicalInvolution.Asc77.AscS22CB
import CFSG.ClassicalInvolution.Asc77.AscT7OZ
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_2S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      Big Ω K →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) →
          IsElemAbelian2 A 2 →
            alphaOf A = alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G))

end Statement

section Hyp51u

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hyp51u_of_four (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (hK₄K : K₄ ≠ K) (hK₄K' : K₄ ≠ K') (hK₄K₃ : K₄ ≠ K₃) :
    ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
      Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c := by
  intro c hc hc1 hcz
  obtain ⟨R, R', R₃, hT⟩ := T7J.exists_triple h
  have hq : 5 ≤ p ^ f := h.stand.five
  have hp : p ≠ 2 := h.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hBelow : CITBelowU p f (Nat.card G) := h.stand.below f hq
  have hA : ∀ M ∈ Ω, AEmpty Ω M := h.stand.aEmpty
  have hex : G2D4VertexExcl p f := g2d4VertexExcl_proved
  have hres : TwinSqAlphaRows p := twinSqAlphaRows_proved p
  have hK₄u : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet h.hz hK₄
  have cm := hT.cm
  have hcm := T7J.mem_closure_three cm.commute_xz cm.commute_xw cm.commute_wz.symm cm.sq_pair
    cm.z2 cm.rot.sq_pair hc
  rcases hcm with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hc1
  · exact hT.hyp51At hp hq hΩ hBelow hA hex hres (Or.inl h2) hc1 hcz hK₄.1 hK₄u hK₄K hK₄K'
      hK₄K₃
  · exact absurd h3 hcz
  · exact hT.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inl h4) hc1 hcz hK₄.1 hK₄u hK₄K'
      hK₄K₃ hK₄K
  · exact hT.hyp51At hp hq hΩ hBelow hA hex hres (Or.inr h5) hc1 hcz hK₄.1 hK₄u hK₄K hK₄K'
      hK₄K₃
  · exact hT.rot.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inr (h6.trans cm.eq_xw)) hc1 hcz
      hK₄.1 hK₄u hK₄K₃ hK₄K hK₄K'
  · exact hT.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inr (h7.trans cm.zc₂₃)) hc1 hcz
      hK₄.1 hK₄u hK₄K' hK₄K₃ hK₄K
  · exact hT.rot.rot.hyp51At hp hq hΩ hBelow hA hex hres (Or.inl (h8.trans cm.eq_xyw)) hc1 hcz
      hK₄.1 hK₄u hK₄K₃ hK₄K hK₄K'

end Hyp51u

section C22

variable (p f : ℕ) [Fact p.Prime]

theorem c22_2S : C22_2S p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hb
  obtain ⟨K₄, hK₄, h1, h2, h3⟩ := hb.fourth K K' K₃
  have hB : Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    refine ⟨Hyp22Setting.isElemAbelian_B h, natCard_B h, fun c hc hc1 => ?_⟩
    by_cases hcz : c = z
    · rw [hcz]
      exact hyp22Hyp51z p f G Ω K K' K₃ z u₁ u₂ u₃ h
    · exact hyp51u_of_four h hK₄ h1 h2 h3 c hc hc1 hcz
  exact lemma54_odd_and_eq hB (closure_12_le h) (isElemAbelian2_closure h)

end C22

section Alpha

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem alpha_23 (h2 : C22_2S p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (closure_23_le h) (isElemAbelian2_closure_23 h)

theorem alpha_13 (h2 : C22_2S p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (closure_13_le h) (isElemAbelian2_closure_13 h)

theorem oddCore_le_normalizer_alpha (h2 : C22_2S p f)
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha (Hyp22Setting.isElemAbelian_B h) (natCard_B h)
    (B_le_centralizer h) (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2

theorem third_le_normalizer_alpha (h2 : C22_2S p f)
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro ℓ hℓ
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem h.hzK₃ hℓ).symm
  have hzt : z * (u₁ * u₂) = (u₁ * u₂) * z :=
    (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_z₁.symm
  have hsub := T7A.isSubnormal_centralizer hΩ hK₃Ω h.hzK₃
  have hc₁ : ⁅u₁, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK hK₃Ω h.hK₃K.symm h.hz h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₁.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hc₂ : ⁅u₂, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK' hK₃Ω h.hK₃K'.symm h.hzK' h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₂.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hN := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hu₁C
  have hcomm : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have e : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ = (u₁ * ⁅u₂, ℓ⁆ * u₁⁻¹) * ⁅u₁, ℓ⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN _).mp hc₂) hc₁
  exact T7B.mem_normalizer_alphaOf_of_commutator h.sq_12 hzt hℓC hcomm
    (oddCore_le_normalizer_alpha h2 h hb)

theorem le_normalizer_alpha (h2 : C22_2S p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hb : Big Ω K) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, third_le_normalizer_alpha h2 h hb⟩
  · have := third_le_normalizer_alpha h2 (rotate h) (hb.of_twin h.hz h.hK')
    rwa [alpha_23 h2 h hb] at this
  · have := third_le_normalizer_alpha h2 (rotate (rotate h)) (hb.of_twin h.hz h.hK₃)
    rwa [← T7J.comm₁₃ h, alpha_13 h2 h hb] at this

theorem twin_le_normalizer_alpha (h2 : C22_2S p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hb : Big Ω K) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  by_cases hLK : L = K
  · rw [hLK]
    exact (le_normalizer_alpha h2 h hb).1
  by_cases hLK' : L = K'
  · rw [hLK']
    exact (le_normalizer_alpha h2 h hb).2.1
  obtain ⟨w, hw⟩ := exists_replace_third h hL hLK hLK'
  exact third_le_normalizer_alpha h2 hw hb

end Alpha

end S22

end CFSG.ClassicalInvolution.Asc77
