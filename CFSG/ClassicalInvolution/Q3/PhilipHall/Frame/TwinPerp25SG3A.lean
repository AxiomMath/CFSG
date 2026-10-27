module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf81Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUConnE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfIdent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M7

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Gen

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem transitive_of_twin_nbr_pair (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A)
    (hpair : (∀ M ∈ Φ, M = A ∨ M = A') → False) :
    ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  have h4' := h4 X hlt Φ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcA : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A = M) → M = A' := by
    intro M hM hnot
    have hMA : M ≠ A := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A hA M hM hnot))
  have hcA' : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A' = M) → M = A := by
    intro M hM hnot
    have hMA : M ≠ A' := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb' M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A' hA' M hM hnot))
  have hAA' : ∃ g : X, conjSub g A = A' := by
    by_contra hnot
    apply hpair
    intro M hM
    by_cases hM1 : ∃ g : X, conjSub g A = M
    · left
      obtain ⟨g, hg⟩ := hM1
      refine hcA' M hM ?_
      rintro ⟨g', hg'⟩
      exact hnot ⟨g'⁻¹ * g, by rw [conjSub_mul, hg, ← hg', conjSub_inv_conjSub]⟩
    · right
      exact hcA M hM hM1
  have hcl : ∀ M ∈ Φ, ∃ g : X, conjSub g A = M := by
    intro M hM
    by_cases h : ∃ g : X, conjSub g A = M
    · exact h
    · obtain ⟨g, hg⟩ := hAA'
      exact ⟨g, hg.trans (hcA M hM h).symm⟩
  intro K hK L hL
  obtain ⟨x, hx⟩ := hcl K hK
  obtain ⟨y, hy⟩ := hcl L hL
  exact ⟨y * x⁻¹, by rw [conjSub_mul, ← hx, conjSub_inv_conjSub, hy]⟩

end Gen

section Layer

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem layer_transitive_of_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hbad : BadElt z a) :
    ∀ M ∈ TwinDisc.secFam Ω a, ∀ N ∈ TwinDisc.secFam Ω a,
      ∃ x : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a), conjSub x M = N := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨hKtq, hK'tq, hz, hz', hperp₁, hperp₂⟩ := layer_twins_tq hyp hacA
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  have h4 := hT (Nat.card G) hih.1 hih.2
  obtain ⟨htC₁, htY₁, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
  refine transitive_of_twin_nbr_pair h4 hlt hS (secImg_mem_secFam hKtq)
    (secImg_mem_secFam hK'tq) ?_ ?_ ?_
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hKtq hJ₀ hperp₁ hMn
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK'tq hJ₀ hperp₂ hMn
  · intro hall
    apply hbad
    refine TwinPerpV3.mem_zStarOf_of_allMembers hΩ hc2 hKtq htC₁ htY₁ ?_
    intro M hM
    rcases hall M hM with rfl | rfl
    · exact hz₁
    · exact hz₂

theorem layer_edge (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (hacA : a ∈ cA S R R') :
    ∃ M ∈ TwinDisc.secFam Ω a, ∃ N, N ∈ omegaNbr (TwinDisc.secFam Ω a) M := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨hKtq, hK'tq, hz, hz', -, -⟩ := layer_twins_tq hyp hacA
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hKΩ : K ∈ Ω := hyp.std.1.stand.mem
  have hK'Ω : K' ∈ Ω := hyp.std.1.hK'.1
  have hRK : IsSylow2In R K := h.hRsyl
  have hR'K' : IsSylow2In R' K' := h.hR'syl
  have hcommR : Commutes R R' := h.hcomm
  have hcommA : ∀ x ∈ R ⊔ R', x * a = a * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hacA.2 x hx
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommA x (Subgroup.mem_sup_left hx))
  have hR'c : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommA x (Subgroup.mem_sup_right hx))
  have hR'N : R' ≤ Subgroup.normalizer (K : Set G) :=
    (Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hKΩ hyp.std.1.hne hz' hz).trans' hR'K'.1
  exact ⟨_, secImg_mem_secFam hKtq, _,
    omegaNbr_secImg hΩ hc2 hKtq hK'tq hRK hR'K' hRc hR'c hcommR hR'N⟩

theorem layer_trichotomy_of_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply)
    (hOE : TwinDisc.OddCentEdge (Nat.card G)) (hbad : BadElt z a) :
    SecNoExitAt Ω a ∨
      (∃ M ∈ TwinDisc.secFam Ω a, ∃ zb : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a),
        IsUniqueInvolution M zb ∧ TightInO2 zb) ∨
      TwinE4 (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) := by
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  have htr := layer_transitive_of_bad hyp ha2 ha1 hacA hT hbad
  have hedge := layer_edge hyp ha2 hacA
  have hodd := hOE hih.1 hih.2 _ hlt _ hS htr hedge
  exact ExitU.noExit_or_o2_or_e4 hS htr hedge hodd

end Layer

section Typing

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerLieType6 (Ω : Set (Subgroup G)) (c : G) : Prop :=
  ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam Ω c)), TwinPerp23.LieTypeOf D 6 true

@[expose] def LayerAE5 (Ω : Set (Subgroup G)) (c : G) : Prop :=
  ∃ I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5, I.φ.ker = ⊥

@[expose] def LayerSq (Ω : Set (Subgroup G)) (c : G) : Prop :=
  ∀ β : MulAut (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
    (∀ y, β (β (β (β y))) = y) →
      ∃ M ∈ TwinDisc.secFam Ω c, ∃ y ∈ M, orderOf y = 4 ∧ β (β y) = y

@[expose] def AE5SqModel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), Q8Section X Φ →
    ∀ I : TC.Thin.AEIdent Φ 5, I.φ.ker = ⊥ →
      ∀ β : MulAut X, (∀ y, β (β (β (β y))) = y) → ∃ M ∈ Φ, ∃ y ∈ M, orderOf y = 4 ∧ β (β y) = y

end Typing

section Leaves

@[expose] def P25_TypedO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ cA S R R', a * a = 1 → a ≠ 1 → BadElt z a →
      (∃ M ∈ TwinDisc.secFam Ω a, ∃ zb : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a),
        IsUniqueInvolution M zb ∧ TightInO2 zb) → LayerAE5 Ω a

@[expose] def P25_TypedE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ cA S R R', a * a = 1 → a ≠ 1 → BadElt z a →
      (¬ ∃ M ∈ TwinDisc.secFam Ω a, ∃ zb : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a),
        IsUniqueInvolution M zb ∧ TightInO2 zb) →
      ¬ TwinE4 (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a))

end Leaves

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
