module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotMainGraphOmegaInputsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def GraphKindModelInput (κ : Sp6Kind) : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 ^ f →
    ∃ (M : Type) (_ : Group M) (_ : Finite M) (_ : Group.IsPerfect M) (ι : StatedSp 3 k →* M)
      (βC : MulAut M),
      (∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
        π'.ker ≤ center E' → ∃ s : M →* E', ∀ g, π' (s g) = g) ∧
      (∀ (S : Type) [Group S], Sp6KindType S f κ →
        ∃ π : M →* S, Function.Surjective π ∧ π.ker ≤ center M) ∧
      Function.Injective ι ∧ fixedSubgroup βC = ι.range ∧
      (∀ ρ : k ≃+* k, ∃ ρ' : MulAut M, ∀ g, ρ' (ι g) = ι (statedSpMap (ρ : k →+* k) 3 g)) ∧
      (∀ (β : MulAut M), centerQuotientAut β * centerQuotientAut β = 1 →
        centerQuotientAut β ∉ (MulAut.conj : M ⧸ center M →* MulAut (M ⧸ center M)).range →
        ∀ f' : ℕ, LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f' →
          ∃ Ψ : M ≃* M, ∀ g, β (Ψ g) = Ψ (βC g)) ∧
      ∀ (G : Type) [Group G] [Finite G] (Φ : M →* G), Φ.ker ≤ center M →
        pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup kˣ)).map ι).map Φ)
          (((sp6TorusM2 (⊤ : Subgroup kˣ)).map ι).map Φ)
          (((sp6TorusM3 (⊤ : Subgroup kˣ)).map ι).map Φ) = pieceOrders κ (2 ^ f)

section Rows


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_exact_of_graphKindModel_X {κ : Sp6Kind} (hκF : κ ≠ .field) (hκS : κ ≠ .swap)
    (hM : GraphKindModelInput κ) {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X κ) :
    ∃ (M : Type) (_ : Group M) (ι : StatedSp 3 K →* M) (Φ : M →* G),
      Φ.range = neighbourCore e .X ∧ Φ.ker ≤ center M ∧
      ((sp6TorusA (⊤ : Subgroup Kˣ)).map ι).map Φ = leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM2 (⊤ : Subgroup Kˣ)).map ι).map Φ = leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM3 (⊤ : Subgroup Kˣ)).map ι).map Φ = leviTorusG e {2} ⊓ neighbourLeviG e .X ∧
      pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup Kˣ)).map ι).map Φ)
        (((sp6TorusM2 (⊤ : Subgroup Kˣ)).map ι).map Φ)
        (((sp6TorusM3 (⊤ : Subgroup Kˣ)).map ι).map Φ) = pieceOrders κ (2 ^ f) := by
  obtain ⟨M, _, _, _, ι, βC, hsplit, hcov, hι, hfix, hρ, hnorm, hpieces⟩ :=
    hM f hf K hw.card_eq
  obtain ⟨S, _, hS, ρ, hρs, hρker⟩ := exists_surjective_neighbourCore_of_hr8Kind_graph hw hf e
    (by decide) hκF hκS hX
  obtain ⟨π, hπ, hπker⟩ := hcov S hS
  have : Group.IsPerfect (neighbourCore e .X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_lift_of_central π hπ hsplit ρ hρs hρker
  set Φ₁ : M →* G := (neighbourCore e .X).subtype.comp Φ₀ with hΦ₁
  have hE₁ : Φ₁.range = neighbourCore e .X := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  have hker₁ : Φ₁.ker ≤ center M := by
    intro g hg
    have hg₀ : Φ₀ g = 1 := (neighbourCore e .X).subtype_injective (by rw [map_one]; exact hg)
    apply hπker
    rw [MonoidHom.mem_ker, ← hΦ₀, hg₀, map_one]
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ :=
    exists_graphLift_of_closed_X hw hf e hκF hκS hX hsplit Φ₁ hE₁ hker₁
  obtain ⟨Ψ, hΨ⟩ := hnorm β hβ2 hβo f hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = neighbourCore e .X := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ = Φ₂ (βC g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (βC g))
    rw [← hΨ, hβ]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  obtain ⟨Φ', hr, hk, hA, h2, h3⟩ := exists_exact_of_cover_model e (RingEquiv.refl K) hι hρ hfix
    Φ₂ hker₂ hc hD
  exact ⟨M, inferInstance, ι, Φ', hr.trans hE₂, hk, hA, h2, h3, hpieces G Φ' hk⟩

omit [Finite K] [CharP K 2] in
theorem pieceCards_of_graphKindModelInput {κ : Sp6Kind} (hκF : κ ≠ .field) (hκS : κ ≠ .swap)
    (hM : GraphKindModelInput κ) [Finite K] {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X') (h : HR8Kind e t f N κ) :
    neighbourPieceCards e N = pieceOrders κ (2 ^ f) := by
  have : CharP K 2 := charP_two_of_natCard_eq_two_pow hw.card_eq
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  cases N with
  | X =>
    obtain ⟨M, _, ι, Φ, hE, -, hA, h₂, h₃, hP⟩ :=
      exists_exact_of_graphKindModel_X hκF hκS hM hw hf e h
    rw [neighbourPieceCards_eq_of_exact e hN hE hA h₂ h₃]
    exact hP
  | Y =>
    obtain ⟨M, _, ι, Φ, hE, -, hA, h₂, h₃, hP⟩ :=
      exists_exact_of_graphKindModel_X hκF hκS hM hw hf _ ((hr8Kind_Y_iff_X e).1 h)
    obtain ⟨hA', h₂', h₃'⟩ := exact_Y_of_exact_X e hA h₂ h₃
    rw [neighbourPieceCards_eq_of_exact e hN (hE.trans (neighbourCore_Y_eq_X e).symm) hA' h₂' h₃']
    exact hP
  | X' => exact absurd rfl hN

theorem omegaPieceTablesInput_of_models (hP : GraphKindModelInput .omegaPlus8)
    (hM : GraphKindModelInput .omegaMinus8) : OmegaPieceTablesInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN κ hκ h
  rcases hκ with rfl | rfl
  · exact pieceCards_of_graphKindModelInput (by decide) (by decide) hP hw hf e hN h
  · exact pieceCards_of_graphKindModelInput (by decide) (by decide) hM hw hf e hN h

end Rows

end CFSG.SeitzReduction.F4Pilot
