module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLinear
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainKinds

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open Matrix
open CFSG.Quasithin (perfectCore)

local instance f4PilotMainGraphPiecesMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def rankOneTori : AmalgamNeighbour →
    Finset (Fin (Tag.rank .F4)) × Finset (Fin (Tag.rank .F4))
  | .Y => ({2}, {1})
  | _ => ({1}, {2})

section Pieces


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbourPieceCards_eq_pieceCards (e : L ≃* adjointGroup .F4 K) (N : AmalgamNeighbour) :
    neighbourPieceCards e N = pieceCards (neighbourCore e N) (leviTorusG e {1, 2})
      (leviTorusG e (rankOneTori N).1) (leviTorusG e (rankOneTori N).2) := by
  cases N <;> rfl

end Pieces

section Model

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}

@[expose] def SLModelOf (F : Type) [Field F] (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F)
    (E T₁₂ T₁ T₂ : Subgroup G) : Prop :=
  ∃ Φ : SpecialLinearGroup (Fin n) F →* G, Φ.range = E ∧
    Φ.ker ≤ center (SpecialLinearGroup (Fin n) F) ∧
    T₁₂ ⊔ centralizer (E : Set G) =
      (linTorusA τ (⊤ : Subgroup Fˣ)).map Φ ⊔ centralizer (E : Set G) ∧
    T₁ ⊔ centralizer (E : Set G) =
      (linTorusM2 τ (⊤ : Subgroup Fˣ)).map Φ ⊔ centralizer (E : Set G) ∧
    T₂ ⊔ centralizer (E : Set G) =
      (linTorusM3 τ (⊤ : Subgroup Fˣ)).map Φ ⊔ centralizer (E : Set G)

theorem pieceCards_eq_of_slModelOf {τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F}
    {E T₁₂ T₁ T₂ : Subgroup G} {Φ : SpecialLinearGroup (Fin n) F →* G} (hE : Φ.range = E)
    (h₁₂ : T₁₂ ⊔ centralizer (E : Set G) =
      (linTorusA τ (⊤ : Subgroup Fˣ)).map Φ ⊔ centralizer (E : Set G))
    (h₁ : T₁ ⊔ centralizer (E : Set G) =
      (linTorusM2 τ (⊤ : Subgroup Fˣ)).map Φ ⊔ centralizer (E : Set G))
    (h₂ : T₂ ⊔ centralizer (E : Set G) =
      (linTorusM3 τ (⊤ : Subgroup Fˣ)).map Φ ⊔ centralizer (E : Set G)) :
    pieceCards E T₁₂ T₁ T₂ =
      pieceCards Φ.range ((linTorusA τ ⊤).map Φ) ((linTorusM2 τ ⊤).map Φ)
        ((linTorusM3 τ ⊤).map Φ) := by
  subst hE
  simp only [pieceCards, inf_centralizer_eq_of_sup_eq h₁₂, inf_centralizer_eq_of_sup_eq h₁,
    inf_centralizer_eq_of_sup_eq h₂]

theorem exists_units_sq_ne_one_of_four_le [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ a : Fˣ, a ^ 2 ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1, -1} : Finset F)) (t := Finset.univ) (by
      calc ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
        _ < Finset.univ.card := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨h0, h1, hm1⟩ := hx
  refine ⟨Units.mk0 x h0, fun h => ?_⟩
  have h2 : x ^ 2 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h
    simpa using this
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact h1 h3
  · exact hm1 h3

variable [Finite G] [Finite F]

theorem pieceCards_of_slModelOf_lin6 {E T₁₂ T₁ T₂ : Subgroup G}
    (h : SLModelOf F (lin6Torus F) E T₁₂ T₁ T₂) {q : ℕ} (hq : Nat.card F = q) (hq4 : 4 ≤ q) :
    pieceCards E T₁₂ T₁ T₂ = pieceOrders .linear6 q := by
  obtain ⟨Φ, hE, hker, h₁₂, h₁, h₂⟩ := h
  obtain ⟨a₀, ha₀⟩ := exists_units_sq_ne_one_of_four_le (F := F) (hq ▸ hq4)
  rw [pieceCards_eq_of_slModelOf hE h₁₂ h₁ h₂,
    pieceCards_range_lin6 Φ hker (hq ▸ hq4) (mem_top a₀) ha₀, hq]

theorem pieceCards_of_slModelOf_lin7 {E T₁₂ T₁ T₂ : Subgroup G}
    (h : SLModelOf F (lin7Torus F) E T₁₂ T₁ T₂) {q : ℕ} (hq : Nat.card F = q) (hq4 : 4 ≤ q) :
    pieceCards E T₁₂ T₁ T₂ = pieceOrders .linear7 q := by
  obtain ⟨Φ, hE, hker, h₁₂, h₁, h₂⟩ := h
  obtain ⟨a₀, ha₀⟩ := exists_units_sq_ne_one_of_four_le (F := F) (hq ▸ hq4)
  rw [pieceCards_eq_of_slModelOf hE h₁₂ h₁ h₂,
    pieceCards_range_lin7 Φ hker (hq ▸ hq4) (mem_top a₀) ha₀, hq]

end Model


section Inputs


@[expose] def LinearGraphNeighbourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' →
      (HR8Kind e t f N .linear6 → ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 2 ^ f ∧
        SLModelOf F (lin6Torus F) (neighbourCore e N) (leviTorusG e {1, 2})
          (leviTorusG e (rankOneTori N).1) (leviTorusG e (rankOneTori N).2)) ∧
      (HR8Kind e t f N .linear7 → ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 2 ^ f ∧
        SLModelOf F (lin7Torus F) (neighbourCore e N) (leviTorusG e {1, 2})
          (leviTorusG e (rankOneTori N).1) (leviTorusG e (rankOneTori N).2))

@[expose] def UnitaryOmegaPieceTablesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' → ∀ κ : Sp6Kind,
      (κ = .unitary6 ∨ κ = .unitary7 ∨ κ = .omegaPlus8 ∨ κ = .omegaMinus8) →
      HR8Kind e t f N κ → neighbourPieceCards e N = pieceOrders κ (2 ^ f)

theorem graphPieceTablesInput_of_inputs (hL : LinearGraphNeighbourInput)
    (hUO : UnitaryOmegaPieceTablesInput) : GraphPieceTablesInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN κ hκF hκS h
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  cases κ with
  | field => exact absurd rfl hκF
  | swap => exact absurd rfl hκS
  | linear6 =>
    obtain ⟨F, _, _, hF, hM⟩ := (hL G L K e t f hw hf N hN).1 h
    rw [neighbourPieceCards_eq_pieceCards]
    exact pieceCards_of_slModelOf_lin6 hM hF hq4
  | linear7 =>
    obtain ⟨F, _, _, hF, hM⟩ := (hL G L K e t f hw hf N hN).2 h
    rw [neighbourPieceCards_eq_pieceCards]
    exact pieceCards_of_slModelOf_lin7 hM hF hq4
  | unitary6 => exact hUO G L K e t f hw hf N hN _ (.inl rfl) h
  | unitary7 => exact hUO G L K e t f hw hf N hN _ (.inr (.inl rfl)) h
  | omegaPlus8 => exact hUO G L K e t f hw hf N hN _ (.inr (.inr (.inl rfl))) h
  | omegaMinus8 => exact hUO G L K e t f hw hf N hN _ (.inr (.inr (.inr rfl))) h

end Inputs

end CFSG.SeitzReduction.F4Pilot
