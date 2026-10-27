module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesTransport
public import CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)

section Tori

variable (F : Type) [Field F]

@[expose] noncomputable def sp6ParamA : Fˣ →* (Fin 3 → Fˣ) :=
  MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0

@[expose] noncomputable def sp6ParamM2 : Fˣ × Fˣ →* (Fin 3 → Fˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0).comp (MonoidHom.fst Fˣ Fˣ) *
    (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 1).comp (MonoidHom.snd Fˣ Fˣ)

@[expose] noncomputable def sp6ParamM3 : Fˣ × Fˣ →* (Fin 3 → Fˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0).comp (MonoidHom.fst Fˣ Fˣ) *
    ((MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 1) * (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 2)).comp
      (MonoidHom.snd Fˣ Fˣ)

@[expose] noncomputable def sp6Diag :
    (Fin 3 → Fˣ) →* CFSG.Assembly.LowTwoRank.StatedSp 3 F :=
  (CFSG.LieType.Universal.Symplectic.equivStatedSp 3 F).toMonoidHom.comp
    TauCeti.GLSymplecticFin.diagonal

variable {F}

@[expose] noncomputable def sp6TorusA (A : Subgroup Fˣ) :
    Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 3 F) :=
  A.map ((sp6Diag F).comp (sp6ParamA F))

@[expose] noncomputable def sp6TorusM2 (A : Subgroup Fˣ) :
    Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 3 F) :=
  (A.prod A).map ((sp6Diag F).comp (sp6ParamM2 F))

@[expose] noncomputable def sp6TorusM3 (A : Subgroup Fˣ) :
    Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 3 F) :=
  (A.prod A).map ((sp6Diag F).comp (sp6ParamM3 F))

end Tori

theorem mul_diagonal_eq_diagonal_mul_iff {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (g : Matrix ι ι F) (d : ι → F) :
    g * Matrix.diagonal d = Matrix.diagonal d * g ↔ ∀ i j, d i ≠ d j → g i j = 0 := by
  constructor
  · intro h i j hij
    have h' := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
    have h'' : (d j - d i) * g i j = 0 := by
      rw [sub_mul, mul_comm (d j), h', sub_self]
    rcases mul_eq_zero.mp h'' with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hij
    · exact h0
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

@[expose] def Sp6PieceComputation : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (A : Subgroup Fˣ), 4 ≤ Nat.card F →
    (∃ a ∈ A, a ^ 2 ≠ 1) →
    pieceCards ⊤ (sp6TorusA A) (sp6TorusM2 A) (sp6TorusM3 A) =
      (ordSp 2 (Nat.card F), ordSL 2 (Nat.card F), ordSL 2 (Nat.card F))

section Kinds

variable {G : Type*} [Group G] [Finite G] {E T₁₂ T₁ T₂ : Subgroup G}

private theorem exists_unit_sq_ne_one {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
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

theorem pieceCards_field (hSp6 : Sp6PieceComputation) {F : Type} [Field F] [Finite F]
    [CharP F 2] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : 2 ≤ q) {A : Subgroup Fˣ}
    (hA : ∃ a ∈ A, a ^ 2 ≠ 1) (Φ : CFSG.Assembly.LowTwoRank.StatedSp 3 F ≃* E)
    (h₁₂ : T₁₂ ⊔ centralizer (E : Set G) =
      (sp6TorusA A).map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G))
    (h₁ : T₁ ⊔ centralizer (E : Set G) =
      (sp6TorusM2 A).map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G))
    (h₂ : T₂ ⊔ centralizer (E : Set G) =
      (sp6TorusM3 A).map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G)) :
    pieceCards E T₁₂ T₁ T₂ = pieceOrders .field q := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    nlinarith
  rw [pieceCards_eq_of_mulEquiv Φ h₁₂ h₁ h₂, hSp6 F A h4 hA, hF]
  rfl

theorem pieceCards_swap (hSp6 : Sp6PieceComputation) {F : Type} [Field F] [Finite F] [CharP F 2]
    {q : ℕ} (hF : Nat.card F = q) (hq : 4 ≤ q)
    (Φ : CFSG.Assembly.LowTwoRank.StatedSp 3 F × CFSG.Assembly.LowTwoRank.StatedSp 3 F ≃* E)
    (h₁₂ : T₁₂ ⊔ centralizer (E : Set G) =
      (diagPairSubgroup (sp6TorusA (⊤ : Subgroup Fˣ))).map (E.subtype.comp Φ.toMonoidHom) ⊔
        centralizer (E : Set G))
    (h₁ : T₁ ⊔ centralizer (E : Set G) =
      (diagPairSubgroup (sp6TorusM2 (⊤ : Subgroup Fˣ))).map (E.subtype.comp Φ.toMonoidHom) ⊔
        centralizer (E : Set G))
    (h₂ : T₂ ⊔ centralizer (E : Set G) =
      (diagPairSubgroup (sp6TorusM3 (⊤ : Subgroup Fˣ))).map (E.subtype.comp Φ.toMonoidHom) ⊔
        centralizer (E : Set G)) :
    pieceCards E T₁₂ T₁ T₂ = pieceOrders .swap q := by
  have h4 : 4 ≤ Nat.card F := hF ▸ hq
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one h4
  rw [pieceCards_eq_of_mulEquiv Φ h₁₂ h₁ h₂, pieceCards_diagPairSubgroup,
    hSp6 F ⊤ h4 ⟨a, mem_top a, ha⟩, hF]
  rfl

end Kinds

end CFSG.SeitzReduction.F4Pilot
