module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitA

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open
open scoped Matrix

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def Smaller (D : ClassicalModel A) (n : ℕ) (x : G) : Prop :=
  ∃ m < n, D.HasMeasure x m

theorem Smaller.mono {D : ClassicalModel A} {n n' : ℕ} {x : G} (h : Smaller D n x)
    (hn : n ≤ n') : Smaller D n' x := by
  obtain ⟨m, hm, hmx⟩ := h
  exact ⟨m, by omega, hmx⟩

theorem SplitData.mono {J : Subgroup G} {P₁ P₂ P₁' P₂' : G → Prop} {F : Type} [Field F]
    {ι₁ ι₂ : F → G} (h : SplitData A J P₁ P₂ F ι₁ ι₂) (h₁ : ∀ x, P₁ x → P₁' x)
    (h₂ : ∀ x, P₂ x → P₂' x) : SplitData A J P₁' P₂' F ι₁ ι₂ :=
  { h with
    prop₁ := fun x hx => h₁ _ (h.prop₁ x hx)
    prop₂ := fun x hx => h₂ _ (h.prop₂ x hx) }

theorem SplitAt.mono {J : Subgroup G} {q : ℕ} {P₁ P₂ P₁' P₂' : G → Prop}
    (h : SplitAt A J q P₁ P₂) (h₁ : ∀ x, P₁ x → P₁' x) (h₂ : ∀ x, P₂ x → P₂' x) :
    SplitAt A J q P₁' P₂' := by
  obtain ⟨F, hF₁, hF₂, ι₁, ι₂, hF, hd⟩ := h
  exact ⟨F, hF₁, hF₂, ι₁, ι₂, hF, hd.mono h₁ h₂⟩

namespace ClassicalModel

theorem smaller_of_hasRank (D : ClassicalModel A) {x : G} {k ℓ : ℕ} (hx : D.HasRank x k)
    (hk : k < ℓ) : Smaller D (3 * ℓ + 1) x := by
  obtain ⟨m, hm, hmx⟩ := D.exists_hasMeasure_le hx
  exact ⟨m, by omega, hmx⟩

theorem exists_suzukiType (D : ClassicalModel A)
    (hD : D.family = .orthPlus ∨ D.family = .orthMinus) (hZ : Odd (Nat.card (center ↥A)))
    {x : G} (hx : x ∈ A) (hx2 : orderOf x = 2) : ∃ (L : Letter) (ℓ : ℕ), D.SuzukiType x L ℓ := by
  have hxZ := not_mem_center_of_orderOf_eq_two hZ hx hx2
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  cases D with
  | linear => simp [family] at hD
  | unitary => simp [family] at hD
  | symplectic => simp [family] at hD
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    obtain ⟨L, hL⟩ := exists_letterHolds (commRank M) fun v =>
      Assembly.LowTwoRank.StatedQuadPlus n K
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v)
    exact ⟨L, _, hx2, M, hM, hM2, rfl, hL⟩
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    obtain ⟨L, hL⟩ := exists_letterHolds (commRank M) fun v =>
      Assembly.LowTwoRank.StatedQuadMinus n K b c
        (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          K) - 1) *ᵥ v)
    exact ⟨L, _, hx2, M, hM, hM2, rfl, hL⟩

theorem even_of_suzukiType (D : ClassicalModel A) {x : G} {L : Letter} {ℓ : ℕ}
    (h : D.SuzukiType x L ℓ) (hL : L ≠ .b) : Even ℓ := by
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic =>
    obtain ⟨-, M, -, -, -, hl⟩ := h
    cases L with
    | a => exact hl.1
    | b => exact absurd rfl hL
    | c => exact hl.1
  | orthPlus =>
    obtain ⟨-, M, -, -, -, hl⟩ := h
    cases L with
    | a => exact hl.1
    | b => exact absurd rfl hL
    | c => exact hl.1
  | orthMinus =>
    obtain ⟨-, M, -, -, -, hl⟩ := h
    cases L with
    | a => exact hl.1
    | b => exact absurd rfl hL
    | c => exact hl.1

end ClassicalModel

open ClassicalModel in
theorem exists_splitAt_smaller [Finite G] (hS : ClassicalSplit) (D : ClassicalModel A)
    (hfam : D.family ≠ .symplectic) (hA : CFSG.Open.IsQuasisimple ↥A)
    (hZ : Odd (Nat.card (center ↥A))) (hq : 4 ≤ D.q) {p : G} (hpA : p ∈ A)
    (hp2 : orderOf p = 2) (hnp : ¬ D.IsPrimary p) {n : ℕ} (hn : D.HasMeasure p n)
    (hI : Case1 D p ∨ Case4 D p) : SplitAt A (jGroup A p) D.q (Smaller D n) (Smaller D n) := by
  obtain ⟨hPC, hMC, hPC2, hMC2⟩ := hS
  obtain ⟨ℓ, hℓ, -⟩ := id hn
  have hn' : 3 * ℓ + 1 ≤ n := hn.ge_of_not_isPrimary hℓ hnp
  suffices h : SplitAt A (jGroup A p) D.q (Smaller D (3 * ℓ + 1)) (Smaller D (3 * ℓ + 1)) from
    h.mono (fun x hx => hx.mono hn') fun x hx => hx.mono hn'
  have hℓ0 := D.pos_of_hasRank hℓ
  cases hf : D.family with
  | symplectic => exact absurd hf hfam
  | linear | unitary =>
    have hℓ2 : 2 ≤ ℓ := by
      rcases Nat.lt_or_ge ℓ 2 with h | h
      · have h1 : ℓ = 1 := by omega
        subst h1
        exfalso
        apply hnp
        cases D with
        | linear => exact hℓ
        | unitary => exact hℓ
        | symplectic => exact hℓ
        | orthPlus => simp [family] at hf
        | orthMinus => simp [family] at hf
      · exact h
    have hJ : jGroup A p = D.alpha p := by
      rcases hI with ⟨hJ, -⟩ | ⟨⟨k, hk⟩, -⟩
      · exact hJ
      · cases D with
        | linear => exact hk.elim
        | unitary => exact hk.elim
        | symplectic => simp [family] at hf
        | orthPlus => simp [family] at hf
        | orthMinus => simp [family] at hf
    rw [hJ]
    have hsplit : SplitAt A (D.alpha p) D.q (fun x => D.HasRank x 1)
        fun x => D.HasRank x (ℓ - 1) := by
      first
      | exact linearSplit G A D hf hA hZ hq p ℓ hℓ2 hℓ
      | exact unitarySplit G A D hf hA hZ hq p ℓ hℓ2 hℓ
    exact hsplit.mono (fun x hx => D.smaller_of_hasRank hx (by omega))
      fun x hx => D.smaller_of_hasRank hx (by omega)
  | orthPlus | orthMinus =>
    have hO : D.family = .orthPlus ∨ D.family = .orthMinus := by
      first | exact Or.inl hf | exact Or.inr hf
    obtain ⟨L, k, hLk⟩ := D.exists_suzukiType hO hZ hpA hp2
    obtain rfl := D.hasRank_unique hℓ (D.hasRank_of_suzukiType hLk)
    cases L with
    | b => exact absurd hLk (orthTypeAC G A D hO p ℓ)
    | a =>
      have hev := D.even_of_suzukiType hLk fun h => by cases h
      have hℓ4 : 4 ≤ ℓ := by
        rcases Nat.lt_or_ge ℓ 4 with h | h
        · have h2 : ℓ = 2 := by
            obtain ⟨r, hr⟩ := hev
            omega
          subst h2
          exact absurd (D.isPrimary_of_suzukiType_a_two hO hLk) hnp
        · exact h
      have hJ : jGroup A p = D.alpha p := by
        rcases hI with ⟨hJ, -⟩ | ⟨⟨k', hk'⟩, -⟩
        · exact hJ
        · exact absurd (D.suzukiType_unique hLk hk').1 fun h => by cases h
      rw [hJ]
      have hsplit : SplitAt A (D.alpha p) D.q (fun x => D.SuzukiType x .a 2)
          fun x => D.SuzukiType x .a (ℓ - 2) := by
        first
        | exact orthPlusSplitA G A D hf hA hZ hq p ℓ hℓ4 hLk
        | exact orthMinusSplitA G A D hf hA hZ hq p ℓ hℓ4 hLk
      exact hsplit.mono (fun x hx => D.smaller_of_hasRank (D.hasRank_of_suzukiType hx)
        (by omega)) fun x hx => D.smaller_of_hasRank (D.hasRank_of_suzukiType hx) (by omega)
    | c =>
      have hev := D.even_of_suzukiType hLk fun h => by cases h
      rcases Nat.lt_or_ge ℓ 4 with h | h
      ·
        have h2 : ℓ = 2 := by
          obtain ⟨r, hr⟩ := hev
          omega
        subst h2
        have hsplit : SplitAt A (jGroup A p) D.q (fun x => D.SuzukiType x .a 2)
            fun x => D.SuzukiType x .a 2 := by
          first
          | exact hPC2 G A D hf hA hZ hq p hLk hI
          | exact hMC2 G A D hf hA hZ hq p hLk hI
        have hsm : ∀ x, D.SuzukiType x .a 2 → Smaller D (3 * 2 + 1) x := fun x hx =>
          ⟨3 * 2, by omega, D.hasMeasure_of_isPrimary (D.hasRank_of_suzukiType hx)
            (D.isPrimary_of_suzukiType_a_two hO hx)⟩
        exact hsplit.mono hsm hsm
      · have hsplit : SplitAt A (jGroup A p) D.q (fun x => D.SuzukiType x .a (ℓ - 2))
            fun x => D.SuzukiType x .c 2 := by
          first
          | exact hPC G A D hf hA hZ hq p ℓ h hLk hI
          | exact hMC G A D hf hA hZ hq p ℓ h hLk hI
        exact hsplit.mono (fun x hx => D.smaller_of_hasRank (D.hasRank_of_suzukiType hx)
          (by omega)) fun x hx => D.smaller_of_hasRank (D.hasRank_of_suzukiType hx) (by omega)

end CFSG.ComponentClassification.RankTwoClassical
