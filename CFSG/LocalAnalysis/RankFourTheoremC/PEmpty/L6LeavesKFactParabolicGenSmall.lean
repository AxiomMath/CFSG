module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenCore
public import CFSG.Quasithin.Background.SmithC27RLieA6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenSmallK

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits Subgroup Equiv

abbrev A6 : Type := ↥(alternatingGroup (Fin 6))

@[expose] def alt6C012 : A6 :=
  ⟨swap 0 2 * swap 0 1, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6C024 : A6 :=
  ⟨swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5), by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6C345 : A6 :=
  ⟨swap 3 4 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem alt6V1_mul : ∀ x y : A6, (x = 1 ∨ x = alt6Inv ∨ x = alt6InvA ∨ x = alt6InvC) →
    (y = 1 ∨ y = alt6Inv ∨ y = alt6InvA ∨ y = alt6InvC) →
      (x * y = 1 ∨ x * y = alt6Inv ∨ x * y = alt6InvA ∨ x * y = alt6InvC) := by
  intro x y hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6V1_inv : ∀ x : A6, (x = 1 ∨ x = alt6Inv ∨ x = alt6InvA ∨ x = alt6InvC) →
    (x⁻¹ = 1 ∨ x⁻¹ = alt6Inv ∨ x⁻¹ = alt6InvA ∨ x⁻¹ = alt6InvC) := by
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6V2_mul : ∀ x y : A6, (x = 1 ∨ x = alt6Inv ∨ x = alt6InvB ∨ x = alt6InvD) →
    (y = 1 ∨ y = alt6Inv ∨ y = alt6InvB ∨ y = alt6InvD) →
      (x * y = 1 ∨ x * y = alt6Inv ∨ x * y = alt6InvB ∨ x * y = alt6InvD) := by
  intro x y hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6V2_inv : ∀ x : A6, (x = 1 ∨ x = alt6Inv ∨ x = alt6InvB ∨ x = alt6InvD) →
    (x⁻¹ = 1 ∨ x⁻¹ = alt6Inv ∨ x⁻¹ = alt6InvB ∨ x⁻¹ = alt6InvD) := by
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

@[expose] def alt6V1 : Subgroup A6 where
  carrier := {x | x = 1 ∨ x = alt6Inv ∨ x = alt6InvA ∨ x = alt6InvC}
  one_mem' := Or.inl rfl
  mul_mem' := fun {x y} hx hy => alt6V1_mul x y hx hy
  inv_mem' := fun {x} hx => alt6V1_inv x hx

@[expose] def alt6V2 : Subgroup A6 where
  carrier := {x | x = 1 ∨ x = alt6Inv ∨ x = alt6InvB ∨ x = alt6InvD}
  one_mem' := Or.inl rfl
  mul_mem' := fun {x y} hx hy => alt6V2_mul x y hx hy
  inv_mem' := fun {x} hx => alt6V2_inv x hx

theorem mem_alt6V1 {x : A6} : x ∈ alt6V1 ↔ x = 1 ∨ x = alt6Inv ∨ x = alt6InvA ∨ x = alt6InvC :=
  Iff.rfl

theorem mem_alt6V2 {x : A6} : x ∈ alt6V2 ↔ x = 1 ∨ x = alt6Inv ∨ x = alt6InvB ∨ x = alt6InvD :=
  Iff.rfl

instance : DecidablePred (· ∈ alt6V1) := fun x => decidable_of_iff _ mem_alt6V1.symm

instance : DecidablePred (· ∈ alt6V2) := fun x => decidable_of_iff _ mem_alt6V2.symm

theorem alt6V1_le_syl : alt6V1 ≤ alt6Syl := by
  intro x hx
  rw [mem_alt6Syl]
  rcases mem_alt6V1.1 hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6V2_le_syl : alt6V2 ≤ alt6Syl := by
  intro x hx
  rw [mem_alt6Syl]
  rcases mem_alt6V2.1 hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6V1_ne_bot : alt6V1 ≠ ⊥ := by
  intro h
  have : alt6Inv ∈ alt6V1 := Or.inr (Or.inl rfl)
  rw [h, Subgroup.mem_bot] at this
  exact absurd this (by decide)

theorem alt6V2_ne_bot : alt6V2 ≠ ⊥ := by
  intro h
  have : alt6Inv ∈ alt6V2 := Or.inr (Or.inl rfl)
  rw [h, Subgroup.mem_bot] at this
  exact absurd this (by decide)

theorem mem_normalizer_iff_alt6 {V : Subgroup A6} {g : A6} :
    g ∈ normalizer (V : Set A6) ↔ ∀ h : A6, h ∈ V ↔ g * h * g⁻¹ ∈ V :=
  Subgroup.mem_normalizer_iff

theorem alt6Syl_le_normalizer_V1 : alt6Syl ≤ normalizer (alt6V1 : Set A6) := by
  intro g hg
  rw [mem_alt6Syl] at hg
  rw [mem_normalizer_iff_alt6]
  exact KPGenK.iff_of_fwd (P := (· ∈ alt6V1)) (KPGenK.fwd_V1 g hg)
    (KPGenK.fwd_V1 g⁻¹ (Commute.inv_left (hg : Commute g alt6Inv)))

theorem alt6Syl_le_normalizer_V2 : alt6Syl ≤ normalizer (alt6V2 : Set A6) := by
  intro g hg
  rw [mem_alt6Syl] at hg
  rw [mem_normalizer_iff_alt6]
  exact KPGenK.iff_of_fwd (P := (· ∈ alt6V2)) (KPGenK.fwd_V2 g hg)
    (KPGenK.fwd_V2 g⁻¹ (Commute.inv_left (hg : Commute g alt6Inv)))

theorem alt6C012_mem_normalizer_V1 : alt6C012 ∈ normalizer (alt6V1 : Set A6) := by
  rw [mem_normalizer_iff_alt6]
  refine KPGenK.iff_of_fwd (P := (· ∈ alt6V1)) (fun x hx => ?_) (fun x hx => ?_) <;>
    rcases mem_alt6V1.1 hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6C012_not_mem_syl : alt6C012 ∉ alt6Syl := by
  rw [mem_alt6Syl]
  decide +kernel

theorem alt6C024_mem_normalizer_V2 : alt6C024 ∈ normalizer (alt6V2 : Set A6) := by
  rw [mem_normalizer_iff_alt6]
  refine KPGenK.iff_of_fwd (P := (· ∈ alt6V2)) (fun x hx => ?_) (fun x hx => ?_) <;>
    rcases mem_alt6V2.1 hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem alt6C024_not_mem_syl : alt6C024 ∉ alt6Syl := by
  rw [mem_alt6Syl]
  decide +kernel

theorem alt6C024_not_mem_normalizer_V1 : alt6C024 ∉ normalizer (alt6V1 : Set A6) := by
  rw [mem_normalizer_iff_alt6]
  intro h
  have h1 := (h alt6Inv).1 (Or.inr (Or.inl rfl))
  revert h1
  decide +kernel

theorem alt6C345_not_mem_normalizer_V1 : alt6C345 ∉ normalizer (alt6V1 : Set A6) := by
  rw [mem_normalizer_iff_alt6]
  intro h
  have h1 := (h alt6Inv).1 (Or.inr (Or.inl rfl))
  revert h1
  decide +kernel

theorem alt6C345_not_mem_normalizer_V2 : alt6C345 ∉ normalizer (alt6V2 : Set A6) := by
  rw [mem_normalizer_iff_alt6]
  intro h
  have h1 := (h alt6Inv).1 (Or.inr (Or.inl rfl))
  revert h1
  decide +kernel

theorem card_eq_24_of_alt6 {P : Subgroup A6} (hSP : alt6Syl ≤ P) (hne : P ≠ alt6Syl)
    (hP : P ≠ ⊤) : Nat.card P = 24 := by
  rcases card_eq_of_sylow_le_alt6 isSylowTwoOf_alt6Syl hSP with h | h | h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hSP (by rw [h, card_alt6Syl])).symm hne
  · exact h
  · exact absurd (Subgroup.eq_top_of_card_eq P
      (by rw [h, CFSG.QuasithinUnique.Setup.X3.card_alt6])) hP

@[expose] def alt6P1 : Subgroup A6 := normalizer (alt6V1 : Set A6)

@[expose] def alt6P2 : Subgroup A6 := normalizer (alt6V2 : Set A6)

theorem hasParGen_alt6 : HasParGen A6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := exists_sylow_two_coe_eq isSylowTwoOf_alt6Syl
  have hNW : normalizer ((W : Subgroup A6) : Set A6) = alt6Syl := by
    rw [hW]
    exact normalizer_alt6Syl
  have hS2 : IsPGroup 2 alt6Syl := isSylowTwoOf_alt6Syl.2.1
  have hcore₁ : pCoreOf 2 alt6P1 ≠ ⊥ := by
    intro hbot
    have hle : alt6V1 ≤ pCoreOf 2 alt6P1 :=
      le_pCoreOf_of_le_normalizer 2 (le_normalizer : alt6V1 ≤ alt6P1) le_rfl
        (hS2.to_le alt6V1_le_syl)
    rw [hbot, le_bot_iff] at hle
    exact alt6V1_ne_bot hle
  have hcore₂ : pCoreOf 2 alt6P2 ≠ ⊥ := by
    intro hbot
    have hle : alt6V2 ≤ pCoreOf 2 alt6P2 :=
      le_pCoreOf_of_le_normalizer 2 (le_normalizer : alt6V2 ≤ alt6P2) le_rfl
        (hS2.to_le alt6V2_le_syl)
    rw [hbot, le_bot_iff] at hle
    exact alt6V2_ne_bot hle
  have hSP₁ : alt6Syl ≤ alt6P1 := alt6Syl_le_normalizer_V1
  have hSP₂ : alt6Syl ≤ alt6P2 := alt6Syl_le_normalizer_V2
  have hP₁S : alt6P1 ≠ alt6Syl := by
    intro h
    exact alt6C012_not_mem_syl (h ▸ alt6C012_mem_normalizer_V1)
  have hP₂S : alt6P2 ≠ alt6Syl := by
    intro h
    exact alt6C024_not_mem_syl (h ▸ alt6C024_mem_normalizer_V2)
  have hP₁t : alt6P1 ≠ ⊤ := by
    intro h
    have hmem : alt6C345 ∈ alt6P1 := h ▸ Subgroup.mem_top _
    exact alt6C345_not_mem_normalizer_V1 hmem
  have hP₂t : alt6P2 ≠ ⊤ := by
    intro h
    have hmem : alt6C345 ∈ alt6P2 := h ▸ Subgroup.mem_top _
    exact alt6C345_not_mem_normalizer_V2 hmem
  have h24₁ := card_eq_24_of_alt6 hSP₁ hP₁S hP₁t
  have h24₂ := card_eq_24_of_alt6 hSP₂ hP₂S hP₂t
  have hP₁₂ : alt6P1 ≠ alt6P2 := by
    intro h
    have hmem : alt6C024 ∈ alt6P1 := h ▸ alt6C024_mem_normalizer_V2
    exact alt6C024_not_mem_normalizer_V1 hmem
  have hgen : alt6P1 ⊔ alt6P2 = ⊤ := by
    have hM := card_eq_of_sylow_le_alt6 isSylowTwoOf_alt6Syl
      (hSP₁.trans (le_sup_left : alt6P1 ≤ alt6P1 ⊔ alt6P2))
    rcases hM with h | h | h
    · have hle := Subgroup.card_le_of_le (le_sup_left : alt6P1 ≤ alt6P1 ⊔ alt6P2)
      rw [h, h24₁] at hle
      omega
    · have h1 : alt6P1 ⊔ alt6P2 = alt6P1 :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_left : alt6P1 ≤ alt6P1 ⊔ alt6P2)
          (by rw [h, h24₁])).symm
      have h2 : alt6P1 ⊔ alt6P2 = alt6P2 :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_right : alt6P2 ≤ alt6P1 ⊔ alt6P2)
          (by rw [h, h24₂])).symm
      exact absurd (h1.symm.trans h2) hP₁₂
    · exact Subgroup.eq_top_of_card_eq _ (by rw [h, CFSG.QuasithinUnique.Setup.X3.card_alt6])
  refine ⟨W, ?_⟩
  rw [eq_top_iff, ← hgen]
  exact sup_le (le_parabGen (by rw [hNW]; exact hSP₁) hcore₁)
    (le_parabGen (by rw [hNW]; exact hSP₂) hcore₂)

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
