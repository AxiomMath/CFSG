module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Coprime
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Conj
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Bender.Thm2

variable {G : Type} [Group G] [Finite G]

theorem part_a_of_ivk {z : G} {S : Subgroup G} (h812 : IVK_8_12_ly) (ctx : Stage2Ctx G z Kind.ly S)
    {H : Subgroup G} (hH : H ≠ ⊤) (hSH : S ≤ H) {V : Subgroup G} (hV : MaxSInv 3 S H V) :
    ∀ V' : Subgroup G, MaxSInv 3 S H V' → ∃ c ∈ H ⊓ centralizer (S : Set G), V' = conjugate V c :=
  L121.part_a ctx.sylow.isPGroup hSH
    (fun V₁ V₂ hV₁ hV₂ h₁ h₂ => ((h812 G z S ctx H hH hSH V₁ hV₁ h₁).2.1 V₂ hV₂ h₂).symm) hV

theorem transitivity {z : G} {S : Subgroup G} (h812 : IVK_8_12_ly) (ctx : Stage2Ctx G z Kind.ly S)
    {Y₁ Y₂ : Subgroup G} (hY₁ : MaxSInv 3 S ⊤ Y₁) (hY₂ : MaxSInv 3 S ⊤ Y₂) (hne : Y₁ ⊓ Y₂ ≠ ⊥) :
    ∃ c ∈ centralizer (S : Set G), Y₂ = conjugate Y₁ c := by
  by_contra hcon
  let 𝔅 : Set (Subgroup G × Subgroup G) := {τ | MaxSInv 3 S ⊤ τ.1 ∧ MaxSInv 3 S ⊤ τ.2 ∧
    τ.1 ⊓ τ.2 ≠ ⊥ ∧ ¬ ∃ c ∈ centralizer (S : Set G), τ.2 = conjugate τ.1 c}
  obtain ⟨⟨A, B⟩, ⟨hA, hB, hAB, hnc⟩, hmax⟩ :=
    Set.exists_max_image 𝔅 (fun τ => Nat.card ↥(τ.1 ⊓ τ.2)) (Set.toFinite _)
      ⟨(Y₁, Y₂), hY₁, hY₂, hne, hcon⟩
  have key : ∀ A' B' : Subgroup G, MaxSInv 3 S ⊤ A' → MaxSInv 3 S ⊤ B' →
      Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B') →
        ∃ c ∈ centralizer (S : Set G), B' = conjugate A' c := by
    intro A' B' hA' hB' hlt
    by_contra hc
    have hne' : A' ⊓ B' ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hlt
      have := Nat.card_pos (α := ↥(A ⊓ B))
      omega
    exact absurd (hmax (A', B') ⟨hA', hB', hne', hc⟩) (not_le.mpr hlt)
  have hApg : IsPGroup 3 ↥A := hA.2.1
  have hBpg : IsPGroup 3 ↥B := hB.2.1
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  have hYA : A ⊓ B < A := by
    refine lt_of_le_of_ne inf_le_left (fun h => ?_)
    have hAB' : A ≤ B := inf_eq_left.mp h
    have : B = A := hA.2.2.2 B le_top hBpg hB.2.2.1 hAB'
    exact hnc ⟨1, one_mem _, by rw [conjugate_one]; exact this⟩
  have hYB : A ⊓ B < B := by
    refine lt_of_le_of_ne inf_le_right (fun h => ?_)
    have hBA : B ≤ A := inf_eq_right.mp h
    have : A = B := hB.2.2.2 A le_top hApg hA.2.2.1 hBA
    exact hnc ⟨1, one_mem _, by rw [conjugate_one]; exact this.symm⟩
  have hSY : S ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := fun s hs =>
    inf_normalizer_le_normalizer_inf ⟨hA.2.2.1 hs, hB.2.2.1 hs⟩
  have hSN : S ≤ normalizer ((normalizer ((A ⊓ B : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun s hs => Subgroup.le_normalizer (hSY hs)
  have hVA : A ⊓ B < A ⊓ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    lt_inf_normalizer_of_lt h3 hApg hYA
  have hVB : A ⊓ B < B ⊓ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    lt_inf_normalizer_of_lt h3 hBpg hYB
  obtain ⟨D_A, hDA, hVAD⟩ := exists_maxSInv_above (r := 3) (S := S)
    (H := normalizer ((A ⊓ B : Subgroup G) : Set G))
    (W := A ⊓ normalizer ((A ⊓ B : Subgroup G) : Set G)) inf_le_right (hApg.to_le inf_le_left)
    (fun s hs => inf_normalizer_le_normalizer_inf ⟨hA.2.2.1 hs, hSN hs⟩)
  obtain ⟨D_B, hDB, hVBD⟩ := exists_maxSInv_above (r := 3) (S := S)
    (H := normalizer ((A ⊓ B : Subgroup G) : Set G))
    (W := B ⊓ normalizer ((A ⊓ B : Subgroup G) : Set G)) inf_le_right (hBpg.to_le inf_le_left)
    (fun s hs => inf_normalizer_le_normalizer_inf ⟨hB.2.2.1 hs, hSN hs⟩)
  obtain ⟨E_A, hEA, hDAE⟩ :=
    exists_maxSInv_above (r := 3) (S := S) (H := ⊤) (W := D_A) le_top hDA.2.1 hDA.2.2.1
  obtain ⟨E_B, hEB, hDBE⟩ :=
    exists_maxSInv_above (r := 3) (S := S) (H := ⊤) (W := D_B) le_top hDB.2.1 hDB.2.2.1
  have hltA : Nat.card ↥(A ⊓ B) < Nat.card ↥(A ⊓ E_A) :=
    card_lt_of_lt' (lt_of_lt_of_le hVA (le_inf inf_le_left (hVAD.trans hDAE)))
  have hltB : Nat.card ↥(A ⊓ B) < Nat.card ↥(B ⊓ E_B) :=
    card_lt_of_lt' (lt_of_lt_of_le hVB (le_inf inf_le_left (hVBD.trans hDBE)))
  obtain ⟨cA, hcA, hEAeq⟩ := key A E_A hA hEA hltA
  obtain ⟨cB, hcB, hEBeq⟩ := key B E_B hB hEB hltB
  have hHne : normalizer ((A ⊓ B : Subgroup G) : Set G) ≠ ⊤ :=
    normalizer_ne_top ctx.std.kps.1 (ne_top_of_isPGroup_three ctx.orderOf_z hApg) inf_le_left hAB
  obtain ⟨c, hc, hDBeq⟩ := part_a_of_ivk h812 ctx hHne hSY hDA D_B hDB
  have hcC : c ∈ centralizer (S : Set G) := hc.2
  have hEAc : MaxSInv 3 S ⊤ (conjugate E_A c) := maxSInv_top_conjugate hcC hEA
  have hDBle : D_B ≤ conjugate E_A c := by
    rw [hDBeq]
    exact conjugate_mono hDAE c
  have hltC : Nat.card ↥(A ⊓ B) < Nat.card ↥(E_B ⊓ conjugate E_A c) :=
    card_lt_of_lt' (lt_of_lt_of_le hVB (le_inf (hVBD.trans hDBE) (hVBD.trans hDBle)))
  obtain ⟨c₂, hc₂, hc₂eq⟩ := key E_B (conjugate E_A c) hEB hEAc hltC
  apply hnc
  refine ⟨cA * c * (cB * c₂)⁻¹, mul_mem (mul_mem hcA hcC) (inv_mem (mul_mem hcB hc₂)), ?_⟩
  have h1 : conjugate A (cA * c) = conjugate B (cB * c₂) := by
    calc conjugate A (cA * c) = conjugate (conjugate A cA) c := (conjugate_conjugate A cA c).symm
      _ = conjugate E_A c := by rw [← hEAeq]
      _ = conjugate E_B c₂ := hc₂eq
      _ = conjugate (conjugate B cB) c₂ := by rw [← hEBeq]
      _ = conjugate B (cB * c₂) := conjugate_conjugate B cB c₂
  calc B = conjugate (conjugate B (cB * c₂)) (cB * c₂)⁻¹ := (conjugate_inv_conjugate B _).symm
    _ = conjugate (conjugate A (cA * c)) (cB * c₂)⁻¹ := by rw [h1]
    _ = conjugate A (cA * c * (cB * c₂)⁻¹) := conjugate_conjugate _ _ _

end CFSG.OddStandard.GH71
