module

import CFSG.Holt.H78.Lemma27SE
public import CFSG.Holt.H78.Lemma27Alt
import CFSG.Holt.H78.DataPrimitive
import CFSG.Holt.H78.OddCore

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Cases

@[expose] def Lemma27Case1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
    IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1) →
    Lemma27iBelow (Nat.card G) (Nat.card Ω) →
    ∀ {Γ : Set Ω}, IsBlock G Γ → Γ ≠ Set.univ → ∀ {α β : Ω}, α ∈ Γ → β ∈ Γ → α ≠ β →
      Lemma27iAt G Ω α β

@[expose] def Lemma27Case2a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
    IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1) →
    Lemma27iBelow (Nat.card G) (Nat.card Ω) → jHull G Ω = ⊤ →
    ∀ (D : HoltData G Ω) (k : D.ι), D.M k = alternatingGroup (D.Ψc k) →
      7 ≤ Fintype.card (D.Ψc k) → ∀ {α β : Ω}, α ≠ β → D.coord α k ≠ D.coord β k →
      Lemma27iAt G Ω α β

@[expose] def Lemma27Case2b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
    IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1) →
    ∀ (D : HoltData G Ω), (∀ i, IsNaturalSE (D.M i)) → ∀ {α β : Ω}, α ≠ β →
      (∀ i, D.coord α i ≠ D.coord β i) →
      Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) ∧
        (Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) → Lemma27iAt G Ω α β)

end Cases

section Reductions

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem lemma27iAt_of_jHull_le {K : Subgroup G} (hK : jHull G Ω ≤ K) {α β : Ω}
    (h : Lemma27iAt ↥K Ω α β) : Lemma27iAt G Ω α β := by
  have hJK : ∀ {g : G}, g ∈ longInv G Ω → g ∈ K := fun hg => hK (mem_jHull_of_mem_longInv hg)
  have hswap : longInvSwap G Ω α β = Subtype.val '' longInvSwap ↥K Ω α β := by
    ext g
    refine ⟨fun hg => ⟨⟨g, hJK hg.1⟩, ⟨mem_longInv_subgroup_iff.mpr hg.1, hg.2⟩, rfl⟩, ?_⟩
    rintro ⟨k, hk, rfl⟩
    exact ⟨mem_longInv_subgroup_iff.mp hk.1, hk.2⟩
  have hat : longInvAt G Ω α = Subtype.val '' longInvAt ↥K Ω α := by
    ext g
    refine ⟨fun hg => ⟨⟨g, hJK hg.1⟩, mem_longInvAt_subgroup_iff.mpr hg, rfl⟩, ?_⟩
    rintro ⟨k, hk, rfl⟩
    exact mem_longInvAt_subgroup_iff.mp hk
  have hΔ : holtDelta' G Ω α β = holtDelta' ↥K Ω α β := by
    ext γ
    refine ⟨fun ⟨s, hs, hsγ⟩ => ⟨⟨s, hJK hs.1⟩, mem_longInvAt_subgroup_iff.mpr hs, hsγ⟩, ?_⟩
    rintro ⟨k, hk, hkγ⟩
    exact ⟨k, mem_longInvAt_subgroup_iff.mp hk, hkγ⟩
  refine ⟨?_, fun γ hγ => holtDelta'_eq_orbit_of_subset hγ ?_⟩
  · rw [hswap, hat, Nat.card_image_of_injective Subtype.val_injective,
      Nat.card_image_of_injective Subtype.val_injective]
    exact h.1
  · rw [hΔ] at hγ ⊢
    rw [h.2 γ hγ]
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, k.2.1, k.2.2⟩, rfl⟩

theorem card_longInvSwap_eq_of_forall_le [Finite G] [Finite Ω] (hG : IsStarGroup G Ω) (α : Ω)
    (hle : ∀ β, β ≠ α → Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α))
    (β : Ω) : Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) := by
  classical
  have := Fintype.ofFinite Ω
  by_cases hβα : β = α
  · rw [hβα, longInvSwap_self]
  have hconst : ∑ _β' ∈ Finset.univ.erase α, Nat.card (longInvAt G Ω α) =
      Nat.card (longInvAt G Ω α) * (Fintype.card Ω - 1) := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ,
      smul_eq_mul, mul_comm]
  exact (Finset.sum_eq_sum_iff_of_le fun β' hβ' => hle β' (Finset.ne_of_mem_erase hβ')).mp
    ((sum_card_longInvSwap hG α).trans hconst.symm) β
    (Finset.mem_erase.mpr ⟨hβα, Finset.mem_univ β⟩)

private theorem coord_fibre_ne_univ (D : HoltData G Ω) (k : D.ι) (α : Ω) :
    {ω | D.coord ω k = D.coord α k} ≠ Set.univ := by
  intro h
  have : Nontrivial (D.Ψc k) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := D.five_le_card k; omega)
  obtain ⟨b, hb⟩ := exists_ne (D.coord α k)
  obtain ⟨ω, hω⟩ := D.exists_coord_apply_eq k b
  have hmem : ω ∈ {ω | D.coord ω k = D.coord α k} := h ▸ Set.mem_univ ω
  exact hb (hω.symm.trans hmem)

end Reductions

section Induction

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

theorem lemma27iAt_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (α β : Ω) : Lemma27iAt G Ω α β :=
  ⟨(lemma_2_3_ii hO α β).1, fun γ hγ => ((lemma_2_3_ii hO α β).2.2 γ hγ).2⟩

theorem lemma27iAt_of_cases (h1 : Lemma27Case1) (h2a : Lemma27Case2a) (h2b : Lemma27Case2b)
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1))
    (hIH : Lemma27iBelow (Nat.card G) (Nat.card Ω)) {α β : Ω} (hαβ : α ≠ β) :
    Lemma27iAt G Ω α β := by
  by_cases hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω
  · exact lemma27iAt_of_isPretransitive hO α β
  by_cases hH : jHull G Ω = ⊤
  swap
  · have hlt : Nat.card (jHull G Ω) < Nat.card G :=
      lt_of_not_ge fun h => hH (Subgroup.eq_top_of_le_card _ h)
    exact lemma27iAt_of_jHull_le le_rfl (hIH _ Ω (Or.inl hlt) (isStarGroup_jHull hG)
      (hB.of_le (Subgroup.card_le_card_group _) le_rfl) α β hαβ)
  obtain ⟨D⟩ := hB.holtStructure hG
  have hcase1 : ∀ {β' : Ω}, β' ≠ α → (∃ k, D.coord α k = D.coord β' k) →
      Lemma27iAt G Ω α β' := by
    rintro β' hβ' ⟨k, hk⟩
    exact h1 G Ω hG hB hIH (D.isBlock_coord_fibre hH k (D.coord α k))
      (coord_fibre_ne_univ D k α) rfl hk.symm hβ'.symm
  by_cases hA : ∃ k, D.M k = alternatingGroup (D.Ψc k) ∧ 7 ≤ Fintype.card (D.Ψc k)
  · obtain ⟨k, hk, hk7⟩ := hA
    by_cases hc : ∃ k', D.coord α k' = D.coord β k'
    · exact hcase1 hαβ.symm hc
    · push Not at hc
      exact h2a G Ω hG hB hIH hH D k hk hk7 hαβ (hc k)
  · have hSE : ∀ i, IsNaturalSE (D.M i) := fun i =>
      (D.factor i).resolve_left fun h => hA ⟨i, h⟩
    have hle : ∀ β', β' ≠ α → Nat.card (longInvSwap G Ω α β') ≤ Nat.card (longInvAt G Ω α) := by
      intro β' hβ'
      by_cases hc : ∃ k, D.coord α k = D.coord β' k
      · exact (hcase1 hβ' hc).1.le
      · push Not at hc
        exact (h2b G Ω hG hB D hSE hβ'.symm hc).1
    by_cases hc : ∃ k, D.coord α k = D.coord β k
    · exact hcase1 hαβ.symm hc
    · push Not at hc
      exact (h2b G Ω hG hB D hSE hαβ hc).2 (card_longInvSwap_eq_of_forall_le hG α hle β)

theorem lemma27iBelow_of_cases (h1 : Lemma27Case1) (h2a : Lemma27Case2a)
    (h2b : Lemma27Case2b) (n d : ℕ) : Lemma27iBelow n d := by
  induction n using Nat.strong_induction_on generalizing d with
  | _ n ihn =>
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro X _ _ Δ _ _ _ hlt hX hBX α β hαβ
      refine lemma27iAt_of_cases h1 h2a h2b hX hBX ?_ hαβ
      rcases hlt with hlt | ⟨rfl, hlt⟩
      · exact ihn _ hlt _
      · exact ihd _ hlt

theorem card_longInvSwap_eq_of_cases (h1 : Lemma27Case1) (h2a : Lemma27Case2a)
    (h2b : Lemma27Case2b) (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {α β : Ω} (hαβ : α ≠ β) :
    Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) :=
  (lemma27iAt_of_cases h1 h2a h2b hG hB (lemma27iBelow_of_cases h1 h2a h2b _ _) hαβ).1

theorem holtDelta'_eq_orbit_of_cases (h1 : Lemma27Case1) (h2a : Lemma27Case2a)
    (h2b : Lemma27Case2b) (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta' G Ω α β) :
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ :=
  (lemma27iAt_of_cases h1 h2a h2b hG hB (lemma27iBelow_of_cases h1 h2a h2b _ _) hαβ).2 γ hγ

end Induction

section Proved


theorem lemma27Case1 : Lemma27Case1 := fun _ _ _ _ _ _ _ hG hB hIH _ hΓ hΓu _ _ hα hβ hαβ =>
  lemma27iAt_of_isBlock hG hB hIH hΓ hΓu hα hβ hαβ

theorem lemma27Case2b : Lemma27Case2b := fun _ _ _ _ _ _ _ hG hB D hSE _ _ _ hc =>
  ⟨card_longInvSwap_le_of_isNaturalSE hG hB D hSE hc, lemma27iAt_of_isNaturalSE hG hB D hSE hc⟩

theorem lemma27Case2a_of_socInvFixesBlocks (h24 : SocInvFixesBlocksStatement) : Lemma27Case2a :=
  fun G _ _ Ω _ _ _ hG hB hIH _ D _ hk hk7 _ _ hαβ hc =>
    lemma27iAt_of_alternating hG hB hIH D (h24 G Ω hG hB D) hk hk7 hαβ hc

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

theorem card_longInvSwap_eq_of_socInvFixesBlocks (h24 : SocInvFixesBlocksStatement)
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {α β : Ω}
    (hαβ : α ≠ β) : Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) :=
  card_longInvSwap_eq_of_cases lemma27Case1 (lemma27Case2a_of_socInvFixesBlocks h24)
    lemma27Case2b hG hB hαβ

theorem holtDelta'_eq_orbit_of_socInvFixesBlocks (h24 : SocInvFixesBlocksStatement)
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {α β γ : Ω}
    (hαβ : α ≠ β) (hγ : γ ∈ holtDelta' G Ω α β) :
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ :=
  holtDelta'_eq_orbit_of_cases lemma27Case1 (lemma27Case2a_of_socInvFixesBlocks h24)
    lemma27Case2b hG hB hαβ hγ

end Proved

end CFSG.Holt.H78
