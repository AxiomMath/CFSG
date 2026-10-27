module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenAbelian

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem eq_N_inf_centralizer [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {B : Subgroup G} (hBN : B ≤ fr.N) (hB : Nat.card B = 3 ^ 5)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {x : G} (hxB : x ∈ B) (hxM : x ∉ fr.M) :
    B = fr.N ⊓ centralizer ({x} : Set G) :=
  Subgroup.eq_of_le_of_card_ge
    (fun b hb => ⟨hBN hb, mem_centralizer_singleton_iff.mpr (hBc b hb x hxB)⟩)
    (by rw [hB]; exact card_N_inf_centralizer_le p7 p10 hz (hBN hxB) hxM)

theorem exists_mem_not_mem_M [Finite G] (p10 : JankoProp10 fr) {B : Subgroup G}
    (hB : Nat.card B = 3 ^ 5) (hBM : B ≠ fr.M) : ∃ x ∈ B, x ∉ fr.M := by
  by_contra h
  exact hBM (Subgroup.eq_of_le_of_card_ge (fun x hx => by_contra fun hxM => h ⟨x, hx, hxM⟩)
    (by rw [hB, p10.card_M]))

theorem card_filter_mem_not_mem [Fintype G] [DecidableEq G] (A B : Subgroup G)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (h : A ≤ B) :
    (Finset.univ.filter fun x => x ∈ B ∧ x ∉ A).card = Nat.card B - Nat.card A := by
  classical
  have hB : Nat.card B = (Finset.univ.filter fun x => x ∈ B).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hA : Nat.card A = (Finset.univ.filter fun x => x ∈ A).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun x => x ∈ A) ⊆ (Finset.univ.filter fun x => x ∈ B) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h hx
  have heq : (Finset.univ.filter fun x => x ∈ B ∧ x ∉ A) =
      (Finset.univ.filter fun x => x ∈ B) \ (Finset.univ.filter fun x => x ∈ A) := by
    ext x
    simp
  rw [heq, Finset.card_sdiff_of_subset hsub, hA, hB]

theorem card_abelian [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) :
    Nat.card {B : Subgroup G // B ≤ fr.N ∧ Nat.card B = 3 ^ 5 ∧
      ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} = 10 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  let P : Subgroup G → Prop := fun B => B ≤ fr.N ∧ Nat.card B = 3 ^ 5 ∧
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  let s : Finset G := Finset.univ.filter fun x => x ∈ fr.N ∧ x ∉ fr.M
  let t : Finset (Subgroup G) := Finset.univ.filter fun B => P B ∧ B ≠ fr.M
  let f : G → Subgroup G := fun x => fr.N ⊓ centralizer ({x} : Set G)
  have hfx : ∀ x ∈ fr.N, x ∈ f x := fun x hx => ⟨hx, mem_centralizer_singleton_iff.mpr rfl⟩
  have hmaps : Set.MapsTo f s t := by
    intro x hx
    simp only [s, t, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨⟨inf_le_left, card_N_inf_centralizer p7 p10 hz hx.1 hx.2,
      comm_of_mem_N_inf_centralizer p7 p10 hz hx.1 hx.2⟩, fun h => hx.2 ?_⟩
    have h' := hfx x hx.1
    rw [h] at h'
    exact h'
  have hcount := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ B ∈ t, (s.filter fun x => f x = B).card = 216 := by
    intro B hB
    simp only [t, P, Finset.mem_filter, Finset.mem_univ, true_and] at hB
    obtain ⟨⟨hBN, hB5, hBc⟩, hBM⟩ := hB
    obtain ⟨x₀, hx₀B, hx₀M⟩ := exists_mem_not_mem_M p10 hB5 hBM
    have hBinf : B ⊓ fr.M = fr.ZN := by
      rw [eq_N_inf_centralizer p7 p10 hz hBN hB5 hBc hx₀B hx₀M]
      exact N_inf_centralizer_inf_M p7 p10 hz (hBN hx₀B) hx₀M
    have heq : (s.filter fun x => f x = B) =
        Finset.univ.filter fun x => x ∈ B ∧ x ∉ B ⊓ fr.M := by
      ext x
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf, not_and]
      constructor
      · rintro ⟨⟨hxN, hxM⟩, hfxB⟩
        have h' := hfx x hxN
        rw [hfxB] at h'
        exact ⟨h', fun _ => hxM⟩
      · rintro ⟨hxB, hxM⟩
        exact ⟨⟨hBN hxB, hxM hxB⟩,
          (eq_N_inf_centralizer p7 p10 hz hBN hB5 hBc hxB (hxM hxB)).symm⟩
    rw [heq, card_filter_mem_not_mem _ _ inf_le_left, hB5, hBinf, card_ZN p7 p10 hz]
    norm_num
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcount
  have hs : s.card = 1944 := by
    simp only [s]
    rw [card_filter_mem_not_mem _ _ M_le_N, card_N p10, p10.card_M]
    norm_num
  rw [hs] at hcount
  have ht : t.card = 9 := by omega
  have hMP : P fr.M := ⟨M_le_N, p10.card_M, p10.M_comm⟩
  have hfull : (Finset.univ.filter P) = insert fr.M t := by
    ext B
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hB
      by_cases h : B = fr.M
      · exact Or.inl h
      · exact Or.inr ⟨hB, h⟩
    · rintro (rfl | ⟨hB, -⟩)
      · exact hMP
      · exact hB
  have hMt : fr.M ∉ t := by simp [t]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter P).card = 10
  rw [hfull, Finset.card_insert_of_notMem hMt, ht]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
