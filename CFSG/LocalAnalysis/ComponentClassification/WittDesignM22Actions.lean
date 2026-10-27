module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCases
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Involutions
public import Certificates.Certificate2029

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction
open scoped Pointwise

theorem index_stabilizer_point (a : Fin 22) : (stabilizer M22 a).index = 22 := by
  have h := Subgroup.card_mul_index (stabilizer M22 a)
  rw [card_stabilizer_point, card_M22'] at h
  omega

theorem index_stabilizer_hexad {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    (stabilizer M22 B).index = 77 := by
  have h := Subgroup.card_mul_index (stabilizer M22 B)
  rw [card_stabilizer_hexad hB, card_M22'] at h
  omega

theorem mem_hexads_of_card_orbit {X : Finset (Fin 22)} (hX : X.card = 6)
    (h77 : Nat.card (orbit M22 X) = 77) : X ∈ hexads := by
  have hindex : (stabilizer M22 X).index = 77 := by
    have h := card_orbit_mul_card_stabilizer X
    have h2 := Subgroup.card_mul_index (stabilizer M22 X)
    rw [h77] at h
    rw [card_M22'] at h2
    have hs : Nat.card (stabilizer M22 X) = 5760 := by omega
    rw [hs] at h2
    omega
  obtain ⟨B, hB, hXB⟩ := eq_stabilizer_hexad_of_index_77 _ hindex
  have hinv : ∀ g : stabilizer M22 B, ∀ x ∈ X, (g.1 : Equiv.Perm (Fin 22)) x ∈ X := by
    intro g x hx
    have hg : g.1 ∈ stabilizer M22 X := by
      rw [hXB]
      exact g.2
    exact mem_stabilizer_finset_iff.1 hg x hx
  have hfull : ∀ x ∈ X, ∀ y, (x ∈ B ↔ y ∈ B) → y ∈ X := by
    intro x hx y hxy
    obtain ⟨g, rfl⟩ := (exists_stabilizer_apply_eq_iff hB x y).2 hxy
    exact hinv g x hx
  obtain ⟨x, hx⟩ : X.Nonempty := by
    rw [← Finset.card_pos, hX]
    norm_num
  by_cases hxB : x ∈ B
  · have hsub : B ⊆ X := fun y hy => hfull x hx y (iff_of_true hxB hy)
    have := Finset.eq_of_subset_of_card_le hsub (by rw [hX, card_of_mem_hexads hB])
    exact this ▸ hB
  · exfalso
    have hsub : Bᶜ ⊆ X := fun y hy => hfull x hx y (iff_of_false hxB (Finset.mem_compl.1 hy))
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, card_of_mem_hexads hB, hX] at this
    norm_num at this

theorem m22_point_hexad_actions :
    (Nat.card M22 = 443520 ∧ (443520 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 ∧
      IsMultiplyPretransitive M22 (Fin 22) 3 ∧
      ∀ a : Fin 22, Nat.card (stabilizer M22 a) = 20160 ∧
        Nonempty (stabilizer M22 a ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4) ∧
        ∀ x y : Fin 22, x ≠ a → y ≠ a → ∃ g ∈ stabilizer M22 a, g • x = y) ∧
    ((∃ X : Finset (Fin 22), X.card = 6 ∧ orbit M22 X = ↑hexads) ∧ hexads.card = 77 ∧
      (∀ X : Finset (Fin 22), X.card = 6 →
        (Nat.card (orbit M22 X) = 77 ↔ orbit M22 X = ↑hexads)) ∧
      IsSteinerTriple hexads ∧
      (∀ B ∈ hexads, ∀ B' ∈ hexads, B ≠ B' → (B ∩ B').card = 0 ∨ (B ∩ B').card = 2) ∧
      ∀ B ∈ hexads, (hexads.filter fun B' => Disjoint B B').card = 16 ∧
        (hexads.filter fun B' => (B ∩ B').card = 2).card = 60) ∧
    (∀ B ∈ hexads, Nat.card (stabilizer M22 B) = 5760 ∧ Nat.card (resHexad B).ker = 16 ∧
      (∀ e f : (resHexad B).ker, e * f = f * e) ∧ (∀ e : (resHexad B).ker, e * e = 1) ∧
      (∀ x y : Fin 22, x ∉ B → y ∉ B →
        ∃! e : (resHexad B).ker, (e.1.1 : Equiv.Perm (Fin 22)) x = y) ∧
      (resHexad B).range = alternatingGroup B ∧
      (∃ F : Subgroup (stabilizer M22 B), F ⊓ (resHexad B).ker = ⊥ ∧
        F ⊔ (resHexad B).ker = ⊤ ∧ Nonempty (F ≃* alternatingGroup (Fin 6))) ∧
      (∀ x y : Fin 22,
        (∃ g : stabilizer M22 B, (g.1 : Equiv.Perm (Fin 22)) x = y) ↔ (x ∈ B ↔ y ∈ B)) ∧
      ∀ C ∈ hexads, ∀ C' ∈ hexads,
        (∃ g : stabilizer M22 B, g.1 • C = C') ↔ (B ∩ C).card = (B ∩ C').card) ∧
    (∀ a : Fin 22, (hexads.filter (a ∈ ·)).card = 21 ∧ (hexads.filter (a ∉ ·)).card = 56 ∧
      ∀ C ∈ hexads, ∀ C' ∈ hexads,
        (∃ g : stabilizer M22 a, g.1 • C = C') ↔ (a ∈ C ↔ a ∈ C')) ∧
    ((∀ a : Fin 22, (stabilizer M22 a).index = 22) ∧
      (∀ B ∈ hexads, (stabilizer M22 B).index = 77) ∧
      (∀ H : Subgroup M22, H.index = 22 → ∃ a : Fin 22, H = stabilizer M22 a) ∧
      (∀ H : Subgroup M22, H.index = 77 → ∃ B ∈ hexads, H = stabilizer M22 B) ∧
      (∀ H K : Subgroup M22, H.index = 22 → K.index = 22 →
        ∃ g : M22, K = H.map (MulAut.conj g).toMonoidHom) ∧
      (∀ H K : Subgroup M22, H.index = 77 → K.index = 77 →
        ∃ g : M22, K = H.map (MulAut.conj g).toMonoidHom) ∧
      ∀ H : Subgroup M22, H ≠ ⊤ → H.index < 99 → H.index = 22 ∨ H.index = 77) ∧
    ((∀ s t : M22, orderOf s = 2 → orderOf t = 2 → IsConj s t) ∧
      Nat.card {x : M22 // orderOf x = 2} = 1155 ∧
      ∀ t : M22, orderOf t = 2 → Nat.card (Subgroup.centralizer {t}) = 384) := by
  refine ⟨⟨card_M22', by norm_num, isMultiplyPretransitive_M22, fun a =>
      ⟨card_stabilizer_point a, nonempty_stabilizer_equiv_PSL a,
        fun x y hx hy => exists_mem_stabilizer_smul_eq a hx hy⟩⟩, ⟨⟨hexad0, Certificates.certificate2029,
      orbit_hexad0⟩, card_hexads, fun X hX => ⟨fun h => ?_, fun h => ?_⟩, isSteinerTriple_hexads,
      fun B hB B' hB' hne => isSteinerTriple_hexads.card_inter hB hB' hne,
      fun B hB => hexads_intersections hB⟩, fun B hB => ⟨card_stabilizer_hexad hB,
      card_ker_resHexad hB, ker_resHexad_comm hB, ker_resHexad_mul_self hB,
      fun x y hx hy => existsUnique_ker_resHexad hB hx hy, range_resHexad hB,
      exists_complement hB, exists_stabilizer_apply_eq_iff hB,
      fun C hC C' hC' => exists_stabilizer_smul_hexad_eq_iff hB hC hC'⟩, fun a =>
      ⟨isSteinerTriple_hexads.card_blocks_mem a, isSteinerTriple_hexads.card_blocks_not_mem a,
        fun C hC C' hC' => exists_stabilizer_point_smul_hexad_eq_iff a hC hC'⟩,
      ⟨index_stabilizer_point, fun B hB => index_stabilizer_hexad hB, eq_stabilizer_of_index_22,
        eq_stabilizer_hexad_of_index_77, fun H K hH hK => ?_, fun H K hH hK => ?_,
        fun H hH h99 => ?_⟩, ⟨fun s t hs ht => isConj_of_orderOf_eq_two hs ht, card_involutions,
        fun t ht => card_centralizer_involution ht⟩⟩
  ·
    have hXmem := mem_hexads_of_card_orbit hX h
    obtain ⟨g, rfl⟩ := mem_hexads_iff.1 hXmem
    rw [orbit_smul, orbit_hexad0]
  · rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_hexads]
  · obtain ⟨a, rfl⟩ := eq_stabilizer_of_index_22 H hH
    obtain ⟨b, rfl⟩ := eq_stabilizer_of_index_22 K hK
    obtain ⟨g, hg⟩ := exists_smul_eq M22 a b
    exact ⟨g, by rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]⟩
  · obtain ⟨B, hB, rfl⟩ := eq_stabilizer_hexad_of_index_77 H hH
    obtain ⟨C, hC, rfl⟩ := eq_stabilizer_hexad_of_index_77 K hK
    obtain ⟨k, rfl⟩ := mem_hexads_iff.1 hB
    obtain ⟨k', rfl⟩ := mem_hexads_iff.1 hC
    refine ⟨k' * k⁻¹, ?_⟩
    rw [← stabilizer_smul_eq_stabilizer_map_conj, smul_smul, inv_mul_cancel_right]
  · rcases low_index_classification H hH h99 with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h

end CFSG.ComponentClassification.WittDesign
