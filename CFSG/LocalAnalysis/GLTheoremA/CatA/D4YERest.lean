module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YECore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YERank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YEEven

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T

section Defs

variable {H : Type} [Group H]

@[expose] def IsD4Odd (K : Subgroup H) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Odd n ∧ catalogIs ↥K (isD4pow2 n)

@[expose] def D4Unhandled (K B : Subgroup H) : Prop :=
  27 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set H)) < Nat.card B ∨
    (9 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set H)) < Nat.card B ∧ IsD4Odd K ∧
      ∃ T : Subgroup H, IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set H) ∧
        T ≤ Subgroup.normalizer (K : Set H) ∧ ¬ T ≤ Subgroup.centralizer (K : Set H))

end Defs

@[expose] def D4BigCoreRest : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K B : Subgroup H),
    catalogIs ↥K isD4any → ¬ catalogIs ↥K S9.isD4two →
    (∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) → IsElemAbelian 3 B →
    B ≤ Subgroup.normalizer (K : Set H) →
    (∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (K : Set H), NotCentralOut (conjAut K b hb)) →
    D4RankCase K B → D4Unhandled K B → False

theorem map_subtype_elemAbelian {H : Type} [Group H] {K : Subgroup H} {E : Subgroup ↥K}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map K.subtype) :=
  CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map K.subtype hE

theorem d4BigCoreAt_of_rest (hrest : D4BigCoreRest) : D4BigCoreAt := by
  classical
  intro H _ _ K B hK hn hKc hB hBK hout hcase
  by_cases hU : D4Unhandled K B
  · exact hrest H K B hK hn hKc hB hBK hout hcase hU
  unfold D4Unhandled at hU
  push Not at hU
  obtain ⟨h27', hrest2'⟩ := hU
  have h27 : Nat.card B ≤ 27 * Nat.card (Bo K B) := h27'
  have hrest2 : 9 * Nat.card (Bo K B) < Nat.card B → IsD4Odd K → ∀ T : Subgroup H, IsPGroup 2 T →
      T ≠ ⊥ → B ≤ Subgroup.normalizer (T : Set H) → T ≤ Subgroup.normalizer (K : Set H) →
        T ≤ Subgroup.centralizer (K : Set H) := hrest2'
  have hBopos : 0 < Nat.card (Bo K B) := Nat.card_pos
  obtain ⟨E4, hE4el, hE4c⟩ := d4big_rank4 hK hn
  have hE4K : E4.map K.subtype ≤ K := Subgroup.map_subtype_le E4
  have hE4card : Nat.card (E4.map K.subtype) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE4c]
  rcases hcase with hall | ⟨hmax, T, hT2, hTne, hBT, hTK⟩
  · exact core_all hKc hB hE4K (map_subtype_elemAbelian hE4el) (by rw [hE4card]; omega) hall
  · by_cases h9 : Nat.card B ≤ 9 * Nat.card (Bo K B)
    · obtain ⟨E3, W3, hE3el, hE3c, hW32, hW3ne, hE3W⟩ := d4big_rank3 hK hn
      have hE3K : E3.map K.subtype ≤ K := Subgroup.map_subtype_le E3
      have hE3card : Nat.card (E3.map K.subtype) = 3 ^ 3 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hE3c]
      have hW3K : W3.map K.subtype ≤ K := Subgroup.map_subtype_le W3
      refine core_two hKc hB hE3K (map_subtype_elemAbelian hE3el) (hW32.map K.subtype)
        (fun h => hW3ne ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h)) ?_ ?_
        (by rw [hE3card]; omega) hmax
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem _ (hE3W hy))
      · intro s hs
        refine mem_normalizer_of_centralizes fun w hw => Bo_cent hs w (hW3K hw)
    · by_cases hodd : IsD4Odd K
      · have hTc := hrest2 (lt_of_not_ge h9) hodd T hT2 hTne hBT hTK
        refine core_two hKc hB hE4K (map_subtype_elemAbelian hE4el) hT2 hTne ?_ ?_
          (by rw [hE4card]; omega) hmax
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
          refine mem_normalizer_of_centralizes fun t ht => ?_
          exact Subgroup.mem_centralizer_iff.1 (hTc ht) (y : H) y.2
        · exact fun s hs => hBT (Subgroup.mem_inf.1 hs).1
      · obtain ⟨n, hn2, hKn⟩ := exists_isD4pow2 hK hn
        have hev : Even n := by
          by_contra hne
          exact hodd ⟨n, hn2, Nat.not_even_iff_odd.1 hne, hKn⟩
        obtain ⟨E, W, hEK, hWK, hEel, hEc, hW2, hWne, hEW⟩ := hasE4W_of_even hev hn2 hKn
        refine core_two hKc hB hEK hEel hW2 hWne hEW ?_ (by rw [hEc]; omega) hmax
        intro s hs
        exact mem_normalizer_of_centralizes fun w hw => Bo_cent hs w (hWK hw)

end CFSG.LocalAnalysis.GLTheoremA.D4Y
