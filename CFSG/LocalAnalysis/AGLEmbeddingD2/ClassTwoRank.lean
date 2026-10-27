module

import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankForm
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.Open
open scoped commutatorElement

section ClassTwo

variable {D : Type*} [Group D] [Finite D] {s : ℕ}

theorem index_centralizer_singleton_le_card_center (hc : commutator D ≤ Subgroup.center D)
    (x : D) : (Subgroup.centralizer ({x} : Set D)).index ≤ Nat.card (Subgroup.center D) := by
  have hker : (commRightHom hc x).ker = Subgroup.centralizer ({x} : Set D) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    change ⁅x, y⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm, eq_comm]
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_le_card_group _

omit [Finite D] in
theorem isMulCommutative_sup_zpowers {T : Subgroup D} [IsMulCommutative T] {x : D}
    (hx : x ∈ Subgroup.centralizer (T : Set D)) :
    IsMulCommutative (T ⊔ Subgroup.zpowers x : Subgroup D) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer T) (Subgroup.zpowers_le.mpr hx)
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hx))
      (Subgroup.le_centralizer _)

omit [Finite D] in
theorem centralizer_inf_le_centralizer_sup_zpowers (T : Subgroup D) (x : D) :
    Subgroup.centralizer (T : Set D) ⊓ Subgroup.centralizer ({x} : Set D) ≤
      Subgroup.centralizer ((T ⊔ Subgroup.zpowers x : Subgroup D) : Set D) := by
  rintro y ⟨hy1, hy2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hle : T ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set D) := by
    refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy1 t ht)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hy2).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem exists_isMulCommutative_extension (hs : s.Prime) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ Subgroup.center D) {T : Subgroup D} [IsMulCommutative T]
    (hT : ¬ Subgroup.centralizer (T : Set D) ≤ T) :
    ∃ T' : Subgroup D, IsMulCommutative T' ∧ s * Nat.card T ≤ Nat.card T' ∧
      (Subgroup.centralizer (T' : Set D)).index ≤
        (Subgroup.centralizer (T : Set D)).index * Nat.card (Subgroup.center D) := by
  have := Fact.mk hs
  obtain ⟨x, hxC, hxT⟩ := IsConcreteLE.not_le_iff_exists.mp hT
  refine ⟨T ⊔ Subgroup.zpowers x, isMulCommutative_sup_zpowers hxC, ?_, ?_⟩
  · refine prime_mul_card_le_of_lt (fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hD g)⟩) ?_
    refine lt_of_le_of_ne le_sup_left fun h => hxT ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  · calc (Subgroup.centralizer ((T ⊔ Subgroup.zpowers x : Subgroup D) : Set D)).index
        ≤ (Subgroup.centralizer (T : Set D) ⊓ Subgroup.centralizer ({x} : Set D)).index :=
          Subgroup.index_antitone (centralizer_inf_le_centralizer_sup_zpowers T x)
      _ ≤ (Subgroup.centralizer (T : Set D)).index *
          (Subgroup.centralizer ({x} : Set D)).index := Subgroup.index_inf_le
      _ ≤ _ := Nat.mul_le_mul_left _ (index_centralizer_singleton_le_card_center hc x)

theorem exists_isMulCommutative_pow_four_le_card (hs : s.Prime) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ Subgroup.center D) (h5 : s ^ 5 ≤ Nat.card (D ⧸ Subgroup.center D)) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have := Fact.mk hs
  obtain ⟨z, hz⟩ := IsPGroup.iff_card.mp
    (show IsPGroup s (Subgroup.center D) from fun g => ⟨1, by
      rw [pow_one]; exact Subtype.ext (hD g)⟩)
  have hDcard : s ^ z * s ^ 5 ≤ Nat.card D := by
    calc s ^ z * s ^ 5 ≤ Nat.card (Subgroup.center D) * (Subgroup.center D).index := by
          rw [hz]; exact Nat.mul_le_mul_left _ h5
      _ = Nat.card D := Subgroup.card_mul_index _
  have harith : ∀ z t : ℕ, z + t < 4 → ¬ z + 5 < 4 + z * t := by
    intro z t h1 h2
    have : z ≤ 3 := by omega
    interval_cases z <;> omega
  have key : ∀ t : ℕ, (∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E) ∨
      ∃ T : Subgroup D, IsMulCommutative T ∧ s ^ z * s ^ t ≤ Nat.card T ∧
        (Subgroup.centralizer (T : Set D)).index ≤ (s ^ z) ^ t := by
    intro t
    induction t with
    | zero =>
      refine Or.inr ⟨Subgroup.center D, inferInstance, ?_, ?_⟩
      · rw [hz]; simp
      · simp
    | succ t ih =>
      rcases ih with h | ⟨T, hT, hTcard, hTidx⟩
      · exact Or.inl h
      · by_cases hstuck : Subgroup.centralizer (T : Set D) ≤ T
        · refine Or.inl ⟨T, hT, ?_⟩
          by_contra hlt
          rw [not_le] at hlt
          have h1 : Nat.card D ≤ Nat.card T * (s ^ z) ^ t :=
            calc Nat.card D = Nat.card (Subgroup.centralizer (T : Set D)) *
                  (Subgroup.centralizer (T : Set D)).index := (Subgroup.card_mul_index _).symm
              _ ≤ Nat.card T * (s ^ z) ^ t :=
                Nat.mul_le_mul (Subgroup.card_le_of_le hstuck) hTidx
          have h2 : s ^ (z + t) < s ^ 4 := by
            rw [pow_add]; exact lt_of_le_of_lt hTcard hlt
          have h3 : s ^ (z + 5) < s ^ (4 + z * t) := by
            rw [pow_add, pow_add, pow_mul]
            calc s ^ z * s ^ 5 ≤ Nat.card D := hDcard
              _ ≤ Nat.card T * (s ^ z) ^ t := h1
              _ < s ^ 4 * (s ^ z) ^ t :=
                Nat.mul_lt_mul_of_pos_right hlt (pow_pos (pow_pos hs.pos z) t)
          exact harith z t ((Nat.pow_lt_pow_iff_right hs.one_lt).mp h2)
            ((Nat.pow_lt_pow_iff_right hs.one_lt).mp h3)
        · obtain ⟨T', hT'c, hT'card, hT'idx⟩ := exists_isMulCommutative_extension hs hD hc hstuck
          refine Or.inr ⟨T', hT'c, ?_, ?_⟩
          · calc s ^ z * s ^ (t + 1) = s * (s ^ z * s ^ t) := by ring
              _ ≤ s * Nat.card T := Nat.mul_le_mul_left _ hTcard
              _ ≤ Nat.card T' := hT'card
          · calc (Subgroup.centralizer (T' : Set D)).index
                ≤ (Subgroup.centralizer (T : Set D)).index * Nat.card (Subgroup.center D) :=
                  hT'idx
              _ ≤ (s ^ z) ^ t * s ^ z := by rw [hz]; exact Nat.mul_le_mul_right _ hTidx
              _ = (s ^ z) ^ (t + 1) := by ring
  rcases key 4 with h | ⟨T, hT, hTcard, -⟩
  · exact h
  · exact ⟨T, hT, le_trans (Nat.le_mul_of_pos_left _ (pow_pos hs.pos z)) hTcard⟩

end ClassTwo

theorem four_le_pRank_of_classTwo {Y : Type*} [Group Y] [Finite Y] {s : ℕ} (hs : s.Prime)
    {D : Subgroup Y} (hD : ∀ d ∈ D, d ^ s = 1) (hc : commutator D ≤ Subgroup.center D)
    (h5 : s ^ 5 ≤ Nat.card (D ⧸ Subgroup.center D)) : 4 ≤ Open.pRank s D := by
  have := Fact.mk hs
  have hD' : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (hD d d.2)
  obtain ⟨E, hEc, hEcard⟩ := exists_isMulCommutative_pow_four_le_card hs hD' hc h5
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
    (show IsPGroup s E from fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD' e)⟩)
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp (hm ▸ hEcard)).trans
    (CFSG.SectionRank.le_pRank hs.one_lt (Subgroup.map_subtype_le E)
      (CFSG.SectionRank.isElemAbelian_map ⟨hEc, fun e _ => hD' e⟩ D.subtype) ?_)
  rw [Subgroup.card_map_of_injective D.subtype_injective, hm]

end CFSG.AGLEmbeddingD2
