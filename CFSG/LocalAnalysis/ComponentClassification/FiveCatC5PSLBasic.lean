module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGraph

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5PSL

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof.X10Lin

@[expose] def A5Shape (n f : ℕ) (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5)) →
    (∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z * z = 1 → z = 1) →
    (∀ L' : Subgroup G, IsComponent L' → L' = L) → (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1)

theorem A5Shape.of_mulEquiv {n f : ℕ} {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : A5Shape n f H) : A5Shape n f G := by
  intro L hL hA hz hu
  refine h (L.map e.toMonoidHom) (LocalCores.isComponent_map_mulEquiv e hL) ?_ ?_ ?_
  · obtain ⟨eA⟩ := hA
    exact ⟨(QuotientGroup.congr _ _ (L.equivMapOfInjective e.toMonoidHom e.injective)
      (Subgroup.map_center_eq _)).symm.trans eA⟩
  · intro z hz' hc hzz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.1 hz'
    have h1 : z₀ = 1 := hz z₀ hz₀
      (fun y hy => e.injective (by
        simpa using hc (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)))
      (e.injective (by simpa using hzz))
    rw [h1]
    exact map_one e
  · intro L' hL'
    have h2 : L'.map e.symm.toMonoidHom = L :=
      hu _ (LocalCores.isComponent_map_mulEquiv e.symm hL')
    calc L' = (L'.map e.symm.toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_map]
          have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
            ext
            simp
          rw [this, Subgroup.map_id]
      _ = L.map e.toMonoidHom := by rw [h2]

private theorem nat_card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem factorization_sixty : (60 : ℕ).factorization 5 = 1 := by
  have h : (60 : ℕ) = 5 * 12 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply]
  have h5 : (5 : ℕ).factorization 5 = 1 := by
    rw [Nat.Prime.factorization_self (by norm_num)]
  have h12 : (12 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h5, h12]

private theorem eq_two_of_tri_eq_one {m : ℕ} (hm : 2 ≤ m) (h : m * (m - 1) / 2 = 1) : m = 2 := by
  by_contra hne
  have h3 : 3 ≤ m := by omega
  have : 6 ≤ m * (m - 1) := by
    calc 6 = 3 * 2 := by norm_num
      _ ≤ m * (m - 1) := Nat.mul_le_mul h3 (by omega)
  omega

theorem eq_psl_two_one_of_a5 {Y : Type} [Group Y] {t : StatedLieTag} {m e : ℕ}
    (ht : IsClassicalTag t) (hadm : StatedLieAdmissible t m 5 e)
    (h : Blueprint.LieModel Y t m 5 e)
    (hY : Nonempty (Y ≃* alternatingGroup (Fin 5))) : t = .PSL ∧ m = 2 ∧ e = 1 := by
  obtain ⟨eY⟩ := hY
  have hcard : Nat.card Y = 60 := by
    rw [Nat.card_congr eY.toEquiv]
    exact nat_card_alt_five
  have hm0 : m ≠ 0 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have : 4 ≤ m := hadm.2.2; omega
    · exact fun h0 => by have : 4 ≤ m := hadm.2.2; omega
  obtain ⟨-, hv⟩ := lieOrder_of_lieModel_classical ht (by norm_num : (5 : ℕ) ≠ 2) hm0 h
  rw [hcard, factorization_sixty] at hv
  have hmul : lieSylowExponent t m * e = 1 := hv.symm
  have hN : lieSylowExponent t m = 1 := Nat.eq_one_of_mul_eq_one_right hmul
  have hef : e = 1 := Nat.eq_one_of_mul_eq_one_left hmul
  have hPSL : t = .PSL ∧ m = 2 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, eq_two_of_tri_eq_one hadm.2.2.1 hN⟩
    · exfalso
      have hm : 3 ≤ m := hadm.2.2.1
      have h6 : m * (m - 1) / 2 = 1 := hN
      have := eq_two_of_tri_eq_one (by omega) h6
      omega
    · exfalso
      have hm : 2 ≤ m := hadm.2.2.1
      have h1 : m ^ 2 = 1 := hN
      nlinarith
    · exfalso
      have hm : 3 ≤ m := hadm.2.2.1
      have h1 : m ^ 2 = 1 := hN
      nlinarith
    · exfalso
      have hm : 4 ≤ m := hadm.2.2
      have h1 : m * (m - 1) = 1 := hN
      have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
      omega
    · exfalso
      have hm : 4 ≤ m := hadm.2.2
      have h1 : m * (m - 1) = 1 := hN
      have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
      omega
  exact ⟨hPSL.1, hPSL.2, hef⟩

theorem tag_of_mem_linInnerTuples {t : StatedLieTag} {m e n f : ℕ}
    (h : (t, m, e) ∈ linInnerTuples n f) : t = .PSL := by
  rcases h with ⟨k, -, -, -, h⟩ | ⟨-, h⟩ <;> exact (Prod.mk.inj h).1

theorem not_mem_linInnerTuples {n f : ℕ}
    (h : ((.PSL : StatedLieTag), 2, 1) ∈ linInnerTuples n f) : False := by
  rcases h with ⟨k, -, hk3, -, h⟩ | ⟨-, h⟩
  · have h2 := (Prod.mk.inj (Prod.mk.inj h).2).1
    omega
  · have h2 := (Prod.mk.inj (Prod.mk.inj h).2).2
    omega

theorem mem_graphTuples_psl_two_one {n f : ℕ}
    (h : ((.PSL : StatedLieTag), 2, 1) ∈ graphTuples n f) : (n = 3 ∧ f = 1) ∨ (n = 4 ∧ f = 1) := by
  rcases h with (⟨h3, h⟩ | ⟨h4, h | h⟩ | ⟨h5, h⟩ | ⟨h6, h | h⟩ | ⟨h7, -, h⟩ | ⟨h8, -, h | h⟩) |
    ⟨-, h⟩
  · have := (Prod.mk.inj (Prod.mk.inj h).2).2
    exact Or.inl ⟨h3, by omega⟩
  · have := (Prod.mk.inj (Prod.mk.inj h).2).2
    exact Or.inr ⟨h4, by omega⟩
  · have := (Prod.mk.inj (Prod.mk.inj h).2).2
    omega
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · have := (Prod.mk.inj (Prod.mk.inj h).2).1
    omega
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.C5PSL
