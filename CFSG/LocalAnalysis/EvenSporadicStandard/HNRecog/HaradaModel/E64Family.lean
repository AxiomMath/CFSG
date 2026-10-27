module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

theorem mem_family_of_isElemAbelian {G : Type*} [Group G] [Finite G] {S V : Subgroup G}
    {𝓛 : Set (Subgroup G)} (hV : V ∈ 𝓛)
    (hext : ∀ B ∈ 𝓛, ∀ s ∈ S, s ^ 2 = 1 → s ∉ B → (∀ b ∈ B, s * b = b * s) →
      ∃ B' ∈ 𝓛, B ≤ B' ∧ s ∈ B' ∧ Nat.card B' = 2 * Nat.card B)
    {B : Subgroup G} (hBS : B ≤ S) (hBe : CFSG.Open.IsElemAbelian 2 B) (hVB : V ≤ B) :
    B ∈ 𝓛 := by
  classical
  have key : ∀ n : ℕ, ∀ B : Subgroup G, Nat.card B = n → B ≤ S →
      CFSG.Open.IsElemAbelian 2 B → V ≤ B → B ∈ 𝓛 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hBn hBS hBe hVB
      by_cases hBV : B = V
      · rw [hBV]; exact hV
      · have hVBlt : V < B := lt_of_le_of_ne hVB (Ne.symm hBV)
        haveI : Fintype G := Fintype.ofFinite G
        haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
        have hsne : ({C : Subgroup G | V ≤ C ∧ C < B} : Set (Subgroup G)).Nonempty :=
          ⟨V, le_rfl, hVBlt⟩
        obtain ⟨C, hCs, hCmax⟩ := (Set.toFinite _).exists_maximal hsne
        obtain ⟨hVC, hCBlt⟩ := hCs
        have hCB : C ≤ B := hCBlt.le
        have hCS : C ≤ S := hCB.trans hBS
        have hClt : Nat.card C < n := by
          rw [← hBn]; exact Subgroup.card_lt_of_lt hCBlt
        haveI : IsMulCommutative B := hBe.1
        have hCe : CFSG.Open.IsElemAbelian 2 C := by
          constructor
          · refine ⟨⟨fun x y => ?_⟩⟩
            apply Subtype.ext
            have hxy := congrArg Subtype.val
              (mul_comm' (⟨x, hCB x.2⟩ : B) (⟨y, hCB y.2⟩ : B))
            simpa using hxy
          · intro x hx
            exact hBe.2 x (hCB hx)
        have hCl : C ∈ 𝓛 := ih (Nat.card C) hClt C rfl hCS hCe hVC
        obtain ⟨s, hsB, hsnC⟩ := SetLike.exists_of_lt hCBlt
        have hsS : s ∈ S := hBS hsB
        have hs2 : s ^ 2 = 1 := hBe.2 s hsB
        have hcomm : ∀ b ∈ C, s * b = b * s := by
          intro b hb
          have hsb := congrArg Subtype.val
            (mul_comm' (⟨s, hsB⟩ : B) (⟨b, hCB hb⟩ : B))
          simpa using hsb
        obtain ⟨B', hB'l, hCB', hsB', hcardB'⟩ := hext C hCl s hsS hs2 hsnC hcomm
        let D : Subgroup G := C ⊔ Subgroup.zpowers s
        have hCDle : C ≤ D := le_sup_left
        have hDB : D ≤ B := sup_le hCB (Subgroup.zpowers_le.2 hsB)
        have hDB' : D ≤ B' := sup_le hCB' (Subgroup.zpowers_le.2 hsB')
        have hCDlt : C < D := by
          rw [lt_iff_le_and_ne]
          refine ⟨hCDle, fun hCD => hsnC ?_⟩
          have hsD : s ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
          exact hCD.symm ▸ hsD
        have hcardCDlt : Nat.card C < Nat.card D := Subgroup.card_lt_of_lt hCDlt
        have hdiv : Nat.card C ∣ Nat.card D := Subgroup.card_dvd_of_le hCDle
        haveI : Nonempty C := ⟨⟨1, C.one_mem⟩⟩
        have hposC : 0 < Nat.card C := Nat.card_pos
        obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd hdiv
        have hq0 : q ≠ 0 := by
          rintro rfl
          simp only [zero_mul] at hq
          omega
        have hq1 : q ≠ 1 := by
          rintro rfl
          simp only [one_mul] at hq
          omega
        have hq2 : 2 ≤ q := by omega
        have hge : 2 * Nat.card C ≤ Nat.card D := by
          rw [hq]
          exact Nat.mul_le_mul_right _ hq2
        have hD_eq : D = B' :=
          Subgroup.eq_of_le_of_card_ge hDB' (by rw [hcardB']; exact hge)
        have hB'B : B' ≤ B := by
          rw [hD_eq] at hDB
          exact hDB
        by_cases hB'Blt : B' < B
        · exfalso
          have hB's : B' ∈ ({C : Subgroup G | V ≤ C ∧ C < B} : Set (Subgroup G)) :=
            ⟨hVC.trans hCB', hB'Blt⟩
          have hB'C : B' ≤ C := hCmax hB's hCB'
          have hCB'lt : C < B' :=
            lt_of_le_of_ne hCB' (fun h => hsnC (h.symm ▸ hsB'))
          exact absurd hB'C (not_le_of_gt hCB'lt)
        · have hB'eq : B' = B := le_antisymm hB'B (by
            by_contra h
            exact hB'Blt (lt_iff_le_not_ge.mpr ⟨hB'B, h⟩))
          rwa [hB'eq] at hB'l
  exact key (Nat.card B) B rfl hBS hBe hVB

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
