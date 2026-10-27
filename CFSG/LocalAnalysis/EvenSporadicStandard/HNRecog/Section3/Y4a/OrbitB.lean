module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.A5Index

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_orbit_size {G : Type} [Group G] [Finite G] {Y M : Subgroup G}
    (ψ : ↥Y →* alternatingGroup (Fin 5)) (hψ : Function.Surjective ψ)
    (hker : ∀ l : ↥Y, ψ l = 1 ↔ (l : G) ∈ M) (hMY : M ≤ Y)
    (hMab : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ = m₂ * m₁) {c : G} (hc : c ∈ M) :
    Y ≤ Gx c ∨ 5 * Nat.card ↥(Y ⊓ Gx c) ≤ Nat.card ↥Y := by
  classical
  set S : Subgroup ↥Y := (Y ⊓ Gx c).subgroupOf Y with hS
  have hkerS : ψ.ker ≤ S := by
    intro l hl
    rw [hS, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨l.2, ?_⟩
    rw [mem_Gx]
    exact (hMab (l : G) ((hker l).mp (MonoidHom.mem_ker.mp hl)) c hc).symm
  have hcomap : S = (S.map ψ).comap ψ := (Subgroup.comap_map_eq_self hkerS).symm
  have hindex : S.index = (S.map ψ).index := by
    conv_lhs => rw [hcomap]
    exact Subgroup.index_comap_of_surjective (H := S.map ψ) hψ
  have hcardS : Nat.card ↥S = Nat.card ↥(Y ⊓ Gx c) := by
    rw [hS]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ Gx c ≤ Y)).toEquiv
  by_cases hle : (S.map ψ).index ≤ 4
  · left
    have htop : S.map ψ = ⊤ := y4a_eq_top_of_index_le_four hle
    have hStop : S = ⊤ := by rw [hcomap, htop, Subgroup.comap_top]
    intro y hy
    have hyS : (⟨y, hy⟩ : ↥Y) ∈ S := by rw [hStop]; exact Subgroup.mem_top _
    rw [hS, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hyS
    exact hyS.2
  · right
    have h5 : 5 ≤ S.index := by omega
    have hmul : Nat.card ↥S * S.index = Nat.card ↥Y := Subgroup.card_mul_index S
    calc 5 * Nat.card ↥(Y ⊓ Gx c) = 5 * Nat.card ↥S := by rw [hcardS]
      _ ≤ S.index * Nat.card ↥S := Nat.mul_le_mul_right _ h5
      _ = Nat.card ↥S * S.index := by rw [mul_comm]
      _ = Nat.card ↥Y := hmul

theorem y4a_isConjOrbit_B {G : Type} [Group G] [Finite G] {Y M : Subgroup G} {A B : Set G}
    (hM : Nat.card ↥M = 16) (hBM : B ⊆ M) (h1B : (1 : G) ∉ B)
    (hcover : ∀ m ∈ M, m ≠ 1 → m ∈ A ∨ m ∈ B) (hB : Nat.card ↥B = 5)
    (hBinv : ∀ l ∈ Y, ∀ c ∈ B, l * c * l⁻¹ ∈ B) (hAnf : ∀ c ∈ A, ¬ Y ≤ Gx c)
    (hsize : ∀ c ∈ B, Y ≤ Gx c ∨ 5 * Nat.card ↥(Y ⊓ Gx c) ≤ Nat.card ↥Y) :
    IsConjOrbit Y B := by
  classical
  by_cases hcase : ∃ c ∈ B, ¬ Y ≤ Gx c
  · obtain ⟨c, hcB, hcnot⟩ := hcase
    have hsize_c : 5 * Nat.card ↥(Y ⊓ Gx c) ≤ Nat.card ↥Y :=
      (hsize c hcB).resolve_left hcnot
    let O : Set G := {d | ∃ l ∈ Y, l * c * l⁻¹ = d}
    have hcO : c ∈ O := ⟨1, Y.one_mem, by simp⟩
    have hO : IsConjOrbit Y O := by
      refine ⟨?_, ?_, ?_⟩
      · rintro k hk d ⟨l, hl, rfl⟩
        exact ⟨k * l, Y.mul_mem hk hl, by group⟩
      · exact ⟨c, hcO⟩
      · rintro d ⟨l, hl, rfl⟩ d' ⟨l', hl', rfl⟩
        exact ⟨l' * l⁻¹, Y.mul_mem hl' (Y.inv_mem hl), by group⟩
    have hOS := IsConjOrbit.card_mul_card_stab hO hcO
    have hn : 0 < Nat.card ↥(Y ⊓ Gx c) := by
      rw [Nat.card_pos_iff]
      exact ⟨⟨1, Subgroup.mem_inf.mpr ⟨Y.one_mem, (Gx c).one_mem⟩⟩, inferInstance⟩
    have h5le : 5 ≤ Nat.card ↥O := by
      rw [← hOS] at hsize_c
      exact le_of_mul_le_mul_right hsize_c hn
    have hOB : O ⊆ B := by
      rintro d ⟨l, hl, rfl⟩
      exact hBinv l hl c hcB
    have hcardOle : Nat.card ↥O ≤ Nat.card ↥B := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hOB
    have hcardO : Nat.card ↥O = 5 := by omega
    have hOeqB : O = B := by
      apply Set.eq_of_subset_of_ncard_le hOB
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      omega
    rw [hOeqB] at hO
    exact hO
  · exfalso
    push_neg at hcase
    set F : Subgroup G := M ⊓ Subgroup.centralizer (Y : Set G) with hF
    have hFset : (F : Set G) = insert 1 B := by
      ext m
      constructor
      · intro hm
        simp only [hF, Subgroup.mem_inf] at hm
        obtain ⟨hmM, hmC⟩ := hm
        by_cases hm1 : m = 1
        · rw [hm1]; exact Set.mem_insert _ _
        · rcases hcover m hmM hm1 with hmA | hmB
          · exfalso
            exact hAnf m hmA (fun y hy => by
              rw [mem_Gx]
              exact (Subgroup.mem_centralizer_iff.mp hmC y hy).symm)
          · exact Set.mem_insert_of_mem _ hmB
      · intro hm
        rw [Set.mem_insert_iff] at hm
        rw [hF]
        rcases hm with rfl | hmB
        · exact Subgroup.mem_inf.mpr ⟨M.one_mem, by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            simp⟩
        · exact Subgroup.mem_inf.mpr ⟨hBM hmB, by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact (mem_Gx.mp (hcase m hmB hy)).symm⟩
    have hF6 : Nat.card ↥F = 6 := by
      have h1 : Nat.card ↥F = Nat.card (insert 1 B : Set G) :=
        Nat.card_congr (Set.equivOfEq hFset)
      rw [h1, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1B]
      have hBc : B.ncard = 5 := by rw [← Nat.card_coe_set_eq]; exact hB
      omega
    have hFM : F ≤ M := by rw [hF]; exact inf_le_left
    have hdvd : Nat.card ↥F ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hFM
    rw [hF6, hM] at hdvd
    norm_num at hdvd

end CFSG.EvenSporadicStandard.HNRecog.Section3
