module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveChain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMaxAbstract
public import Certificates.Certificate9555
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveWords

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Certificates
  CFSG.Certificates.Native
open scoped Pointwise

theorem closure_le_stab {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    Subgroup.closure ({G₁, G₂} : Set fi22P) ≤
      MulAction.stabilizer fi22P (finSet 3510 s0Arr.toList) := by
  obtain ⟨⟨hf1, hf2⟩, -⟩ := Certificates.certificate9555 G₁.1 G₂.1 h₁ h₂
  have hs0l : s0Arr.toList = s0List := by simp [s0Arr]
  rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · change G₁.1 • finSet 3510 s0Arr.toList = finSet 3510 s0Arr.toList
    rw [hs0l]
    exact hf1
  · change G₂.1 • finSet 3510 s0Arr.toList = finSet 3510 s0Arr.toList
    rw [hs0l]
    exact hf2

theorem orbit_pieces
    {G₁ G₂ : fi22P} (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    ∃ A B C : Equiv.Perm (Fin 3510), A ∈ fi22P ∧ B ∈ fi22P ∧ C ∈ fi22P ∧
      ∃ E : Fin 4 → Set (Set (Fin 3510)), (∀ j, (E j).Finite) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        (∀ j, E j ⊆ MulAction.orbit (Subgroup.closure ({G₁, G₂} : Set fi22P))
          ((![1, A, B, C] : Fin 4 → Equiv.Perm (Fin 3510)) j • finSet 3510 s0Arr.toList)) ∧
        (∀ j, (E j).ncard = (![1, 1575, 22400, 37800] : Fin 4 → ℕ) j) := by
  obtain ⟨-, hrest⟩ := Certificates.certificate9555 G₁.1 G₂.1 h₁ h₂
  obtain ⟨A, hAP, hA⟩ := exists_rep_evalW (w := [1]) (by decide)
  obtain ⟨B, hBP, hB⟩ := exists_rep_evalW (w := [2]) (by decide)
  obtain ⟨E, hfin, hdisj, hsub, hcard⟩ := hrest A B hA hB
  have hs0l : s0Arr.toList = s0List := by simp [s0Arr]
  have hmap : (Subgroup.closure ({G₁, G₂} : Set fi22P)).map fi22P.subtype =
      Subgroup.closure ({G₁.1, G₂.1} : Set (Equiv.Perm (Fin 3510))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  refine ⟨A, B, B * A, hAP, hBP, mul_mem hBP hAP, E, hfin, hdisj, fun j S hS => ?_, hcard⟩
  obtain ⟨g, hg, rfl⟩ := hsub j S hS
  rw [← hmap] at hg
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
  rw [hs0l]
  exact ⟨⟨m, hm⟩, rfl⟩

theorem harith_pieces : ∀ I : Finset (Fin 4), 0 ∈ I →
    (∑ j ∈ I, (![1, 1575, 22400, 37800] : Fin 4 → ℕ) j) ∣ 61776 → I = {0} ∨ I = Finset.univ := by
  decide

theorem closure_maximal
    {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    ∀ Y : Subgroup fi22P, Subgroup.closure ({G₁, G₂} : Set fi22P) ≤ Y →
      Y = Subgroup.closure ({G₁, G₂} : Set fi22P) ∨ Y = ⊤ := by
  obtain ⟨A, B, C, hAP, hBP, hCP, E, hfin, hdisj, hE, hcard⟩ := orbit_pieces h₁ h₂
  set Γ : Subgroup fi22P := Subgroup.closure ({G₁, G₂} : Set fi22P) with hΓ
  set S₀ : Set (Fin 3510) := finSet 3510 s0Arr.toList with hS₀
  have hΓstab : Γ ≤ MulAction.stabilizer fi22P S₀ := closure_le_stab h₁ h₂
  have hΓcard : 1045094400 ≤ Nat.card Γ := by
    have h1 := card_closure_ge h₁ h₂
    have h2 : Γ.map fi22P.subtype =
        Subgroup.closure ({G₁.1, G₂.1} : Set (Equiv.Perm (Fin 3510))) := by
      rw [hΓ, MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← h2, Subgroup.card_map_of_injective fi22P.subtype_injective] at h1
    exact h1
  have hN : Nat.card fi22P ≤ 61776 * Nat.card Γ := by
    rw [card_fi22P]
    calc 64561751654400 = 61776 * 1045094400 := by norm_num
      _ ≤ 61776 * Nat.card Γ := Nat.mul_le_mul_left _ hΓcard
  have key := maximal_of_orbit_pieces (G := fi22P) (α := Set (Fin 3510)) S₀ Γ hΓstab hN
    (fun j => (![1, A, B, C] : Fin 4 → Equiv.Perm (Fin 3510)) j • S₀) (by simp)
    (by
      intro j
      fin_cases j
      · exact ⟨1, rfl⟩
      · exact ⟨⟨A, hAP⟩, rfl⟩
      · exact ⟨⟨B, hBP⟩, rfl⟩
      · exact ⟨⟨C, hCP⟩, rfl⟩)
    E hE hdisj ![1, 1575, 22400, 37800] hcard hfin rfl (by simp [Fin.sum_univ_four])
    harith_pieces
  exact key.2

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
