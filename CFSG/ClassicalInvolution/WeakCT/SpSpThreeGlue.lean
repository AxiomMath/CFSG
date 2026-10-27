module

public import CFSG.ClassicalInvolution.WeakCT.SpSpChartsTwo
public import CFSG.ClassicalInvolution.WeakCT.SpSpGlue
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock spEmbed range_longBlock
  range_spEmbed coords spEmbed_comp_shortBlock_of_injective spEmbed_longBlock)

theorem range_comp_longBlock_eq_range_comp_spEmbed {n : ℕ} {F : Type} [Field F] {G : Type}
    [Group G] (κ : StatedSp n F →* G) (k : Fin n) :
    (κ.comp (longBlock F n k)).range =
      (κ.comp (spEmbed (fun _ : Fin 1 => k) (Function.injective_of_subsingleton _))).range := by
  rw [MonoidHom.range_comp, MonoidHom.range_comp, range_longBlock, range_spEmbed]
  congr 2
  ext x
  rcases x with x | x <;> simp [coords, eq_comm]

theorem weakCT_symplectic_two_of_three_overlaps {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2) {G : Type} [Group G]
    {κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G} (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂) (hκ₃ : Function.Injective κ₃)
    (hov₁₂ : (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range)
    (hplane₁₂ : ∀ j : Fin (s + 1), (κ₁.comp (longBlock F (s + 2) j.succ)).range =
      (κ₂.comp (longBlock F (s + 2) j.castSucc)).range)
    (hcross₁₂ : ∀ a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a)
    (hov₂₃ : (κ₂.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
      (κ₃.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range)
    (hplane₂₃ : ∀ j : Fin (s + 1), (κ₂.comp (longBlock F (s + 2) j.succ)).range =
      (κ₃.comp (longBlock F (s + 2) j.castSucc)).range)
    (hcross₂₃ : ∀ a ∈ (κ₂.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₃.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a)
    (hcross₁₃ : ∀ a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₃.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a) :
    ∃ Ψ : StatedSp (s + 4) F →* G, Ψ.ker ≤ Subgroup.center (StatedSp (s + 4) F) ∧
      Ψ.range = κ₁.range ⊔ κ₂.range ⊔ κ₃.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hF])
  obtain ⟨κ₂', hκ₂', hr₂, hag₁₂, hlong₁₂, hc₁₂, -, hpres₂⟩ :=
    exists_spSpCharts_of_overlap_of_planes hs hκ₁ hκ₂ hov₁₂ hplane₁₂ hcross₁₂
  have hlb₂ : ∀ k, (κ₂'.comp (longBlock F (s + 2) k)).range =
      (κ₂.comp (longBlock F (s + 2) k)).range := fun k => by
    rw [range_comp_longBlock_eq_range_comp_spEmbed, range_comp_longBlock_eq_range_comp_spEmbed,
      hpres₂]
  obtain ⟨κ₃', hκ₃', hr₃, hag₂₃, hlong₂₃, hc₂₃s, hc₂₃l, hpres₃⟩ :=
    exists_spSpCharts_of_overlap_of_planes hs hκ₂' hκ₃ ((hpres₂ _ _).trans hov₂₃)
      (fun j => (hlb₂ _).trans (hplane₂₃ j)) (by rw [hpres₂]; exact hcross₂₃)
  have hfirst : ∀ a ∈ (κ₁.comp (shortBlock F
      (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range := by
    rintro _ ⟨z, rfl⟩
    refine ⟨shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) z, ?_⟩
    simp only [MonoidHom.comp_apply]
    exact congrArg κ₁ (DFunLike.congr_fun
      (spEmbed_comp_shortBlock_of_injective (Fin.castLE_injective (Nat.le_add_left 2 s))
        (zero_ne_one : (0 : Fin 2) ≠ 1)) z)
  have hlastS : ∀ b ∈ (κ₃'.comp (shortBlock F
      (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
      b ∈ (κ₃.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range := by
    rintro _ ⟨z, rfl⟩
    rw [← hpres₃]
    refine ⟨shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) z, ?_⟩
    simp only [MonoidHom.comp_apply]
    exact congrArg κ₃' (DFunLike.congr_fun
      (spEmbed_comp_shortBlock_of_injective (Fin.natAdd_injective 2 s)
        (zero_ne_one : (0 : Fin 2) ≠ 1)) z)
  have hlastL : ∀ b ∈ (κ₃'.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range,
      b ∈ (κ₃.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range := by
    rintro _ ⟨z, rfl⟩
    rw [← hpres₃]
    exact ⟨longBlock F 2 1 z, congrArg κ₃' (spEmbed_longBlock (Fin.natAdd_injective 2 s) 1 z)⟩
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_two_of_three_spSpCharts hs hF κ₁ κ₂' κ₃' hκ₁
    hκ₂' hκ₃' hag₁₂ hlong₁₂ hag₂₃ hlong₂₃ hc₁₂
    (fun a ha b hb => hcross₁₃ a (hfirst a ha) b (hlastS b hb))
    (fun a ha b hb => hcross₁₃ a (hfirst a ha) b (hlastL b hb)) hc₂₃s hc₂₃l
  exact ⟨Ψ, hker, by rw [hrange, hr₂, hr₃]⟩

end CFSG.ClassicalInvolution.WeakCT

end
