module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThreeHolds
public import CFSG.GroupTheory.ElemAbelianRank
import all CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem card_le_of_isElemAbelian_E6_three (h3 : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .E6 K)} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 := by
  classical
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  obtain ⟨A₀, ι₀, hA₀, hA₀4, hA₀SC, hι₀, hrange, -⟩ :=
    CFSG.StandardType.ExcFrames.e6ThreeRefFrame_holds h3
  have hA₀card : Nat.card A₀ = 3 ^ 4 := by
    rw [← hrange, ← Subgroup.map_top ι₀, Subgroup.card_map_of_injective hι₀,
      Subgroup.card_top, Nat.card_eq_fintype_card]
    change Fintype.card (Fin 4 → ZMod 3) = 3 ^ 4
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  obtain ⟨B, -, hB, hBcard⟩ :=
    CFSG.SectionRank.exists_pRank (G := adjointGroup .E6 K) (p := 3) (by norm_num) ⊤
  have hmax : ∀ E' : Subgroup (adjointGroup .E6 K), IsElemAbelian 3 E' →
      Nat.card E' ≤ Nat.card B := by
    intro E' hE'
    have hE'card : Nat.card E' = 3 ^ CFSG.Open.pRank 3 E' :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hE'
    have hle : CFSG.Open.pRank 3 E' ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .E6 K)) :=
      CFSG.SectionRank.le_pRank (G := adjointGroup .E6 K) (p := 3) (by norm_num)
        (le_top : E' ≤ ⊤) hE' hE'card
    calc Nat.card E' = 3 ^ CFSG.Open.pRank 3 E' := hE'card
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .E6 K)) :=
        Nat.pow_le_pow_right (by norm_num) hle
      _ = Nat.card B := hBcard.symm
  have hBsc : ∀ c ∈ Subgroup.centralizer (B : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ B := by
    intro c hc hc3
    exact CFSG.StandardType.mem_of_mem_centralizer_of_maximal hB hmax hc hc3
  have hB4 : 3 ^ 4 ≤ Nat.card B := by
    rw [← hA₀card]
    exact hmax A₀ hA₀
  obtain ⟨c, hc⟩ :=
    CFSG.StandardType.ExcFrames.e6ThreeSCUnique_holds h3 hA₀ hA₀card.ge hA₀SC hB hB4 hBsc
  have hBcard' : Nat.card B = 3 ^ 4 := by
    rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective, hA₀card]
  exact (hmax E hE).trans hBcard'.le

theorem sc_of_card_eq_E6_three (h3 : 3 ∣ Nat.card K + 1)
    {A : Subgroup (adjointGroup .E6 K)} (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 4) :
    ∀ c ∈ Subgroup.centralizer (A : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ A := by
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  intro c hc hc3
  exact CFSG.StandardType.mem_of_mem_centralizer_of_maximal hA
    (fun E hE => (card_le_of_isElemAbelian_E6_three h3 hE).trans hAcard.ge) hc hc3

theorem exists_conj_eq_of_card_E6_three (h3 : 3 ∣ Nat.card K + 1)
    {A A₀ : Subgroup (adjointGroup .E6 K)} (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 4)
    (hA₀ : IsElemAbelian 3 A₀) (hA₀card : Nat.card A₀ = 3 ^ 4) :
    ∃ g : adjointGroup .E6 K, A.map (MulAut.conj g).toMonoidHom = A₀ := by
  obtain ⟨c, hc⟩ := CFSG.StandardType.ExcFrames.e6ThreeSCUnique_holds h3 hA hAcard.ge
    (sc_of_card_eq_E6_three h3 hA hAcard) hA₀ hA₀card.ge (sc_of_card_eq_E6_three h3 hA₀ hA₀card)
  exact ⟨c, hc.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
