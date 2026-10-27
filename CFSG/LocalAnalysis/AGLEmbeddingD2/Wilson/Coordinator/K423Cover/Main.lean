module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.Passage
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.Heis
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.Split
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.AlphaJ3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover423ON
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Cover423G2
public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofCover

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU)

theorem heis_of_tripleCover {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hLq : IsQuasisimple L) {A : Subgroup H} {c : H}
    (hAm : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hinn : autIn A L ≤ (MulAut.conj : L →* MulAut L).range)
    {S : Type} [Group S] (htc : IsTripleCover L S)
    (hS : ¬ 27 ∣ Nat.card S ∧
      (∀ P : Subgroup S, Nat.card P = 9 → ∃ g : S, ∀ x ∈ P, g * x * g⁻¹ = x⁻¹) ∧
      ∀ P : Subgroup S, Nat.card P = 9 → Subgroup.centralizer (P : Set S) ≤ P) :
    IsHeisCentral ↥(A ⊔ L) ↥L ∧ CFSG.Assembly.IsElemAbelian 3 (autIn L A) ∧
      Nat.card (autIn L A) = 9 := by
  obtain ⟨hZ3, ⟨e⟩⟩ := htc
  obtain ⟨hS27, hSinv, hScent⟩ := hS
  have hZc := map_center_eq_zpowers hZ3 hAm hc3 hAc
  obtain ⟨z, hz, hzc⟩ : ∃ z ∈ Subgroup.center L, (z : H) = c := by
    have hc : c ∈ (Subgroup.center L).map L.subtype := hZc ▸ Subgroup.mem_zpowers c
    obtain ⟨z, hz, hzc⟩ := hc
    exact ⟨z, hz, hzc⟩
  have hcL : c ∈ L := hzc ▸ z.2
  have hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
    have : (⟨c, hcL⟩ : L) = z := Subtype.ext hzc.symm
    rw [this]
    exact hz
  have hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := by
    intro a ha
    have hN : a ∈ Subgroup.normalizer (L : Set H) := le_normalizer_of_normal' A ha
    obtain ⟨l, hl⟩ := hinn (mem_autIn_iff.mpr ⟨a, hN, ha, rfl⟩)
    refine ⟨l, l.2, fun x hx => ?_⟩
    have h1 := congrArg (fun σ : MulAut L => ((σ ⟨x, hx⟩ : L) : H)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [normalizerMonoidHom_apply_coe] at h1
    exact h1.symm
  have hS27' : ¬ 27 ∣ Nat.card (L ⧸ Subgroup.center L) := by
    rwa [Nat.card_congr e.toEquiv]
  have hinv : ∀ P : Subgroup (L ⧸ Subgroup.center L), Nat.card P = 9 →
      ∃ g : L ⧸ Subgroup.center L, ∀ x ∈ P, g * x * g⁻¹ = x⁻¹ := by
    intro P hP
    obtain ⟨g', hg'⟩ := hSinv (P.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, hP])
    refine ⟨e.symm g', fun x hx => e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hg' (e x) ⟨x, hx, rfl⟩
  have hcent : ∀ P : Subgroup (L ⧸ Subgroup.center L), Nat.card P = 9 →
      Subgroup.centralizer (P : Set (L ⧸ Subgroup.center L)) ≤ P := fun P hP =>
    centralizer_le_of_map e (hScent _ (by rw [Subgroup.card_map_of_injective e.injective, hP]))
  exact isHeisCentral_and_autIn hLq.1 hZ3 hAm.prop hA27 (le_normalizer_of_normal' A) hAc hc3
    hcL hcZ hinner hS27' hinv hcent

section Frame


theorem k423CoverFrame_of
    (hJ3 : Census.Karpilovsky.Coordinator.Cover423.AlphaNine
      (Blueprint.NativeSporadic.Carrier .J3))
    (hU43 : Census.Karpilovsky.Coordinator.Cover423.AlphaNine (projSU 4 3 1)) :
    K423CoverFrame := by
  intro H _ _ L _ hLq _ hlist hZ hnsl A c hAm hA27 hc3 hAc hinn Y hY hα
  have hrow : ∀ {S : Type} [Group S], (L ⧸ Subgroup.center L ≃* S) →
      Census.Karpilovsky.Coordinator.Cover423.AlphaNine S → False :=
    fun e hS => false_of_alphaNine hLq hAm.prop hA27 hc3 hAc hinn hY hα e hS
  rcases cover46_cases hlist hLq hZ (fun h => hnsl (Or.inl h)) with
      ⟨-, ⟨e⟩⟩ | htc | htc | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | hG2 | ⟨⟨e⟩⟩
  · exact (hrow e alphaNine_alt6).elim
  · obtain ⟨hH, hEl, h9⟩ := heis_of_tripleCover hLq hAm hA27 hc3 hAc hinn htc
      (rowFacts_alt7 (MulEquiv.refl _))
    exact ⟨hH, Or.inl htc, hEl, h9⟩
  · have : Finite (Blueprint.NativeSporadic.Carrier .M22) :=
      Nat.finite_of_card_ne_zero (by
        show Nat.card Blueprint.NativeSporadic.M22 ≠ 0
        rw [Census.card_m22_eq]
        norm_num)
    obtain ⟨hH, hEl, h9⟩ := heis_of_tripleCover hLq hAm hA27 hc3 hAc hinn htc
      (rowFacts_m22 (S := Blueprint.NativeSporadic.Carrier .M22) (MulEquiv.refl _))
    exact ⟨hH, Or.inr htc, hEl, h9⟩
  · exact (hrow e hJ3).elim
  · exact (hrow e alphaNine_McL).elim
  · exact (hrow e Census.Karpilovsky.ComponentPrimary.alphaNine_ON).elim
  · exact (hrow (MulEquiv.refl _) (Census.Karpilovsky.UniversalCoverMonster.alphaNine_G2 hG2)).elim
  · exact (hrow e hU43).elim


theorem k423CoverFrame_of_u43
    (hU43 : Census.Karpilovsky.Coordinator.Cover423.AlphaNine (projSU 4 3 1)) :
    K423CoverFrame :=
  k423CoverFrame_of alphaNine_J3 hU43

end Frame

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover
