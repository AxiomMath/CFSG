module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma map_closure_singleton (x : Γ₁) :
    (closure {x}).map f = closure {f x} := by
  rw [MonoidHom.map_closure, Set.image_singleton]

private lemma map_image_insert_sdiff (hf : Function.Injective f) (A B : Subgroup Γ₁)
    (S : Set (Subgroup Γ₁)) :
    Subgroup.map f '' (insert A S \ {B}) =
      insert (A.map f) (Subgroup.map f '' S) \ {B.map f} := by
  rw [Set.image_sdiff (Subgroup.map_injective hf), Set.image_insert_eq, Set.image_singleton]

private lemma isMulCommutative_map_iff (hf : Function.Injective f) (U : Subgroup Γ₁) :
    IsMulCommutative (U.map f) ↔ IsMulCommutative U := by
  constructor
  · intro h
    rw [isMulCommutative_iff] at h ⊢
    intro a b
    apply Subtype.ext
    apply hf
    show f ((a : Γ₁) * b) = f ((b : Γ₁) * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (h ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
  · intro _
    infer_instance

theorem f15b_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F15b ↔ gf.F15b := by
  have hS : (gf.map f).S = gf.S.map f := GFrame.map_S f gf
  have hSσ : (gf.map f).Sσ = gf.Sσ.map f := GFrame.map_Sσ f gf
  have hF : (gf.map f).F = gf.F.map f := GFrame.map_F f gf
  have hσ : (gf.map f).σ = f gf.σ := rfl
  have hjoin : (gf.map f).F ⊔ closure {(gf.map f).σ} = (gf.F ⊔ closure {gf.σ}).map f := by
    rw [hF, hσ, ← map_closure_singleton, ← Subgroup.map_sup]
  simp only [GFrame.F15b]
  refine and_congr (and_congr ?_ (and_congr ?_ ?_)) (and_congr ?_ (and_congr ?_ ?_))
  · rw [hSσ, hjoin, thompsonRank_map hf]
    exact (Subgroup.map_injective hf).eq_iff
  · rw [hjoin]
    exact isE_map hf 4 (gf.F ⊔ closure {gf.σ})
  · rw [hSσ, hS]
    simp only [maxElemAbelian_map hf]
    rw [hjoin, hF, ← map_image_insert_sdiff hf]
    exact (Set.image_injective.mpr (Subgroup.map_injective hf)).eq_iff
  · constructor
    · intro h U hU hcomm
      have hU' : U.map f ≤ (gf.map f).Sσ := by
        rw [hSσ]
        exact Subgroup.map_mono hU
      have hcomm' : IsMulCommutative (U.map f) := inferInstance
      have hcard : Nat.card U = Nat.card (U.map f) := (Subgroup.card_map_of_injective hf).symm
      rw [hcard]
      exact h (U.map f) hU' hcomm'
    · intro h U hU hcomm
      have hU' : U ≤ gf.Sσ.map f := by
        rw [hSσ] at hU
        exact hU
      obtain ⟨U₁, hU₁, hmap⟩ := exists_eq_map_of_le hf hU'
      have hcomm' : IsMulCommutative (U₁.map f) := by
        rw [hmap]
        exact hcomm
      have hcomm₁ : IsMulCommutative U₁ := (isMulCommutative_map_iff hf U₁).mp hcomm'
      have hcard : Nat.card U = Nat.card U₁ := by
        rw [← hmap]
        exact Subgroup.card_map_of_injective hf
      rw [hcard]
      exact h U₁ hU₁ hcomm₁
  · rw [hSσ, pRank_map hf]
  · rw [hSσ, sectionalTwoRank_map hf]

end CFSG.OddStandard.HigherRank.YamadaG23
