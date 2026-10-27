module

public import CFSG.GroupTheory.SimpleNormalHom
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

open Subgroup Equiv Equiv.Perm

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem ne_top_of_two_pow_seven_dvd_of_mulEquiv_alternatingGroup_nine {X : Type*} [Group X]
    (T : Subgroup X) (e : ↥T ≃* alternatingGroup (Fin 9)) (hX : 2 ^ 7 ∣ Nat.card X) :
    T ≠ ⊤ := by
  rintro rfl
  have h : Nat.card X = 181440 := by
    rw [← Subgroup.card_top (G := X), Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    norm_num [Nat.factorial]
  rw [h] at hX
  norm_num at hX

theorem nonempty_mulEquiv_perm_fin_nine_of_mulEquiv_alternatingGroup {X : Type*} [Group X]
    [Finite X] (T : Subgroup X) [T.Normal] (e : ↥T ≃* alternatingGroup (Fin 9))
    (hC : centralizer (T : Set X) = ⊥) (hT : T ≠ ⊤) : Nonempty (X ≃* Perm (Fin 9)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥T := e.isSimpleGroup
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  let conjEquiv : Perm (Fin 9) ≃* MulAut (alternatingGroup (Fin 9)) :=
    MulEquiv.ofBijective
      (MulAut.conjNormal : Perm (Fin 9) →* MulAut (alternatingGroup (Fin 9))) hbij
  let aut : X →* MulAut (alternatingGroup (Fin 9)) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  let ψ : X →* Perm (Fin 9) := conjEquiv.symm.toMonoidHom.comp aut
  have hψ : ∀ x, conjEquiv (ψ x) = aut x := fun x => conjEquiv.apply_symm_apply (aut x)
  have hφ : ∃ t ∈ T, ψ t ≠ 1 := by
    obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
      obtain ⟨⟨t, ht⟩, hne⟩ := exists_ne (1 : ↥T)
      exact ⟨t, ht, fun h => hne (Subtype.ext h)⟩
    refine ⟨t, htT, fun h1 => ht1 ?_⟩
    have h2 : aut t = 1 := by rw [← hψ, h1, map_one]
    have h3 : MulAut.conjNormal (H := T) t = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one]
      exact h2
    have h4 : t ∈ centralizer (T : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h5 := congrArg (fun φ : MulAut ↥T => ((φ ⟨s, hs⟩ : ↥T) : X)) h3
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h5
      exact (mul_inv_eq_iff_eq_mul.1 h5).symm
    rw [hC, Subgroup.mem_bot] at h4
    exact h4
  have hcard : Nat.card (Perm (Fin 9)) ≤ 2 * Nat.card ↥T := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  exact ⟨MulEquiv.ofBijective ψ (ψ.bijective_of_simple_normal T hC hT hφ hcard)⟩

end CFSG.EvenSporadicStandard.TwoHS.GH312
