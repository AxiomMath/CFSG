module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticElementaryTwoRank
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

theorem gomiOdd_card_le_four_statedSp {k : Type} [Field k] [Finite k] (hk : (2 : k) ≠ 0)
    (H : Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 2 k)) (hH : ∀ h ∈ H, h * h = 1) :
    Nat.card H ≤ 4 := by
  set V := Fin 2 ⊕ Fin 2 → k
  let ψ : CFSG.Assembly.LowTwoRank.StatedSp 2 k →* (V ≃ₗ[k] V) :=
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V)).toMonoidHom.comp
      (CFSG.Assembly.LowTwoRank.StatedSp 2 k).subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V)).injective h)
  have hψapp : ∀ g x, ψ g x =
      Matrix.mulVec ((g : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) x :=
    fun g x => rfl
  have hRB : H.map ψ ≤ TauCeti.BilinForm.isometryGroup
      (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm k 2) := by
    rintro _ ⟨g, -, rfl⟩
    refine TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => ?_
    rw [hψapp, hψapp]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_mulVec g x y
  have hR2 : ∀ r ∈ H.map ψ, r * r = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, hH g hg, map_one]
  have : Finite (H.map ψ) := Finite.of_surjective _ (H.equivMapOfInjective ψ hψ).surjective
  have hle := CFSG.RankThree.Classical.card_le_two_pow_of_symplectic_elementary_two hk
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard
    (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm k 2)
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (H.map ψ) hRB hR2
  rw [Subgroup.card_map_of_injective hψ] at hle
  norm_num at hle
  exact hle

theorem gomiOdd_card_le_four_of_prod {A B : Type*} [Group A] [Group B] (zA : A) (zB : B)
    (hA : ∀ a : A, a * a = 1 → a = 1 ∨ a = zA) (hB : ∀ b : B, b * b = 1 → b = 1 ∨ b = zB)
    (W : Subgroup (A × B)) (hW : ∀ w ∈ W, w * w = 1) : Nat.card W ≤ 4 := by
  have hsub : (W : Set (A × B)) ⊆ ({1, zA} : Set A) ×ˢ ({1, zB} : Set B) := by
    rintro ⟨a, b⟩ hw
    have h := hW _ hw
    have h1 : a * a = 1 := congrArg Prod.fst h
    have h2 : b * b = 1 := congrArg Prod.snd h
    refine Set.mk_mem_prod ?_ ?_
    · rcases hA a h1 with ha | ha <;> simp [ha]
    · rcases hB b h2 with hb | hb <;> simp [hb]
  have hcard : Nat.card W = (W : Set (A × B)).ncard := Nat.card_coe_set_eq _
  have hA2 : ({1, zA} : Set A).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : A) {zA}
    rw [Set.ncard_singleton] at this
    omega
  have hB2 : ({1, zB} : Set B).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : B) {zB}
    rw [Set.ncard_singleton] at this
    omega
  have hle : (W : Set (A × B)).ncard ≤ (({1, zA} : Set A) ×ˢ ({1, zB} : Set B)).ncard :=
    Set.ncard_le_ncard hsub
  rw [Set.ncard_prod] at hle
  rw [hcard]
  have hmul : ({1, zA} : Set A).ncard * ({1, zB} : Set B).ncard ≤ 2 * 2 :=
    Nat.mul_le_mul hA2 hB2
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
