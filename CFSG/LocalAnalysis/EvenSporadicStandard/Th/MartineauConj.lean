module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Martineau
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndGen
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (W : ThLocalIn L S A B z)

include W

theorem ThLocalIn.martineau_conj (β : G → G → G)
    (hβA : ∀ a ∈ A, ∀ a' ∈ A, β a a' ∈ A)
    (hβl : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a' ∈ A, β (a₁ * a₂) a' = β a₁ a' * β a₂ a')
    (hβr : ∀ a ∈ A, ∀ a₁ ∈ A, ∀ a₂ ∈ A, β a (a₁ * a₂) = β a a₁ * β a a₂)
    (hβn : ∀ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) → ∀ a ∈ A, ∀ a' ∈ A,
      β (n * a * n⁻¹) (n * a' * n⁻¹) = n * β a a' * n⁻¹) :
    ∀ a ∈ A, ∀ a' ∈ A, β a a' = 1 := by
  intro a ha a' ha'
  classical
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun x y => Subtype.ext (W.A_comm x x.2 y y.2) }
  have hV : ∀ x : Additive ↥A, 2 • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ : ∃ a : ↥A, Additive.ofMul a = x := ⟨Additive.toMul x, rfl⟩
    rw [← ofMul_pow]
    have h2 : a ^ 2 = 1 := Subtype.ext (by simpa using W.A_sq (a : G) a.2)
    rw [h2, ofMul_one]
  let _ : Module (ZMod 2) (Additive ↥A) := AddCommGroup.zmodModule hV
  have _ : Module.Finite (ZMod 2) (Additive ↥A) := Module.Finite.of_finite
  have hcard : Nat.card (Additive ↥A) = 16 := by
    rw [Nat.card_congr (Additive.toMul : Additive ↥A ≃ ↥A)]
    exact W.A_card
  have hfin : Module.finrank (ZMod 2) (Additive ↥A) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥A)
    rw [hcard, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  have hβ_one_r : ∀ a ∈ A, β a 1 = 1 := by
    intro a ha
    have h := hβr a ha 1 A.one_mem 1 A.one_mem
    rw [mul_one] at h
    have h1 : β a 1 * 1 = β a 1 * β a 1 := by
      rw [mul_one]
      exact h
    exact (mul_left_cancel h1).symm
  have hβ_one_l : ∀ a ∈ A, β 1 a = 1 := by
    intro a ha
    have h := hβl 1 A.one_mem 1 A.one_mem a ha
    rw [mul_one] at h
    have h1 : β 1 a * 1 = β 1 a * β 1 a := by
      rw [mul_one]
      exact h
    exact (mul_left_cancel h1).symm
  let βadd : Additive ↥A →+ Additive ↥A →+ Additive ↥A :=
    { toFun := fun u =>
        { toFun := fun v =>
            Additive.ofMul (⟨β ((Additive.toMul u : ↥A) : G)
              ((Additive.toMul v : ↥A) : G),
              hβA _ (Additive.toMul u).2 _ (Additive.toMul v).2⟩ : ↥A)
          map_zero' := by
            refine ofMul_eq_zero.2 (Subtype.ext ?_)
            simpa using hβ_one_r ((Additive.toMul u : ↥A) : G) (Additive.toMul u).2
          map_add' := fun v v' => by
            apply Additive.ofMul.injective
            apply Subtype.ext
            simp only [toMul_add, Subgroup.coe_mul]
            exact hβr ((Additive.toMul u : ↥A) : G) (Additive.toMul u).2 _
              (Additive.toMul v).2 _ (Additive.toMul v').2 }
      map_zero' := by
        refine AddMonoidHom.ext fun v => ?_
        refine ofMul_eq_zero.2 (Subtype.ext ?_)
        simpa using hβ_one_l ((Additive.toMul v : ↥A) : G) (Additive.toMul v).2
      map_add' := fun u u' => by
        refine AddMonoidHom.ext fun v => ?_
        apply Additive.ofMul.injective
        apply Subtype.ext
        simp only [toMul_add, Subgroup.coe_mul]
        exact hβl ((Additive.toMul u : ↥A) : G) (Additive.toMul u).2
          ((Additive.toMul u' : ↥A) : G) (Additive.toMul u').2
          ((Additive.toMul v : ↥A) : G) (Additive.toMul v).2 }
  let βlin : Additive ↥A →ₗ[ZMod 2] Additive ↥A →ₗ[ZMod 2] Additive ↥A :=
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun u => AddMonoidHom.toZModLinearMap 2 (βadd u)
        map_zero' := by ext v; simp
        map_add' := fun u u' => by ext v; simp }
  have hβlin : ∀ u v : Additive ↥A, βlin u v =
      Additive.ofMul (⟨β ((Additive.toMul u : ↥A) : G) ((Additive.toMul v : ↥A) : G),
        hβA _ (Additive.toMul u).2 _ (Additive.toMul v).2⟩ : ↥A) := fun u v => rfl
  have heq : ∀ (g : Additive ↥A ≃ₗ[ZMod 2] Additive ↥A) (u u' : Additive ↥A),
      βlin (g u) (g u') = g (βlin u u') := by
    intro g u u'
    classical
    let f : G → G := fun y =>
      if h : y ∈ A then ((g (Additive.ofMul ⟨y, h⟩)).toMul : G) else 1
    have hfval : ∀ a : ↥A, f (a : G) = ((g (Additive.ofMul a)).toMul : G) := by
      intro a
      simp [f, a.2]
    have hfA : ∀ a ∈ A, f a ∈ A := by
      intro a ha
      rw [hfval ⟨a, ha⟩]
      exact (g (Additive.ofMul ⟨a, ha⟩)).toMul.2
    have hfM : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
      intro a ha b hb
      rw [hfval ⟨a * b, A.mul_mem ha hb⟩, hfval ⟨a, ha⟩, hfval ⟨b, hb⟩]
      exact congrArg (fun x : Additive ↥A => ((Additive.toMul x : ↥A) : G))
        (map_add g (Additive.ofMul (⟨a, ha⟩ : ↥A)) (Additive.ofMul (⟨b, hb⟩ : ↥A)))
    have hfI : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
      intro a ha b hb hab
      rw [hfval ⟨a, ha⟩, hfval ⟨b, hb⟩] at hab
      have h1 : g (Additive.ofMul (⟨a, ha⟩ : ↥A)) =
          g (Additive.ofMul (⟨b, hb⟩ : ↥A)) := by
        apply Additive.toMul.injective
        exact Subtype.ext hab
      exact congrArg Subtype.val (Additive.ofMul.injective (g.injective h1))
    obtain ⟨n, hnL, hn⟩ := W.surj f hfA hfM hfI
    have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun x hx => by
      rw [hn x hx]
      exact hfA x hx
    have hgu : n * ((Additive.toMul u : ↥A) : G) * n⁻¹ = ((g u).toMul : G) := by
      rw [hn ((Additive.toMul u : ↥A) : G) (Additive.toMul u).2, hfval (Additive.toMul u),
        ofMul_toMul]
    have hgu' : n * ((Additive.toMul u' : ↥A) : G) * n⁻¹ = ((g u').toMul : G) := by
      rw [hn ((Additive.toMul u' : ↥A) : G) (Additive.toMul u').2, hfval (Additive.toMul u'),
        ofMul_toMul]
    have hβmem : β ((Additive.toMul u : ↥A) : G) ((Additive.toMul u' : ↥A) : G) ∈ A :=
      hβA _ (Additive.toMul u).2 _ (Additive.toMul u').2
    have hconj : n * β ((Additive.toMul u : ↥A) : G) ((Additive.toMul u' : ↥A) : G) * n⁻¹ =
        ((g (Additive.ofMul (⟨β ((Additive.toMul u : ↥A) : G)
          ((Additive.toMul u' : ↥A) : G), hβmem⟩ : ↥A))).toMul : G) := by
      rw [hn _ hβmem, hfval ⟨_, hβmem⟩]
    have hkey := hβn n hnL hnA ((Additive.toMul u : ↥A) : G) (Additive.toMul u).2
      ((Additive.toMul u' : ↥A) : G) (Additive.toMul u').2
    rw [hgu, hgu'] at hkey
    rw [hβlin, hβlin]
    rw [← ofMul_toMul (g (Additive.ofMul (⟨β ((Additive.toMul u : ↥A) : G)
      ((Additive.toMul u' : ↥A) : G), hβmem⟩ : ↥A)))]
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    exact hkey.trans hconj
  have hzero : βlin = 0 := martineau (V := Additive ↥A) (by omega) βlin heq
  have h0 : βlin (Additive.ofMul (⟨a, ha⟩ : ↥A))
      (Additive.ofMul (⟨a', ha'⟩ : ↥A)) = 0 := by
    rw [hzero]
    rfl
  rw [hβlin] at h0
  have h1 : (⟨β a a', hβA a ha a' ha'⟩ : ↥A) = 1 :=
    ofMul_eq_zero.1 (by simpa using h0)
  simpa using congrArg Subtype.val h1

end

end CFSG.EvenSporadicStandard.ThStd
