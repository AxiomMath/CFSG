module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoChev

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo


variable {K : Type} [Field K]

theorem g2FieldHom_weylElement (σ : K ≃+* K) (k : Fin (Tag.rank .G2)) (s : Kˣ) :
    g2FieldHom K σ (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2)) k s) =
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2)) k
        (Units.map σ.toRingHom.toMonoidHom s) := by
  unfold CFSG.LieType.Steinberg.weylElement
  simp only [map_mul, g2FieldHom_xPar]
  simp [map_neg, map_inv₀]

theorem g2FieldHom_torusElement (σ : K ≃+* K) (k : Fin (Tag.rank .G2)) (s : Kˣ) :
    g2FieldHom K σ (torusElement .G2 K k s) =
      torusElement .G2 K k (Units.map σ.toRingHom.toMonoidHom s) := by
  have hd : ∀ t : Kˣ, torusElement .G2 K k t =
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2)) k t *
        (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2)) k 1)⁻¹ := by
    intro t
    have h1 := weylElement_xPar (F := rootOperatorFamily .G2) (K := K) k t
    have h2 := weylElement_xPar (F := rootOperatorFamily .G2) (K := K) k 1
    have h3 : torusElement .G2 K k 1 = 1 := (torusHom (τ := .G2) K k).map_one
    rw [h3, one_mul] at h2
    rw [h1, h2]
    group
  rw [hd, hd, map_mul, map_inv, g2FieldHom_weylElement, g2FieldHom_weylElement]
  simp

theorem g2FieldHom_eq_pow_of_mem_torus {σ : K ≃+* K} {n : ℕ} (hσ : ∀ a : K, σ a = a ^ n)
    (hcomm : ∀ a ∈ ⨆ k, torus (τ := .G2) K k, ∀ b ∈ ⨆ k, torus (τ := .G2) K k, a * b = b * a)
    {t : adjointGroup .G2 K} (ht : t ∈ ⨆ k, torus (τ := .G2) K k) :
    g2FieldHom K σ t = t ^ n := by
  refine Subgroup.iSup_induction' (torus (τ := .G2) K)
    (C := fun t _ => g2FieldHom K σ t = t ^ n) ?_ ?_ ?_ ht
  · intro k x hx
    obtain ⟨s, rfl⟩ := hx
    have hu : Units.map σ.toRingHom.toMonoidHom s = s ^ n := Units.ext (by simp [hσ])
    have h1 := g2FieldHom_torusElement σ k s
    rw [hu] at h1
    exact h1.trans (map_pow (torusHom (τ := .G2) K k) s n)
  · rw [map_one, one_pow]
  · intro x y hx hy hxe hye
    rw [map_mul, hxe, hye]
    exact ((show Commute x y from hcomm x hx y hy).mul_pow n).symm

theorem g2FieldHom_mem_rankOne (σ : K ≃+* K) (i : Fin (Tag.rank .G2))
    {x : adjointGroup .G2 K} (hx : x ∈ rankOne (g2Datum K).rootGroup i) :
    g2FieldHom K σ x ∈ rankOne (g2Datum K).rootGroup i := by
  have hle : rankOne (g2Datum K).rootGroup i ≤
      (rankOne (g2Datum K).rootGroup i).comap (g2FieldHom K σ).toMonoidHom :=
    sup_le (fun y hy => le_sup_left (a := (g2Datum K).rootGroup (Pi.single i 1))
        (g2FieldHom_mem_rootGroup σ hy))
      (fun y hy => le_sup_right (b := (g2Datum K).rootGroup (-Pi.single i 1))
        (g2FieldHom_mem_rootGroup σ hy))
  exact hle hx

theorem g2FieldHom_mem_posUnipotentExcept (σ : K ≃+* K) (i : Fin (Tag.rank .G2))
    {x : adjointGroup .G2 K} (hx : x ∈ posUnipotentExcept (g2Datum K) i) :
    g2FieldHom K σ x ∈ posUnipotentExcept (g2Datum K) i := by
  have hle : posUnipotentExcept (g2Datum K) i ≤
      (posUnipotentExcept (g2Datum K) i).comap (g2FieldHom K σ).toMonoidHom :=
    iSup₂_le fun γ hγ y hy => rootGroup_le_posUnipotentExcept hγ (g2FieldHom_mem_rootGroup σ hy)
  exact hle hx

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo
