module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Torus

variable {K : Type} [Field K]

theorem diagSp_rr1_mem_leviTorusSp_zero_two (r : Kˣ) :
    diagSp K 3 ![r, r, 1] ∈ leviTorusSp K ({0, 2} : Finset (Fin 3)) := by
  refine diagSp_mem_leviTorusSp fun j hj => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩

variable {G : Type} [Group G] {L : Subgroup G}

theorem modelToG_swapChart_threeTorus_le_zero_two (e : L ≃* StatedSp 3 K) :
    modelToG (swapChart e) (threeTorus K) ≤
      modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG _).1 hx
  obtain ⟨r, rfl⟩ := mem_threeTorus.1 hy
  rw [swapChart_symm_apply, conj_permSp_swapOneTwo_diagSp]
  exact UnitaryPilot.symm_mem_modelToG e (diagSp_rr1_mem_leviTorusSp_zero_two r)

end Torus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem le_centralizer_of_conj_eq_mul_three_two (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {g : G}
    (hg : g⁻¹ * t * g = t * ((e.symm (siegDiag K 2 1) : L) : G))
    {φ' : StatedSp 3 K →* G} (hφ' : Function.Injective φ')
    (hφ'r : φ'.range = CFSG.conjugate L g)
    (hφ'z : φ' (siegDiag K 2 1) = ((e.symm (siegDiag K 2 1) : L) : G))
    {S : Subgroup G} (hSperf : ⁅S, S⁆ = S)
    (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSY : S ≤ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G))
    (hzS : ((e.symm (siegDiag K 2 1) : L) : G) ∈ S)
    {B : Subgroup G} (hBperf : ⁅B, B⁆ = B) (hBL : B ≤ L)
    (hBz : B ≤ centralizer ({((e.symm (siegDiag K 2 1) : L) : G)} : Set G))
    (hBY : B ≤ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G)) :
    S ≤ centralizer (B : Set G) := by
  have hz₁ : (((swapChart e).symm (siegDiag K 1 1) : L) : G) =
      ((e.symm (siegDiag K 2 1) : L) : G) := by
    rw [swapChart_symm_siegDiag]
  set φ₁ : StatedSp 3 K →* G :=
    φ'.comp (MulAut.conj (permSp K swapOneTwo)).toMonoidHom with hφ₁def
  have hφ₁ : Function.Injective φ₁ := hφ'.comp (MulAut.conj (permSp K swapOneTwo)).injective
  have hφ₁r : φ₁.range = CFSG.conjugate L g := by
    rw [hφ₁def, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (MulAut.conj (permSp K swapOneTwo)).surjective, ← MonoidHom.range_eq_map, hφ'r]
  have hφ₁z : φ₁ (siegDiag K 1 1) = (((swapChart e).symm (siegDiag K 1 1) : L) : G) := by
    rw [hz₁, ← hφ'z, hφ₁def]
    change φ' (permSp K swapOneTwo * siegDiag K 1 1 * (permSp K swapOneTwo)⁻¹) = _
    rw [conj_permSp_swapOneTwo_siegDiag]
  have hY := modelToG_swapChart_threeTorus_le_zero_two (K := K) e
  exact le_centralizer_of_conj_eq_mul_three hset hOut hK (swapChart e) htC ht
    (by rw [hz₁]; exact hg) hφ₁ hφ₁r hφ₁z hSperf hSsimple hSt
    (hSY.trans (centralizer_le hY)) (by rw [hz₁]; exact hzS) hBperf hBL (by rw [hz₁]; exact hBz)
    (hBY.trans (centralizer_le hY))

end CFSG.SeitzReduction.SymplecticPilot
