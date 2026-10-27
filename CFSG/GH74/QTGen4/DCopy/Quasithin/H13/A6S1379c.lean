module

public import CFSG.Quasithin.H13.A6S1379c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1379a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1379b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem rho_VH_F4 {x : G} (hx : x ∈ conjClosure V H) :
    ∃ hxN : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hxN⟩ = 1 ∨ S.frame.ρ ⟨x, hxN⟩ = swap 4 5 := by
  let X : Subgroup G := ((Subgroup.zpowers (swap (4 : Fin 6) 5)).comap S.frame.ρ).map
    (Subgroup.normalizer (V : Set G)).subtype
  have hmemX : ∀ y : ↥(Subgroup.normalizer (V : Set G)),
      S.frame.ρ y = 1 ∨ S.frame.ρ y = swap 4 5 → (y : G) ∈ X := by
    intro y hy
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_comap]
    rcases hy with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hX : conjClosure V H ≤ X := by
    refine conjClosure_le fun h hh v hv => ?_
    obtain ⟨hwN, hρ⟩ := S.rho_conjSub_V_F4 hNS h13315 h1356two hH hab hh (mul_mem_conjSub hv)
    exact hmemX ⟨_, hwN⟩ hρ
  obtain ⟨y, hy, rfl⟩ := hX hx
  refine ⟨y.2, ?_⟩
  have hy' : S.frame.ρ y ∈ Subgroup.zpowers (swap (4 : Fin 6) 5) := hy
  show S.frame.ρ y = 1 ∨ S.frame.ρ y = swap 4 5
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, ← two_mul, zpow_mul, show swap (4 : Fin 6) 5 ^ (2 : ℤ) = 1 by decide, one_zpow]
  · right
    rw [← hk, zpow_add, zpow_mul, show swap (4 : Fin 6) 5 ^ (2 : ℤ) = 1 by decide, one_zpow,
      one_mul, zpow_one]

theorem R8_le_rho_QH_F4 (h13314 : Stmt13_3_14_F4)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    ∀ σ ∈ R8, ∃ q ∈ pCoreOf 2 H, ∃ hqN : q ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨q, hqN⟩ = σ := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  obtain ⟨h, hh, w, hw, hwN, hρw⟩ := S.exists_conjSub_rho_45_F4 hNS h13315 h1356two hH hab hna
  have hwQ : w ∈ pCoreOf 2 H :=
    hF.conjSub_le_pCoreOf (S.V_le_QH_F4 hNS h13315 h1356two hH hab) hh hw
  intro σ hσ
  rcases R8_cases σ hσ with hK | hK
  · exact S.K4_le_rho_QH_F4 hNS h13315 h1356two hH h13314 σ hK
  · obtain ⟨q, hq, hqN, hρq⟩ := S.K4_le_rho_QH_F4 hNS h13315 h1356two hH h13314 _ hK
    refine ⟨q * w, (pCoreOf 2 H).mul_mem hq hwQ, Subgroup.mul_mem _ hqN hwN, ?_⟩
    have e : (⟨q * w, Subgroup.mul_mem _ hqN hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨q, hqN⟩ * ⟨w, hwN⟩ := rfl
    rw [e, map_mul, hρq, hρw, mul_assoc, show swap (4 : Fin 6) 5 * swap 4 5 = 1 by decide,
      mul_one]

end Abelian

end Setting4

end CFSG.Quasithin.H13.A6
