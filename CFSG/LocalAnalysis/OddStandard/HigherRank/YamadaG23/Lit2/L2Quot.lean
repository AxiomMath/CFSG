module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitCore
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Setup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

theorem l2_quot {X G : Type} [Group X] [Finite X] [Group G] [Finite G] {Z A : Subgroup X}
    {π : X →* G} {M : Subgroup G} {H : Subgroup X} (S : L2Setup Z A π M H) :
    ∃ ρ : ↥(l2Bar H) →* ↥M, Function.Surjective ρ ∧ CFSG.IsQuasisimple ↥(l2Bar H) ∧
      ρ.ker = center ↥(l2Bar H) ∧ IsPGroup 2 ↥(center ↥(l2Bar H)) ∧
      ∀ (x : ↥(l2Bar H)) (y : X), (x : X ⧸ CFSG.oddCore X) = l2Mu X y → (ρ x : G) = π y := by
  classical
  have hkerO : CFSG.oddCore X ≤ π.ker := by
    rw [S.ker]
    show CFSG.oddCore X ≤ Z ⊔ CFSG.oddCore X
    exact le_sup_right
  let ν : X ⧸ CFSG.oddCore X →* G := QuotientGroup.lift (CFSG.oddCore X) π hkerO
  have hν : ∀ y : X, ν (l2Mu X y) = π y := fun _ => rfl
  have hνcomp : ν.comp (l2Mu X) = π := MonoidHom.ext fun y => hν y
  have hker_le : ∀ w ∈ ν.ker, ∃ z ∈ Z, l2Mu X z = w := by
    intro w hw
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) w
    have hy : y ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hν y]
      exact MonoidHom.mem_ker.mp hw
    rw [S.ker] at hy
    change y ∈ Z ⊔ CFSG.oddCore X at hy
    obtain ⟨z, hz, o, ho, hzo⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    refine ⟨z, hz, ?_⟩
    change QuotientGroup.mk' (CFSG.oddCore X) z = QuotientGroup.mk' (CFSG.oddCore X) y
    have ho1 : QuotientGroup.mk' (CFSG.oddCore X) o = 1 := by
      simpa only [QuotientGroup.mk'_apply] using
        (QuotientGroup.eq_one_iff (N := CFSG.oddCore X) o).mpr ho
    rw [← hzo, map_mul, ho1, mul_one]
  have h3 : (l2Bar H).map ν = M := by
    change (H.map (l2Mu X)).map ν = M
    rw [Subgroup.map_map, hνcomp, S.map_H]
  have h4 : ⁅l2Bar H, l2Bar H⁆ = l2Bar H := by
    change ⁅H.map (l2Mu X), H.map (l2Mu X)⁆ = H.map (l2Mu X)
    rw [← Subgroup.map_commutator (l2Mu X) (H₁ := H) (H₂ := H), S.perf]
  have h5 : ∀ x ∈ l2Bar H, ∀ y ∈ ν.ker, x * y = y * x := by
    intro x hx y hy
    obtain ⟨h, _hh, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := hker_le y hy
    rw [← hzy, ← map_mul, ← map_mul, S.central z hz h]
  obtain ⟨ρ, hρsurj, hρcoe, hρker⟩ :=
    lit_H_hom (X := X ⧸ CFSG.oddCore X) (π := ν) (M := M) S.simple S.nonab h3 h5
  have hq : CFSG.IsQuasisimple ↥(l2Bar H) :=
    lit_quasisimple (M := M) S.simple S.nonab h4 h3 h5
  refine ⟨ρ, hρsurj, hq, hρker, ?_, ?_⟩
  ·
    intro x
    refine ⟨2, ?_⟩
    have hxker : (x : ↥(l2Bar H)) ∈ ρ.ker := by
      rw [hρker]; exact x.2
    have hρx : ρ (x : ↥(l2Bar H)) = 1 := MonoidHom.mem_ker.mp hxker
    have hνx : ν ((x : ↥(l2Bar H)) : X ⧸ CFSG.oddCore X) = 1 := by
      rw [← hρcoe (x : ↥(l2Bar H)), hρx]
      rfl
    obtain ⟨z, hz, hzx⟩ := hker_le ((x : ↥(l2Bar H)) : X ⧸ CFSG.oddCore X)
      (by rw [MonoidHom.mem_ker]; exact hνx)
    have hpow : (((x : ↥(l2Bar H)) : X ⧸ CFSG.oddCore X)) ^ 4 = 1 := by
      rw [← hzx, ← map_pow, S.four z hz, map_one]
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    apply Subtype.ext
    apply Subtype.ext
    simpa using hpow
  ·
    intro x y hxy
    rw [hρcoe x, hxy, hν y]

end CFSG.OddStandard.HigherRank.YamadaG23
