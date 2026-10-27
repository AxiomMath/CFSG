module

public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.CharacterTheory.Semidihedral.AlternatingSevenExclusion
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

section Action

variable {G : Type} [Group G]

noncomputable def phiHom [Finite G] (K : Subgroup G) :
    ↥(normalizer (K : Set G)) →* MulAut (Hat K) where
  toFun c := phi K c c.2
  map_one' := by
    ext x
    obtain ⟨k, rfl⟩ := hatMk_surjective K x
    rw [phi_mk]
    simp
  map_mul' x y := phi_mul K x.2 y.2

end Action

theorem no_order_eight_aut {E : Type} [Group E] (hE : IsDoubleCoverOfAlt E 7) (φ : MulAut E) :
    orderOf φ ≠ 8 := by
  obtain ⟨π, z, hcov, -⟩ := CFSG.GH74.KGroups.TwoA7.exists_cover hE
  intro h8
  have h := orderOf_injective hcov.autPerm hcov.autPerm_injective φ
  exact CFSG.Semidihedral.AlternatingSevenExclusion.symmetric_seven_no_order_eight _ (h.trans h8)

variable {G : Type} [Group G] [Finite G]

theorem pow_four_mem_cSec {K : Subgroup G} (hK : IsDoubleCoverOfAlt (Hat K) 7) {y : G}
    (hy : y ∈ normalizer (K : Set G)) (hy8 : y ^ 8 = 1) : y ^ 4 ∈ cSec K := by
  have h4 : y ^ 4 ∈ normalizer (K : Set G) := pow_mem hy 4
  rw [← phi_eq_one_iff K h4]
  let Y : ↥(normalizer (K : Set G)) := ⟨y, hy⟩
  have hφ : phi K (y ^ 4) h4 = (phiHom K Y) ^ 4 := by
    rw [← map_pow]
    rfl
  rw [hφ]
  by_contra hne
  have hφ8 : (phiHom K Y) ^ 8 = 1 := by
    rw [← map_pow]
    have : Y ^ 8 = 1 := Subtype.ext (by simpa using hy8)
    rw [this, map_one]
  have hord : orderOf (phiHom K Y) = 8 :=
    orderOf_eq_prime_pow (p := 2) (n := 2) (by norm_num; exact hne) (by norm_num; exact hφ8)
  exact no_order_eight_aut hK _ hord

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
