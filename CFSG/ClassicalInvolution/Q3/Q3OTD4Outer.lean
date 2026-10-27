module

public import CFSG.ClassicalInvolution.Q3.Q3OTD4Cls

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)


section Outer

variable {H : Type} [Group H] [Finite H]

theorem oddCoreIn_fixed_conj_plus4 (ψ : spinGroup Q₄ →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) (ℓ : ↥ψ.range)
    (hℓ1 : MulAut.conj ℓ ≠ 1) (hℓ2 : MulAut.conj ℓ * MulAut.conj ℓ = 1) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥ψ.range (MulAut.conj ℓ))) = ⊥ := by
  obtain ⟨hLp, hfs, hfk⟩ := quotient_data_plus4 ψ hψ
  have hℓ' : (QuotientGroup.mk ℓ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) ≠ 1 := by
    intro h
    exact hℓ1 ((conj_eq_one_iff_mem_center _).mpr ((QuotientGroup.eq_one_iff _).mp h))
  have hℓ'2 : (QuotientGroup.mk ℓ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) *
      QuotientGroup.mk ℓ = 1 := by
    have h1 : MulAut.conj (ℓ * ℓ) = 1 := by rw [map_mul]; exact hℓ2
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ((conj_eq_one_iff_mem_center _).mp h1)
  have hord : orderOf (QuotientGroup.mk ℓ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hℓ'2) hℓ'
  have hO := oddCoreFree_plus4 _ _ hfs hfk _ hord
  have hfix : fixedSubgroup (autToCentralQuotient ↥ψ.range (MulAut.conj ℓ)) =
      Subgroup.centralizer ({(QuotientGroup.mk ℓ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range)} :
        Set (↥ψ.range ⧸ Subgroup.center ↥ψ.range)) := by
    have : autToCentralQuotient ↥ψ.range (MulAut.conj ℓ) = MulAut.conj (QuotientGroup.mk ℓ) := by
      ext y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rfl
    rw [this, fixedSubgroup_conj]
  rw [hfix]
  exact hO

theorem twinOuterAlphaOn_plus4_aux :
    TwinOuterAlphaOn .POmegaPlus ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ := by
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hy2 hy1 hyz
  classical
  have hxc := central_involution_plus4 hpair.mem hpair.hx hpair.hx2 hpair.hx1
  have hsq := sq_mem_inn_plus4 ψ hpair.ker hpair.mem hpair.mem' hpair.ne hpair.comm v hvR hvR'
  have hxn : ψ x ∈ Subgroup.normalizer (ψ.range : Set H) := FrameVertex.mem_normalizer_range ψ x
  have hxL : ψ x ∈ ψ.range := ⟨x, rfl⟩
  have hb2 : FrameVertex.innerHom ψ x * FrameVertex.innerHom ψ x = 1 := by
    rw [← map_mul, hpair.hx2, map_one]
  have hvb : v * FrameVertex.innerHom ψ x = FrameVertex.innerHom ψ x * v := hvR x hpair.hx
  have hab : v * v * FrameVertex.innerHom ψ x = FrameVertex.innerHom ψ x * (v * v) := by
    rw [mul_assoc, hvb, ← mul_assoc, hvb, mul_assoc]
  have hb1 := innerHom_ne_one_plus4 ψ hpair.ker hpair.mem hpair.hx hpair.hx1
  exact alphaOf_klein_inner_good3 ψ.range hy2 hb2 hab hb1 hsq
    (toInducedAutOn_mem_innSubgroup ψ.range (ψ x) hxn hxL)
    (fun ℓ hℓ1 hℓ2 => oddCoreIn_fixed_conj_plus4 ψ hpair.ker ℓ hℓ1 hℓ2)
    (involutionOddCore_innerHom_plus4 ψ hpair.ker hpair.mem hpair.hx hpair.hx2 hpair.hx1 hxc)

end Outer

theorem twinOuterAlpha3_d4 : TwinOuterAlpha 3 1 .POmegaPlus 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ →
      TwinOuterAlphaOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact twinOuterAlphaOn_plus4_aux
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num))

end CFSG.ClassicalInvolution.Q3.Q3OT
