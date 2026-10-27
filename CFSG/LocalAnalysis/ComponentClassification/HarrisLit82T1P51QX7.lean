module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7SC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7TC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QFAt

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem famF_E7 :
    FamF .E7 := by
  refine famF_of_fAt fun X _ _ _ n p f hp hp2 hX hq z hz => ?_
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup .E7
    (GH74.chevalleyExceptionalModel_of_lieModel (t := .E7) (by decide) hX).2
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at h1
    exact lt_irrefl _ h1
  have hK5 : 5 ≤ Nat.card K := by
    obtain ⟨-, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
    have h3' : Nat.card K ≠ 3 := by
      rw [hK]
      exact hq
    have hKodd : Odd (Nat.card K) := by
      rw [hK]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨k, hk⟩ := hKodd
    omega
  set z' : adjointGroup .E7 K := E z with hz'def
  have hz' : orderOf z' = 2 := (orderOf_injective E.toMonoidHom E.injective z).trans hz
  have hZ := center_adjointGroup_eq_bot (τ := .E7) (K := K)
  have hcj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : x * y * x⁻¹ = y := DFunLike.congr_fun ((MonoidHom.mem_ker).1 hx) y
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  set α : MulAut (adjointGroup .E7 K) :=
    MulAut.conj z' * rootDiagAut .E7 K (1 : Fin Tag.E7.rank → Kˣ) with hαdef
  have hα1 : rootDiagAut .E7 K (1 : Fin Tag.E7.rank → Kˣ) = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_rootDiagAut, rootDiagUnit_one, one_mul, inv_one, mul_one]
    rfl
  have hαeq : α = MulAut.conj z' := by rw [hαdef, hα1, mul_one]
  have hαo : orderOf α = 2 := by
    rw [hαeq, orderOf_injective _ hcj z', hz']
  have hfix : (centralizer ({z} : Set X)).map E.toMonoidHom = fixedSubgroup α := by
    rw [hαeq]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      change z' * E x * z'⁻¹ = E x
      rw [hz'def, ← map_inv, ← map_mul, ← map_mul, ← hx', mul_inv_cancel_right]
    · intro hy
      have hy' : z' * y * z'⁻¹ = y := hy
      refine ⟨E.symm y, Subgroup.mem_centralizer_singleton_iff.2 (E.injective ?_),
        E.apply_symm_apply y⟩
      rw [map_mul, map_mul, E.apply_symm_apply, ← hz'def]
      calc y * z' = z' * y * z'⁻¹ * z' := by rw [hy']
        _ = z' * y := by group
  let Θ₀ : centralizer ({z} : Set X) ≃* fixedSubgroup α :=
    ((centralizer ({z} : Set X)).equivMapOfInjective E.toMonoidHom E.injective).trans
      (MulEquiv.subgroupCongr hfix)
  have hmodel : CentModel (fixedSubgroup α) := by
    by_cases hsplit : ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) ∧ ∃ ψ : MulAut (adjointGroup .E7 K),
        ψ * α * ψ⁻¹ = rootDiagAut .E7 K (signMaskTuple .E7 K m)
    · obtain ⟨m, hm, ψ, hψ⟩ := hsplit
      have h := centModel_e7_split hp hp2 hK hK5 hm
      rw [← hψ] at h
      exact h.of_mulEquiv (fixedSubgroupMulConjEquiv ψ α)
    · push Not at hsplit
      exact centModel_e7_twisted hp2 (Nat.one_le_iff_ne_zero.2 hf) hK hαo hsplit
  obtain ⟨hcomm, hinv⟩ := evenCent_of_centModel hz Θ₀ hmodel
  exact fAt_of_evenCent hcomm hinv

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
