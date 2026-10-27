module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.GorensteinWalter Matrix
open scoped MatrixGroups

section S0

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem s0_mem_range {i : K} (hi : i * i = -1) :
    pGammaL2FullSplitTorus K (-1) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  let g : SL(2, K) := ⟨!![i, 0; 0, -i], by rw [Matrix.det_fin_two_of]; linear_combination -hi⟩
  refine ⟨QuotientGroup.mk' _ g, ?_⟩
  rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K (-1))
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 i hi0, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = !![i, 0; 0, -i] := rfl
  rw [hg]
  fin_cases a <;> fin_cases b <;>
    simp [pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar, hi]

theorem s0_ne_one (hK : IsOddPrimePower (Nat.card K)) : pGammaL2FullSplitTorus K (-1) ≠ 1 := by
  intro h
  rw [← map_one (pGammaL2FullSplitTorus K)] at h
  have h1 := congrArg Units.val (pGammaL2FullSplitTorus_injective K h)
  have hodd : Odd (Nat.card K) := by
    obtain ⟨p, n, -, hp, -, hn⟩ := hK
    rw [hn]; exact hp.pow
  have h2 : (2 : K) = 0 := by
    have : (-1 : K) = 1 := by simpa using h1
    linear_combination -this
  exact GorensteinWalter.two_ne_zero_of_odd_card K hodd h2

theorem exists_conj_s0 (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {i : K}
    (hi : i * i = -1) {x : PGL2 K}
    (hx : x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ c ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range,
      c * x * c⁻¹ = pGammaL2FullSplitTorus K (-1) := by
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  have hs2 : pGammaL2FullSplitTorus K (-1) ^ 2 = 1 := by
    rw [← map_pow]
    simp
  obtain ⟨c, hc, hcx⟩ := pgl2_inner_involutions_conjugate hK hcard (hcomm ▸ hx)
    ⟨hx1, by rw [sq]; exact hx2⟩ (hcomm ▸ s0_mem_range hi) ⟨s0_ne_one hK, hs2⟩
  exact ⟨c, hcomm ▸ hc, hcx⟩

end S0

section Restrict

variable {X : Type} [Group X] {N : Subgroup X} [N.Normal] [IsSimpleGroup N]

theorem map_eq_of_simple [Finite X] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (β : MulAut X) : N.map (β : X →* X) = N := by
  set M := N.map (β : X →* X) with hM
  have hMn : M.Normal := Subgroup.Normal.map inferInstance _ β.surjective
  have hle : N ≤ M := by
    have hNM : (N ⊓ M).subgroupOf N = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ M).subgroupOf N) with h | h
      · exfalso
        have hinf : N ⊓ M = ⊥ := by
          rw [eq_bot_iff]
          intro x ⟨hxN, hxM⟩
          have : (⟨x, hxN⟩ : N) ∈ (N ⊓ M).subgroupOf N := ⟨hxN, hxM⟩
          rw [h, Subgroup.mem_bot] at this
          exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
        have hMC : M ≤ Subgroup.centralizer (N : Set X) := by
          intro m hm
          rw [Subgroup.mem_centralizer_iff]
          intro n hn
          have hc : n * m * n⁻¹ * m⁻¹ ∈ N ⊓ M :=
            ⟨N.mul_mem (‹N.Normal›.conj_mem n hn m) (N.inv_mem hn) |> fun h => by
              simpa [mul_assoc] using N.mul_mem hn (‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) m),
              M.mul_mem (hMn.conj_mem m hm n) (M.inv_mem hm)⟩
          rw [hinf, Subgroup.mem_bot] at hc
          calc n * m = n * m * n⁻¹ * m⁻¹ * (m * n) := by group
            _ = m * n := by rw [hc, one_mul]
        rw [hC] at hMC
        have hM1 : M = ⊥ := le_bot_iff.mp hMC
        have hN1 : N = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          have : β x ∈ M := ⟨x, hx, rfl⟩
          rw [hM1, Subgroup.mem_bot] at this
          exact (Subgroup.mem_bot).mpr (by simpa using this)
        have : Nontrivial N := inferInstance
        rw [hN1] at this
        exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
      · exact h
    intro x hx
    have : (⟨x, hx⟩ : N) ∈ (N ⊓ M).subgroupOf N := by rw [hNM]; trivial
    exact this.2
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [hM, Subgroup.card_map_of_injective β.injective])).symm

@[expose] noncomputable def restrictAut [Finite X] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (β : MulAut X) : MulAut N :=
  (β.subgroupMap N).trans (MulEquiv.subgroupCongr (map_eq_of_simple hC β))

@[expose] noncomputable def restrictHom [Finite X] (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    MulAut X →* MulAut N where
  toFun := restrictAut hC
  map_one' := by ext n; rfl
  map_mul' _ _ := by ext n; rfl

theorem restrictHom_apply [Finite X] (hC : Subgroup.centralizer (N : Set X) = ⊥) (β : MulAut X)
    (n : N) : (restrictHom hC β n : X) = β n := rfl

end Restrict

section Embed

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal] [IsSimpleGroup N]
  (hC : Subgroup.centralizer (N : Set X) = ⊥) {K : Type} [Field K] [Finite K]
  (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : N ≃* PSL2 K)
  (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))

@[expose] noncomputable def autToPGammaL2 : MulAut X →* PGammaL2 K :=
  (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (restrictHom hC))

theorem equiv_autToPGammaL2 (β : MulAut X) :
    pGammaL2EquivMulAutPSL2 K hK hcard hsurj (autToPGammaL2 hC hK hcard e hsurj β) =
      MulAut.congr e (restrictHom hC β) := by
  simp [autToPGammaL2]

omit [Finite X] [IsSimpleGroup N] in
theorem equiv_normalPSL2ToPGammaL2 (x : X) :
    pGammaL2EquivMulAutPSL2 K hK hcard hsurj (normalPSL2ToPGammaL2 N K hK hcard e hsurj x) =
      MulAut.congr e (MulAut.conjNormal x) := by
  simp [normalPSL2ToPGammaL2, normalPSL2ConjAction]

theorem autToPGammaL2_conj (β : MulAut X) (x : X) :
    autToPGammaL2 hC hK hcard e hsurj β * normalPSL2ToPGammaL2 N K hK hcard e hsurj x *
        (autToPGammaL2 hC hK hcard e hsurj β)⁻¹ =
      normalPSL2ToPGammaL2 N K hK hcard e hsurj (β x) := by
  apply (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).injective
  rw [map_mul, map_mul, map_inv, equiv_autToPGammaL2, equiv_normalPSL2ToPGammaL2,
    equiv_normalPSL2ToPGammaL2, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext n
  rw [MulAut.mul_apply, MulAut.mul_apply, ← map_inv, restrictHom_apply, MulAut.conjNormal_apply,
    MulAut.conjNormal_apply, map_mul, map_mul, restrictHom_apply]
  simp [map_inv]

theorem autToPGammaL2_mulAutConj (x : X) :
    autToPGammaL2 hC hK hcard e hsurj (MulAut.conj x) =
      normalPSL2ToPGammaL2 N K hK hcard e hsurj x := by
  apply (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).injective
  rw [equiv_autToPGammaL2, equiv_normalPSL2ToPGammaL2]
  congr 1
  ext n
  rw [restrictHom_apply, MulAut.conjNormal_apply, MulAut.conj_apply]

theorem autToPGammaL2_injective :
    Function.Injective (autToPGammaL2 hC hK hcard e hsurj) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  ext x
  have h := autToPGammaL2_conj hC hK hcard e hsurj β x
  rw [hβ, one_mul, inv_one, mul_one] at h
  exact (normalPSL2ToPGammaL2_injective N K hK hcard e hC hsurj h).symm

end Embed

end CFSG.ClassicalInvolution.Q3.TL4.MF164
