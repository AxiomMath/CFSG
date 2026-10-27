module

public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem layerExcludesQ8_of_gl2 {X : Type} [Group X] {t : X} {F : Type} [Field F]
    {H : Subgroup (GL (Fin 2) F)} {π : H →* X}
    (hrange : π.range = Subgroup.centralizer ({t} : Set X)) (hk : Q5GL2.CubeKer π)
    (hcs : Q5GL2.SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀)
    (eJ : Q5GL2.slPart H ≃* SL(2, F₀)) : LayerExcludesQ8 X t := by
  set C := Subgroup.centralizer ({t} : Set X) with hC
  set J : Subgroup X := (Q5GL2.slPart H).map π with hJ
  have hJr : J = (π.comp (Q5GL2.slPart H).subtype).range := by
    rw [hJ, MonoidHom.range_comp, Subgroup.range_subtype]
  let eJ' : ↥J ≃* SL(2, F₀) := (MulEquiv.subgroupCongr hJr).trans
    ((MonoidHom.ofInjective (Q5GL2.injective_slPart hk)).symm.trans eJ)
  have hJC : J ≤ C := by
    rw [← hrange]
    exact Subgroup.map_le_range π _
  have hn : (J.subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (g : X) ∈ π.range := by
      rw [hrange]
      exact g.2
    obtain ⟨A, hA⟩ := hg
    obtain ⟨B, hB, hBx⟩ := hx
    have hB' := Q5GL2.mem_slPart.mp hB
    have hmem : A * B * A⁻¹ ∈ Q5GL2.slPart H := by
      rw [Q5GL2.mem_slPart, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
        map_mul, map_inv, hB', mul_one, mul_inv_cancel]
    refine ⟨A * B * A⁻¹, hmem, ?_⟩
    rw [map_mul, map_mul, map_inv, hA, hBx]
    rfl
  have hK : IsComponentOf J C :=
    isComponentOf_of_normal hJC hn (isQuasisimple_of_equiv_sl2 h4 eJ')
  refine layerExcludesQ8_of_cent hK fun a ha b hb haJ _ _ _ => ?_
  have ha' : a ∈ π.range := by
    rw [hrange]
    exact ha
  have hb' : b ∈ π.range := by
    rw [hrange]
    exact hb
  obtain ⟨A, rfl⟩ := ha'
  obtain ⟨B, rfl⟩ := hb'
  obtain ⟨c, hc⟩ :=
    Q5GL2.exists_scalar_of_commute hk hcs fun B' hB' => haJ _ ⟨B', hB', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, Q5GL2.scalar_mul_comm]

theorem layerExcludesQ8_l3 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hm : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 p f) (t : X)
    (ht : orderOf t = 2) : LayerExcludesQ8 X t := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  let e : ↥(⊤ : Subgroup X) ≃* LinearFlag.projectiveSL 3 K :=
    Subgroup.topEquiv.trans ((e₀.trans
      (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  have hoddK : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, π, hrange, hk, -, -⟩ := Q5L3.exists_frame hoddK e (Subgroup.mem_top t) ht
  rw [top_inf_eq] at hrange
  exact layerExcludesQ8_of_gl2 hrange hk Q5L3.slCentScalar_top (by rw [hK]; omega)
    Q5L3.slPartTopEquiv

theorem layerExcludesQ8_u3 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hm : Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 p f) (t : X)
    (ht : orderOf t = 2) : LayerExcludesQ8 X t := by
  obtain ⟨⟨hℓ, hm1, -, -⟩, K, _, _, hK, ⟨e₀⟩⟩ := hm
  have h : UnitaryFieldData p f K := ⟨hℓ, hm1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  obtain ⟨π, hrange, hk, -⟩ :=
    Q5U3.exists_frame h hp2 (Subgroup.topEquiv.trans e₀) (Subgroup.mem_top t) ht
  rw [top_inf_eq] at hrange
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv h
  have hq := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  exact layerExcludesQ8_of_gl2 hrange hk (Q5U3.slCentScalar_GU2 h) (by rw [hq]; omega) eJ

end CFSG.ClassicalInvolution.Q3.TA3.Frame
