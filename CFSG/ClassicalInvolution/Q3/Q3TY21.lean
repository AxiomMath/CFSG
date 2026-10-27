module

public import CFSG.ClassicalInvolution.Q3.Q3TY19
public import CFSG.ClassicalInvolution.Q3.Q3TY20
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.RouteD.TWT9Fix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.LieType.Universal CFSG.LieType CFSG.LieType.CurtisTits
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWT9 CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Models.TwistedPairs (four_le_card_shortField')
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}


theorem pattern_td4_3 (c : TCtx3 .POmegaMinus 4 Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {J₁ : Subgroup G} (hJ₁Ω : J₁ ∈ Ω) (hKJ₁ : Commutes K J₁)
    (hβJ₁ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J₁)
    {x : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)}
    {α : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ≃*
      spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)}
    {g₀ : Vm 4 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 4 (GaloisField 3 1)}
    {ε : GaloisField 3 1}
    (hn2 : locImg Ω z J₁ =
      ((rootSL2 (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (hconj : ∀ y v, spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (α y) (g₀ v) =
      g₀ (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) y v))
    (hε : ε * ε = 1)
    (hscal : ∀ y,
      polar (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x
        ((minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
          true)) y = 0 →
      polar (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x
        ((minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
          false)) y = 0 →
      g₀ y = ε • y) :
    PartnerPatternMinus3 4 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have cq := centralQuot3_minus hadm
  have hQ : (polarBilin (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 (GaloisField 3 1) hirr
  obtain ⟨j, hjK, hjY, hjΩ, hjperf, hjc, hjp, hjtw, hjimg⟩ :=
    c.exists_nodes_typeTwistedD3_img (m := 4) le_rfl
      (spinMinus6Generated_galois (p := 3) (f := 1) (by norm_num))
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
    (4 - 1) := (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame with hF₀
  have hg : spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hpow : ∀ a : Fin (4 - 1), Pow3 (rankOne (minusDatum 4 hirr).rootGroup a) := by
    intro a
    by_cases ha : a.val + 1 < 4 - 1
    · exact cq.pow3 _ (rankOne_mem_fund_minus hirr ha)
    · have := fact_shortField hirr
      have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
      intro l hl
      rw [rankOne_minusDatum_short hirr ha] at hl ⊢
      exact range_perfect_of_sl2 (four_le_card_shortField' (b := (minusCoeffs 3 1).1)
        (c := (minusCoeffs 3 1).2)) _ (pow_mem hl 3)
  have hRfix : ∀ a : Fin (4 - 1), 1 ≤ a.val → ∀ r ∈ (rankOne (minusDatum 4 hirr).rootGroup
      a).map (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    have hR3 : Pow3 ((rankOne (minusDatum 4 hirr).rootGroup a).map (MulAut.conj x).toMonoidHom) :=
      (hpow a).map (MulAut.conj x).toMonoidHom
    refine eq_of_fixed_of_pow3 (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) (ker_spinAction_le_center _) cq.cop α (MulAut.conj g₀)
      (fun y => ?_) hR3 ?_
    · refine LinearEquiv.ext fun v => ?_
      show spinAction _ (α y) v = g₀ (spinAction _ y (g₀⁻¹ v))
      have e1 : g₀ (g₀⁻¹ v) = v := by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      have := hconj y (g₀⁻¹ v)
      rw [e1] at this
      exact this
    · rintro _ ⟨s, hs, rfl⟩
      have hshs : (MulAut.conj x).toMonoidHom s = x * s * x⁻¹ := rfl
      have hhO : spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 3 1)
            (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
            (minusCoeffs 3 1).2) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x
            (F₀.vec ⟨0, by omega⟩ r) := by
        intro r
        rw [hshs, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          ← LinearEquiv.mul_apply (spinAction _ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
        show spinAction _ x (spinAction _ s (F₀.vec ⟨0, by omega⟩ r)) = _
        exact congrArg (spinAction _ x) (TWT8.rankOne_fix_vec_zero_minus hirr (by omega)
          (by omega : 0 < a.val) hs r)
      have hcomm := commute_of_scalar_on_perp hQ (imgPair F₀ ⟨0, by omega⟩ hg) hg₀O hhO hε
        (fun y hy => hscal y (HypPair.mem_perp.mp hy).1 (HypPair.mem_perp.mp hy).2)
        (fun q hq => by
          obtain ⟨a₁, b₁, rfl⟩ := (mem_hypPlane_iff _).mp hq
          rw [map_add, map_smul, map_smul]
          exact congrArg₂ (· + ·) (congrArg (a₁ • ·) (hfixv true))
            (congrArg (b₁ • ·) (hfixv false)))
      show g₀ * spinAction _ _ * g₀⁻¹ = _
      rw [hcomm]
      group
  have hfix : ∀ a : Fin (4 - 1), 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)), s ∈ rankOne (minusDatum 4 hirr).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hn2z : J₁ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hJ₁Ω c.hz.mem (commutes_symm hKJ₁)
  have hr0 : rankOne (minusDatum 4 hirr).rootGroup (⟨0, by norm_num⟩ : Fin (4 - 1)) =
      rootSL2 (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1 (by omega)
        (by omega) (by omega) true false :=
    rankOne_minusDatum_of_lt hirr (k := ⟨0, by norm_num⟩) (by norm_num)
  have hpair0 : ∀ a : Fin (4 - 1), a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by norm_num⟩ : Fin (4 - 1)) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j ⟨0, by norm_num⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by norm_num⟩, (hjΩ _ (by simp)).1, rfl⟩
    have heq : conjSub (y' : G) (j ⟨0, by norm_num⟩) = J₁ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j ⟨0, by norm_num⟩) y', hjimg ⟨0, by norm_num⟩, hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    exact hβJ₁
  exact PartnerPatternMinus3.of_locAut c hjK hjY (fun a ha => (hjΩ a ha).1) hjperf hjc hjp hjtw hy
    htz hfix hpair0

end Group

end CFSG.ClassicalInvolution.Q3.Q3TY
