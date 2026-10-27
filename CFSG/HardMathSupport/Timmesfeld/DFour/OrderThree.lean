module

public import CFSG.RankThree.SteinbergR3ECAOddD4Centralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module
open LinearMap (BilinForm)

section OrderThree

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {g : V ≃ₗ[K] V}

@[expose] noncomputable def fix3 (g : V ≃ₗ[K] V) : V →ₗ[K] V :=
  (3 : K)⁻¹ • ((LinearMap.id : V →ₗ[K] V) + (g : V →ₗ[K] V) +
    (g : V →ₗ[K] V) ∘ₗ (g : V →ₗ[K] V))

theorem fix3_apply (v : V) : fix3 g v = (3 : K)⁻¹ • (v + g v + g (g v)) := by
  simp [fix3]

@[expose] noncomputable def fixSp (g : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id)

theorem mem_fixSp {v : V} : v ∈ fixSp g ↔ g v = v := by
  simp [fixSp, sub_eq_zero]

@[expose] noncomputable def movSp (g : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker ((LinearMap.id : V →ₗ[K] V) + (g : V →ₗ[K] V) +
    (g : V →ₗ[K] V) ∘ₗ (g : V →ₗ[K] V))

theorem mem_movSp {v : V} : v ∈ movSp g ↔ v + g v + g (g v) = 0 := by
  simp [movSp]

theorem three_smul_eq (v : V) : (3 : K) • v = v + v + v := by
  rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

section Cube

set_option linter.unusedSectionVars false

variable (h3 : (3 : K) ≠ 0) (hg3 : ∀ v, g (g (g v)) = v)
include h3 hg3

theorem fix3_mem (v : V) : fix3 g v ∈ fixSp g := by
  rw [mem_fixSp, fix3_apply, map_smul, map_add, map_add, hg3]
  congr 1
  abel

theorem fix3_of_mem {v : V} (hv : v ∈ fixSp g) : fix3 g v = v := by
  rw [mem_fixSp] at hv
  rw [fix3_apply, hv, hv, ← three_smul_eq (K := K), smul_smul, inv_mul_cancel₀ h3, one_smul]

theorem fix3_of_mem_movSp {v : V} (hv : v ∈ movSp g) : fix3 g v = 0 := by
  rw [mem_movSp] at hv
  rw [fix3_apply, hv, smul_zero]

theorem sub_fix3_mem (v : V) : v - fix3 g v ∈ movSp g := by
  have hP := fix3_mem h3 hg3 v
  rw [mem_fixSp] at hP
  rw [mem_movSp, map_sub, map_sub, hP, hP]
  have e : (v - fix3 g v) + (g v - fix3 g v) + (g (g v) - fix3 g v) =
      (v + g v + g (g v)) - (3 : K) • fix3 g v := by
    rw [three_smul_eq]
    abel
  rw [e, fix3_apply, smul_smul, mul_inv_cancel₀ h3, one_smul, sub_self]

theorem movSp_apply_mem {v : V} (hv : v ∈ movSp g) : g v ∈ movSp g := by
  rw [mem_movSp] at hv ⊢
  rw [hg3]
  have := congrArg g hv
  rw [map_add, map_add, map_zero, hg3] at this
  exact this

theorem fixSp_inf_movSp : fixSp g ⊓ movSp g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hB, hW⟩
  have h := fix3_of_mem h3 hg3 hB
  rw [fix3_of_mem_movSp h3 hg3 hW] at h
  exact h.symm

theorem fixSp_sup_movSp : fixSp g ⊔ movSp g = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have e : v = fix3 g v + (v - fix3 g v) := by abel
  rw [e]
  exact Submodule.add_mem_sup (fix3_mem h3 hg3 v) (sub_fix3_mem h3 hg3 v)

theorem movSp_sup_fixSp : movSp g ⊔ fixSp g = ⊤ := by
  rw [sup_comm]
  exact fixSp_sup_movSp h3 hg3

theorem eq_sup_inf_fix3 {M : Submodule K V} (hM : ∀ x ∈ M, g x ∈ M) :
    M = (M ⊓ fixSp g) ⊔ (M ⊓ movSp g) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  have hPx : fix3 g x ∈ M := by
    rw [fix3_apply]
    exact M.smul_mem _ (M.add_mem (M.add_mem hx (hM x hx)) (hM _ (hM x hx)))
  have e : x = fix3 g x + (x - fix3 g x) := by abel
  rw [e]
  exact Submodule.add_mem_sup ⟨hPx, fix3_mem h3 hg3 x⟩
    ⟨M.sub_mem hx hPx, sub_fix3_mem h3 hg3 x⟩

theorem polar_fixSp_movSp (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {b w : V}
    (hb : b ∈ fixSp g) (hw : w ∈ movSp g) : polar Q b w = 0 := by
  have hQg : ∀ v, Q (g v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have hpol : ∀ x y : V, polar Q (g x) (g y) = polar Q x y := fun x y => by
    simp only [polar, ← map_add, hQg]
  rw [mem_fixSp] at hb
  rw [mem_movSp] at hw
  have h1 : polar Q b (g w) = polar Q b w := by
    calc polar Q b (g w) = polar Q (g b) (g w) := by rw [hb]
      _ = polar Q b w := hpol b w
  have h2 : polar Q b (g (g w)) = polar Q b w := by
    calc polar Q b (g (g w)) = polar Q (g b) (g (g w)) := by rw [hb]
      _ = polar Q b (g w) := hpol b (g w)
      _ = polar Q b w := h1
  have h : (3 : K) * polar Q b w = 0 := by
    have e : polar Q b (w + g w + g (g w)) = 0 := by rw [hw, polar_zero_right]
    rw [polar_add_right, polar_add_right, h1, h2] at e
    linear_combination e
  exact (mul_eq_zero.mp h).resolve_left h3

end Cube

theorem polar_eq_zero_of_singular {S : Submodule K V} (hS : ∀ x ∈ S, Q x = 0) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) : polar Q x y = 0 := by
  rw [polar, hS _ (S.add_mem hx hy), hS x hx, hS y hy, sub_zero, sub_zero]

section Nondeg

variable [FiniteDimensional K V] (h3 : (3 : K) ≠ 0) (hg3 : ∀ v, g (g (g v)) = v)
  (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hQ : (polarBilin Q).Nondegenerate)
include h3 hg3 hg hQ

theorem two_mul_finrank_le_fixSp {S : Submodule K V} (hSB : S ≤ fixSp g)
    (hS : ∀ x ∈ S, Q x = 0) :
    2 * finrank K S + finrank K (movSp g) ≤ finrank K V := by
  have hle : S ⊔ movSp g ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) S := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => ?_
      change polar Q y x = 0
      exact polar_eq_zero_of_singular hS hy hx
    · refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => ?_
      change polar Q y x = 0
      exact polar_fixSp_movSp h3 hg3 hg (hSB hy) hx
  have hinf : S ⊓ movSp g = ⊥ :=
    le_bot_iff.mp ((fixSp_inf_movSp h3 hg3) ▸ inf_le_inf_right _ hSB)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (movSp g)
  rw [hinf, finrank_bot, add_zero] at hsum
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := Submodule.finrank_le S
  omega

theorem two_mul_finrank_le_movSp {S : Submodule K V} (hSW : S ≤ movSp g)
    (hS : ∀ x ∈ S, Q x = 0) :
    2 * finrank K S + finrank K (fixSp g) ≤ finrank K V := by
  have hle : S ⊔ fixSp g ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) S := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => ?_
      change polar Q y x = 0
      exact polar_eq_zero_of_singular hS hy hx
    · refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => ?_
      change polar Q y x = 0
      rw [polar_comm]
      exact polar_fixSp_movSp h3 hg3 hg hx (hSW hy)
  have hinf : S ⊓ fixSp g = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp ((fixSp_inf_movSp h3 hg3) ▸ inf_le_inf_left _ hSW)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (fixSp g)
  rw [hinf, finrank_bot, add_zero] at hsum
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := Submodule.finrank_le S
  omega

variable (hB : finrank K V < finrank K (fixSp g) + 4)
include hB

theorem apply_mem_span_of_singular {w : V} (hw : w ∈ movSp g) (hQw : Q w = 0) :
    g w ∈ K ∙ w := by
  by_contra hgw
  have hw0 : w ≠ 0 := fun h => hgw (by rw [h, map_zero]; exact Submodule.zero_mem _)
  have hgwW : g w ∈ movSp g := movSp_apply_mem h3 hg3 hw
  have hQg : ∀ v, Q (g v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have hQgw : Q (g w) = 0 := by rw [hQg w, hQw]
  have hpol : polar Q w (g w) = 0 := by
    have hw' := (mem_movSp).mp hw
    have hggw : g (g w) = -(w + g w) := eq_neg_of_add_eq_zero_right hw'
    have h := hQg (g w)
    rw [hQgw, hggw, QuadraticMap.map_neg, QuadraticMap.map_add Q, hQw, hQgw] at h
    simpa using h
  set T := Submodule.span K {w, g w} with hT
  have hTs : ∀ x ∈ T, Q x = 0 := by
    intro x hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hQw, hQgw, hpol]
    ring
  have hTW : T ≤ movSp g := by
    rw [hT, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hw
    · exact hgwW
  have hind : LinearIndependent K ![w, g w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hw0, ht⟩
    · exfalso
      apply hgw
      have e : g w = (-(t⁻¹ * s)) • w := by
        have := congrArg (fun z => t⁻¹ • z) hst
        simp only [smul_add, smul_smul, smul_zero] at this
        rw [inv_mul_cancel₀ ht, one_smul] at this
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right this
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hTdim : finrank K T = 2 := by
    rw [hT, show ({w, g w} : Set V) = Set.range ![w, g w] by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]]
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have := two_mul_finrank_le_movSp h3 hg3 hg hQ hTW hTs
  omega

theorem map_eq_of_singular_le_movSp {S : Submodule K V} (hSW : S ≤ movSp g)
    (hS : ∀ x ∈ S, Q x = 0) : S.map (g : V →ₗ[K] V) = S := by
  have hdim := two_mul_finrank_le_movSp h3 hg3 hg hQ hSW hS
  have h1 : finrank K S ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h1
  · rw [Submodule.finrank_eq_zero.mp h0, Submodule.map_bot]
  · have hS0 : S ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at h1
      exact zero_ne_one h1
    obtain ⟨w, hwS, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    have hspan : K ∙ w = S := Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hwS) (by rw [finrank_span_singleton hw0, h1])
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (apply_mem_span_of_singular h3 hg3 hg hQ hB (hSW hwS) (hS w hwS))
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw0 (g.injective (by rw [← hc, map_zero]))
    rw [← hspan]
    refine CFSG.RankThree.OddD4Centralizer.map_eq_of_eq_smul hc0 fun x hx => ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, ← hc, smul_comm]

end Nondeg

section Inv2

@[expose] noncomputable def inv2Map (g : V ≃ₗ[K] V) : V →ₗ[K] V :=
  (2 : K) • fix3 g - LinearMap.id

theorem inv2Map_apply (v : V) : inv2Map g v = (2 : K) • fix3 g v - v := by
  simp [inv2Map]

set_option linter.unusedSectionVars false

variable (h3 : (3 : K) ≠ 0) (hg3 : ∀ v, g (g (g v)) = v)
include h3 hg3

theorem inv2Map_involutive : Function.Involutive (inv2Map g) := by
  intro v
  simp only [inv2Map_apply, map_sub, map_smul, fix3_of_mem h3 hg3 (fix3_mem h3 hg3 v)]
  module

@[expose] noncomputable def inv2 : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (inv2Map g) (inv2Map_involutive h3 hg3)

theorem inv2_apply (v : V) : inv2 h3 hg3 v = (2 : K) • fix3 g v - v := inv2Map_apply v

theorem inv2_of_fixSp {v : V} (hv : v ∈ fixSp g) : inv2 h3 hg3 v = v := by
  rw [inv2_apply, fix3_of_mem h3 hg3 hv, two_smul, add_sub_cancel_right]

theorem inv2_of_movSp {v : V} (hv : v ∈ movSp g) : inv2 h3 hg3 v = -v := by
  rw [inv2_apply, fix3_of_mem_movSp h3 hg3 hv, smul_zero, zero_sub]

theorem inv2_mem_orthogonalGroup (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    inv2 h3 hg3 ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have hp : polar Q (fix3 g v) (v - fix3 g v) = 0 :=
    polar_fixSp_movSp h3 hg3 hg (fix3_mem h3 hg3 v) (sub_fix3_mem h3 hg3 v)
  have e1 : inv2 h3 hg3 v = fix3 g v + -(v - fix3 g v) := by
    rw [inv2_apply]
    module
  have e2 : v = fix3 g v + (v - fix3 g v) := by abel
  rw [e1]
  conv_rhs => rw [e2]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hp,
    neg_zero]

theorem map_eq_iff_map_inv2_eq [FiniteDimensional K V]
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hQ : (polarBilin Q).Nondegenerate)
    (hB : finrank K V < finrank K (fixSp g) + 4) (h2 : (2 : K) ≠ 0) {U : Submodule K V}
    (hU : ∀ x ∈ U, Q x = 0) :
    U.map (g : V →ₗ[K] V) = U ↔ U.map (inv2 h3 hg3 : V →ₗ[K] V) = U := by
  constructor
  · intro h
    have hM : ∀ x ∈ U, g x ∈ U := fun x hx => by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    have hdec := eq_sup_inf_fix3 h3 hg3 hM
    rw [hdec, Submodule.map_sup]
    congr 1
    · exact CFSG.RankThree.OddD4Centralizer.map_eq_of_eq_smul one_ne_zero fun x hx => by
        rw [inv2_of_fixSp h3 hg3 hx.2, one_smul]
    · exact CFSG.RankThree.OddD4Centralizer.map_eq_of_eq_smul (neg_ne_zero.mpr one_ne_zero)
        fun x hx => by rw [inv2_of_movSp h3 hg3 hx.2, neg_one_smul]
  · intro h
    have hM : ∀ x ∈ U, inv2 h3 hg3 x ∈ U := fun x hx => by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    have hdec := CFSG.RankThree.OddD4Centralizer.eq_sup_inf_of_map h2
      (fun x hx => inv2_of_movSp h3 hg3 hx) (fun x hx => inv2_of_fixSp h3 hg3 hx)
      (movSp_sup_fixSp h3 hg3) hM
    rw [hdec, Submodule.map_sup]
    congr 1
    · exact map_eq_of_singular_le_movSp h3 hg3 hg hQ hB inf_le_right fun x hx => hU x hx.1
    · exact CFSG.RankThree.OddD4Centralizer.map_eq_of_eq_smul one_ne_zero fun x hx => by
        rw [(mem_fixSp).mp hx.2, one_smul]

end Inv2

end OrderThree

end CFSG.HardMathSupport.Timmesfeld.DFour
