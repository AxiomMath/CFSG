module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413Model
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413LA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413U
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.L413

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Steinberg.CentralExt CliffordAlgebra Subgroup
open scoped MatrixGroups

theorem centralizer_mul_central {G : Type*} [Group G] (x : G) {c : G} (hc : c ∈ center G) :
    centralizer ({x * c} : Set G) = centralizer {x} := by
  have hc' := mem_center_iff.mp hc
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine mul_right_cancel (b := c) ?_
    calc g * x * c = g * (x * c) := mul_assoc _ _ _
      _ = x * c * g := h
      _ = x * (c * g) := mul_assoc _ _ _
      _ = x * (g * c) := by rw [hc' g]
      _ = x * g * c := (mul_assoc _ _ _).symm
  · intro h
    calc g * (x * c) = g * x * c := (mul_assoc _ _ _).symm
      _ = x * g * c := by rw [h]
      _ = x * (g * c) := mul_assoc _ _ _
      _ = x * (c * g) := by rw [hc' g]
      _ = x * c * g := (mul_assoc _ _ _).symm

variable {K : Type} [Field K]

theorem centralizer_inv4 (i : Fin 4) :
    centralizer ({inv4 K i} : Set (spinGroup (quadPlus 4 K))) = centralizer {inv4 K 1} := by
  obtain ⟨c, hc, h⟩ := exists_mem_center_inv4_eq (K := K) i
  rw [h, centralizer_mul_central _ hc]

theorem rt_le_centralizer (i : Fin 4) :
    (rt K i).range ≤ centralizer ({inv4 K 1} : Set (spinGroup (quadPlus 4 K))) := by
  rw [← centralizer_inv4 i]
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact commute_inv4 i hx

theorem centralizer_le_normalizer_rt (h2 : (2 : K) ≠ 0) (i : Fin 4) :
    centralizer ({inv4 K 1} : Set (spinGroup (quadPlus 4 K))) ≤
      normalizer ((rt K i).range : Set (spinGroup (quadPlus 4 K))) := by
  rw [← centralizer_inv4 i]
  have hQ := nondegenerate_quadPlus 4 K
  fin_cases i
  · exact CFSG.LieType.HighestRoot.centralizer_le_normalizer_longSL2 (frame8 K) _ _ _ h2 hQ
  · exact CFSG.LieType.HighestRoot.centralizer_le_normalizer_longSL2 (frame8 K) _ _ _ h2 hQ
  · exact CFSG.LieType.HighestRoot.centralizer_le_normalizer_longSL2 (frame8 K) _ _ _ h2 hQ
  · exact CFSG.LieType.HighestRoot.centralizer_le_normalizer_longSL2 (frame8 K) _ _ _ h2 hQ

theorem mem_rt_of_commute_aux (h2 : (2 : K) ≠ 0) {j a b c : Fin 4}
    (hsw : (pl K j).swap = pl K a) (hperp : (pl K j).perp ≤ (pl K b).span)
    (hsw' : (pl K b).swap = pl K c) {y : spinGroup (quadPlus 4 K)} (hy : y ^ 3 = 1)
    (ha : ∀ s ∈ (rt K a).range, y * s = s * y) (hb : ∀ s ∈ (rt K b).range, y * s = s * y)
    (hc : ∀ s ∈ (rt K c).range, y * s = s * y) : y ∈ (rt K j).range := by
  have hO : spinAction (quadPlus 4 K) y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ y)
  have hcomm : ∀ k, (∀ s ∈ (rt K k).range, y * s = s * y) → ∀ B : SL(2, K),
      spinAction (quadPlus 4 K) y * (pl K k).La B =
        (pl K k).La B * spinAction (quadPlus 4 K) y := fun k hk B => by
    rw [← spinAction_rt, ← map_mul, ← map_mul, hk _ ⟨B, rfl⟩]
  obtain ⟨M, hM⟩ := exists_eq_La_of_commute h2 (pl K j) (pl K b) hperp hO
    (by rw [← map_pow, hy, map_one]) (fun B => by rw [hsw]; exact hcomm a ha B) (hcomm b hb)
    (fun B => by rw [hsw']; exact hcomm c hc B)
  have hk : y * (rt K j M)⁻¹ ∈ (spinAction (quadPlus 4 K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, spinAction_rt, ← hM, mul_inv_cancel]
  have hkc := mem_center_iff.mp (ker_spinAction_le_center _ hk)
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hk2 : (y * (rt K j M)⁻¹) * (y * (rt K j M)⁻¹) = 1 := by
    rcases (mem_ker_spinAction_iff _ (nondegenerate_quadPlus 4 K) _).mp hk with h | h
    · rw [h, one_mul]
    · rw [h, spinGroup.negOne_mul_self]
  set k := y * (rt K j M)⁻¹ with hkdef
  have hyk : y = k * rt K j M := by rw [hkdef, inv_mul_cancel_right]
  have hcomm' : Commute k (rt K j M) := (hkc (rt K j M)).symm
  have hy4 : y = rt K j (M ^ 4) := by
    calc y = y ^ 3 * y := by rw [hy, one_mul]
      _ = (k * rt K j M) ^ 4 := by rw [← pow_succ, ← hyk]
      _ = k ^ 4 * rt K j M ^ 4 := hcomm'.mul_pow 4
      _ = rt K j (M ^ 4) := by
        rw [map_pow, show k ^ 4 = k * k * (k * k) by
          rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc], hk2,
          mul_one, one_mul]
  rw [hy4]
  exact ⟨_, rfl⟩

theorem mem_rt_of_commute (h2 : (2 : K) ≠ 0) (j : Fin 4) {y : spinGroup (quadPlus 4 K)}
    (hy : y ^ 3 = 1) (hc : ∀ k, k ≠ j → ∀ s ∈ (rt K k).range, y * s = s * y) :
    y ∈ (rt K j).range := by
  fin_cases j
  · exact mem_rt_of_commute_aux h2 pl_zero_swap (perp_le_span_zero true false) pl_two_swap hy
      (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide))
  · exact mem_rt_of_commute_aux h2 pl_one_swap (perp_le_span_zero true true) pl_two_swap hy
      (hc 0 (by decide)) (hc 2 (by decide)) (hc 3 (by decide))
  · exact mem_rt_of_commute_aux h2 pl_two_swap (perp_le_span_two true false) pl_zero_swap hy
      (hc 3 (by decide)) (hc 0 (by decide)) (hc 1 (by decide))
  · exact mem_rt_of_commute_aux h2 pl_three_swap (perp_le_span_two true true) pl_zero_swap hy
      (hc 2 (by decide)) (hc 0 (by decide)) (hc 1 (by decide))

theorem finite_spin8 [Finite K] : Finite (spinGroup (quadPlus 4 K)) :=
  CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
    (coe_ker_spinMatrix_quadPlus (n := 4) (K := K))

theorem map_rt_range [Finite K] (hodd : Odd (Nat.card K)) (h3K : 3 ≤ Nat.card K)
    (h3 : (3 : K) = 0) (β : MulAut (spinGroup (quadPlus 4 K))) {i j : Fin 4}
    (h : β (inv4 K i) = inv4 K j) : (rt K i).range.map β.toMonoidHom = (rt K j).range := by
  have : Finite (spinGroup (quadPlus 4 K)) := finite_spin8
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hCi := centralizer_inv4 (K := K) i
  have hCj := centralizer_inv4 (K := K) j
  set C := centralizer ({inv4 K 1} : Set (spinGroup (quadPlus 4 K))) with hC
  have hCle : C ≤ C.map β.toMonoidHom := by
    intro g hg
    refine ⟨β.symm g, ?_, by simp⟩
    rw [← hCi, SetLike.mem_coe, mem_centralizer_singleton_iff]
    rw [← hCj, mem_centralizer_singleton_iff] at hg
    apply β.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]
    exact hg
  have hCge : C.map β.toMonoidHom ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hCj, mem_centralizer_singleton_iff]
    rw [← hCi, SetLike.mem_coe, mem_centralizer_singleton_iff] at hg
    show β g * inv4 K j = inv4 K j * β g
    rw [← h, ← map_mul, ← map_mul, hg]
  rw [← MonoidHom.range_comp]
  refine range_eq_of_normal hodd h3K h3 (fun k => (rt K k).range) (inv4 K) C rt_le_centralizer
    (centralizer_le_normalizer_rt h2)
    (fun k => ⟨(MonoidHom.ofInjective (rt_injective k)).symm⟩) inv4_mem (orderOf_inv4 h2)
    (inv4_injective h2) (fun k y hy hc => mem_rt_of_commute h2 k hy hc)
    (β.injective.comp (rt_injective i)) ?_ ?_ ⟨-1, h⟩
  · rw [MonoidHom.range_comp]
    exact (map_mono (rt_le_centralizer i)).trans hCge
  · rw [MonoidHom.range_comp]
    exact hCle.trans ((map_mono (centralizer_le_normalizer_rt h2 i)).trans
      (le_normalizer_map _))

end CFSG.ComponentClassification.HarrisLit.T1.L413
