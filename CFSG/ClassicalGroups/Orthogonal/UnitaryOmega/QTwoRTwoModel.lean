module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.ThreePlaneFourierGeneration
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCentralizer
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  (E : QuadExt F K (unitaryInvolution K 2 1))


private theorem normBlock_apply_fst_eq_zero_of_fst_eq_zero {m : ℕ} {S : Finset (Fin m)}
    {a : normOmega E m} (ha : a ∈ normBlock E m S ⊓ normAnchorFixing E m)
    {v : (F × F) × (Fin m → K)} (hv1 : v.1 = 0) :
    (a.1 v).1 = 0 := by
  have hO : a.1 ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup_of_commutator
      (normHypForm E m) a.2
  have ha_anchor : ∀ w : F × F, a.1 (w, 0) = (w, 0) :=
    (mem_normAnchorFixing_iff E).mp ha.2
  have hpolar : ∀ w : F × F,
      QuadraticMap.polar (normHypForm E m) (a.1 v) (w, 0) = 0 := by
    intro w
    have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hO v (w, 0)
    rw [ha_anchor w] at h
    rw [h, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum]
    simp [hv1]
  have h1 := hpolar (1, 0)
  rw [CFSG.Timmesfeld.ClassicalOrders.polar_hypSum] at h1
  simp only [mul_zero, one_mul, add_zero, zero_add, QuadraticMap.polar_zero_right] at h1
  have h2 := hpolar (0, 1)
  rw [CFSG.Timmesfeld.ClassicalOrders.polar_hypSum] at h2
  simp only [zero_mul, mul_one, add_zero, QuadraticMap.polar_zero_right] at h2
  exact Prod.ext h2 h1

private theorem mem_suppPerp_of_mem_coordSupport_of_disjoint {m : ℕ} {S T : Finset (Fin m)}
    (hST : Disjoint S T) {v : (F × F) × (Fin m → K)} (hv1 : v.1 = 0)
    (hv : v ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
      (LinearEquiv.refl F ((F × F) × (Fin m → K))) S) :
    v ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) := by
  rw [mem_suppPerp_coordSupport_refl_iff E T]
  refine ⟨hv1, ?_⟩
  intro j hjT
  have hjS : j ∉ S := by
    intro hjS
    exact Finset.disjoint_left.mp hST hjS hjT
  rw [mem_coordSupport_refl_iff E S] at hv
  exact hv j hjS

private theorem normBlock_apply_mem_suppPerp_of_mem_coordSupport {m : ℕ} {S T : Finset (Fin m)}
    (hST : Disjoint S T) {a : normOmega E m}
    (ha : a ∈ normBlock E m S ⊓ normAnchorFixing E m)
    {v : (F × F) × (Fin m → K)} (hv1 : v.1 = 0)
    (hv : v ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
      (LinearEquiv.refl F ((F × F) × (Fin m → K))) S) :
    a.1 v ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) := by
  have ha_SD : a.val ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
      (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) S) :=
    Subgroup.mem_subgroupOf.mp ha.1
  have havS_mem : a.1 v ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
      (LinearEquiv.refl F ((F × F) × (Fin m → K))) S :=
    CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_mem ha_SD hv
  rw [mem_suppPerp_coordSupport_refl_iff E T]
  refine ⟨normBlock_apply_fst_eq_zero_of_fst_eq_zero E ha hv1, ?_⟩
  intro j hjT
  have hjS : j ∉ S := by
    intro hjS
    exact Finset.disjoint_left.mp hST hjS hjT
  rw [mem_coordSupport_refl_iff E S] at havS_mem
  exact havS_mem j hjS

private theorem normBlock_apply_eq_self_of_mem_coordSupport_of_disjoint
    {m : ℕ} {S T : Finset (Fin m)} (hST : Disjoint S T) {b : normOmega E m}
    (hb : b ∈ normBlock E m T) {v : (F × F) × (Fin m → K)} (hv1 : v.1 = 0)
    (hv : v ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
      (LinearEquiv.refl F ((F × F) × (Fin m → K))) S) :
    b.1 v = v := by
  have hb_TD : b.val ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
      (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) :=
    Subgroup.mem_subgroupOf.mp hb
  exact CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_perp hb_TD
    (mem_suppPerp_of_mem_coordSupport_of_disjoint E hST hv1 hv)

private theorem normAnchorFixing_apply_anchor_add_of_mem_suppPerp {m : ℕ} {S : Finset (Fin m)}
    {a : normOmega E m} (ha : a ∈ normBlock E m S ⊓ normAnchorFixing E m)
    {w : F × F} {u : Fin m → K}
    (hu : (0, u) ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) S)) :
    a.1 ((w, 0) + (0, u)) = (w, 0) + (0, u) := by
  have ha_anchor : ∀ w : F × F, a.1 (w, 0) = (w, 0) :=
    (mem_normAnchorFixing_iff E).mp ha.2
  have ha_SD : a.val ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
      (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) S) :=
    Subgroup.mem_subgroupOf.mp ha.1
  have h2 : a.1 (0, u) = (0, u) :=
    CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_perp ha_SD hu
  rw [map_add, ha_anchor w, h2]

private theorem normAnchorFixing_apply_of_snd_mem_suppPerp {m : ℕ} {S : Finset (Fin m)}
    {a : normOmega E m} (ha : a ∈ normBlock E m S ⊓ normAnchorFixing E m)
    {v : (F × F) × (Fin m → K)}
    (hv : (0, v.2) ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) S)) :
    a.1 v = v := by
  have hdecomp : v = (v.1, 0) + (0, v.2) := by simp
  rw [hdecomp]
  exact normAnchorFixing_apply_anchor_add_of_mem_suppPerp E ha hv

private theorem normBlock_apply_eq_add_of_mem_suppPerp {m : ℕ} {T : Finset (Fin m)}
    {b : normOmega E m} (hb : b ∈ normBlock E m T)
    {v x y : (F × F) × (Fin m → K)} (hxy : v = x + y)
    (hy : y ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T)) :
    b.1 v = b.1 x + y := by
  have hb_TD : b.val ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
      (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) :=
    Subgroup.mem_subgroupOf.mp hb
  rw [hxy, map_add,
    CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_perp hb_TD hy]

private theorem normBlock_apply_snd_eq_zero_of_mem_coordSupport_of_decomp
    {m : ℕ} {S T : Finset (Fin m)} (hST : Disjoint S T)
    {b : normOmega E m} (hb : b ∈ normBlock E m T)
    {v x y : (F × F) × (Fin m → K)} (hxy : v = x + y)
    (hx : x ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
      (LinearEquiv.refl F ((F × F) × (Fin m → K))) T)
    (hy : y ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T))
    {j : Fin m} (hjS : j ∈ S) (hyj : y.2 j = 0) :
    (b.1 v).2 j = 0 := by
  have hb_TD : b.val ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
      (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) :=
    Subgroup.mem_subgroupOf.mp hb
  have hb_x : b.1 x ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
      (LinearEquiv.refl F ((F × F) × (Fin m → K))) T :=
    CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_mem hb_TD hx
  have hjT : j ∉ T := by
    intro hjT
    exact Finset.disjoint_left.mp hST hjS hjT
  rw [hxy, map_add,
    CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_perp hb_TD hy]
  rw [mem_coordSupport_refl_iff E T] at hb_x
  simp [hb_x j hjT, hyj]

private theorem normOmega_mul_apply_eq_mul_apply_of_add_decomp {m : ℕ}
    {a b : normOmega E m} {v vS vR : (F × F) × (Fin m → K)}
    (hv : v = vS + vR)
    (haR : a.1 vR = vR) (hbS : b.1 vS = vS)
    (hb_aS : b.1 (a.1 vS) = a.1 vS) (ha_bR : a.1 (b.1 vR) = b.1 vR) :
    a.1 (b.1 v) = b.1 (a.1 v) := by
  calc a.1 (b.1 v) = a.1 (b.1 (vS + vR)) := by rw [hv]
    _ = a.1 (b.1 vS + b.1 vR) := by rw [map_add]
    _ = a.1 (vS + b.1 vR) := by rw [hbS]
    _ = a.1 vS + a.1 (b.1 vR) := by rw [map_add]
    _ = a.1 vS + b.1 vR := by rw [ha_bR]
    _ = b.1 (a.1 vS) + b.1 vR := by rw [hb_aS]
    _ = b.1 (a.1 vS + vR) := by conv_rhs => rw [map_add]
    _ = b.1 (a.1 vS + a.1 vR) := by rw [haR]
    _ = b.1 (a.1 (vS + vR)) := by simp only [map_add]
    _ = b.1 (a.1 v) := by rw [hv]

private theorem exists_coordSupport_decomposition {m : ℕ} {S T : Finset (Fin m)}
    (hST : Disjoint S T) (v : (F × F) × (Fin m → K)) :
    ∃ v_S v_off v_r x_T x_o : (F × F) × (Fin m → K),
      v = v_S + v_r ∧ v_r = x_T + x_o ∧
      v_S.1 = 0 ∧ v_off.1 = 0 ∧ v_r.2 = v_off.2 ∧
      v_S ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) S ∧
      v_off ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
        (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
          (LinearEquiv.refl F ((F × F) × (Fin m → K))) S) ∧
      x_T ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T ∧
      x_o ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
        (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
          (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) ∧
      (∀ j ∈ S, x_o.2 j = 0) := by
  let v_S : (F × F) × (Fin m → K) := (0, fun i => if i ∈ S then v.2 i else 0)
  let v_off : (F × F) × (Fin m → K) := (0, fun i => if i ∈ S then 0 else v.2 i)
  let v_r : (F × F) × (Fin m → K) := (v.1, 0) + v_off
  let x_T : (F × F) × (Fin m → K) := (v_r.1, fun i => if i ∈ T then v_r.2 i else 0)
  let x_o : (F × F) × (Fin m → K) := (0, fun i => if i ∈ T then 0 else v_r.2 i)
  refine ⟨v_S, v_off, v_r, x_T, x_o, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · simp [v_S, v_r, v_off]
    · funext i
      by_cases hi : i ∈ S <;> simp [v_S, v_r, v_off, hi]
  · refine Prod.ext ?_ ?_
    · simp [x_T, x_o]
    · funext i
      by_cases hi : i ∈ T <;> simp [x_T, x_o, hi]
  · rfl
  · rfl
  · ext i; simp [v_r]
  · rw [mem_coordSupport_refl_iff E S]
    intro j hj
    simp [v_S, hj]
  · rw [mem_suppPerp_coordSupport_refl_iff E S]
    refine ⟨rfl, ?_⟩
    intro j hj
    simp [v_off, hj]
  · rw [mem_coordSupport_refl_iff E T]
    intro j hj
    simp [x_T, hj]
  · rw [mem_suppPerp_coordSupport_refl_iff E T]
    refine ⟨rfl, ?_⟩
    intro j hj
    simp [x_o, hj]
  · intro j hjS
    have hjT : j ∉ T := fun hjT => Finset.disjoint_left.mp hST hjS hjT
    simp [x_o, hjT, v_r, v_off, hjS]
theorem commute_of_mem_normBlock_inf_normAnchorFixing {m : ℕ} {S T : Finset (Fin m)}
    (hST : Disjoint S T) {a b : normOmega E m}
    (ha : a ∈ normBlock E m S ⊓ normAnchorFixing E m) (hb : b ∈ normBlock E m T) :
    Commute a b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨v_S, v_off, v_r, x_T, x_o, hv_decomp, hvr_decomp, hvS1, hvoff1, hvr2,
    hvS_mem, hvoff_mem, hxT_mem, hxo_mem, hxo_zero⟩ :=
    exists_coordSupport_decomposition E hST v
  have ha_vr : a.1 v_r = v_r :=
    normAnchorFixing_apply_of_snd_mem_suppPerp E ha (by
      simpa [show (0, v_r.2) = v_off by ext <;> simp [hvoff1, hvr2]] using hvoff_mem)
  have hb_vS : b.1 v_S = v_S :=
    normBlock_apply_eq_self_of_mem_coordSupport_of_disjoint E hST hb hvS1 hvS_mem
  have havS_perpT : a.1 v_S ∈ CFSG.RankThree.PartOne.KCOrthogonal.suppPerp (normHypForm E m)
      (CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin m → K))) T) :=
    normBlock_apply_mem_suppPerp_of_mem_coordSupport E hST ha hvS1 hvS_mem
  have hb_avS : b.1 (a.1 v_S) = a.1 v_S :=
    CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_perp
      (Subgroup.mem_subgroupOf.mp hb) havS_perpT
  have hb_vr : b.1 v_r = b.1 x_T + x_o :=
    normBlock_apply_eq_add_of_mem_suppPerp E hb hvr_decomp hxo_mem
  have hb_vr_zeroS : ∀ j ∈ S, (b.1 v_r).2 j = 0 := by
    intro j hjS
    have hjT : j ∉ T := fun hjT => Finset.disjoint_left.mp hST hjS hjT
    exact normBlock_apply_snd_eq_zero_of_mem_coordSupport_of_decomp E hST hb hvr_decomp
      hxT_mem hxo_mem hjS (hxo_zero j hjS)
  have ha_bvr : a.1 (b.1 v_r) = b.1 v_r :=
    normAnchorFixing_apply_of_snd_mem_suppPerp E ha (by
      rw [mem_suppPerp_coordSupport_refl_iff E S]
      exact ⟨rfl, hb_vr_zeroS⟩)
  exact normOmega_mul_apply_eq_mul_apply_of_add_decomp E hv_decomp ha_vr hb_vS hb_avS ha_bvr

private theorem normPerm_mem_normAnchorFixing {n : ℕ} (hn : 3 ≤ n)
    (σ : Equiv.Perm (Fin n)) : normPerm E hn σ ∈ normAnchorFixing E n := by
  rw [mem_normAnchorFixing_iff]
  intro w
  rw [normPerm_apply E hn σ]
  rfl

private theorem conj_mem_normBlock {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    {S : Finset (Fin n)} {x : normOmega E n} (hx : x ∈ normBlock E n S) :
    normPerm E hn σ * x * (normPerm E hn σ)⁻¹ ∈ normBlock E n (S.image σ) := by
  have h := Subgroup.mem_map_of_mem
    (MulAut.conj (normPerm E hn σ)).toMonoidHom hx
  rwa [map_normBlock_normPerm E hn σ S] at h

private theorem normBlock_pair_zero_one_eq_anchorBlock :
    normBlock E 3 ({0, 1} : Finset (Fin 3)) = anchorBlock E (by norm_num : 2 ≤ 3) := by
  rw [anchorBlock_eq_normBlock]
  rfl

private theorem commute_conj_of_mem_normBlock_anchor_pair_zero_one {H : Type} [Group H]
    {κ₁ : normOmega E 3 →* H} {t : Equiv.Perm (Fin 4) →* H}
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁,
      Commute (t (Equiv.swap 2 3)) y)
    {n : normOmega E 3}
    (hn : n ∈ normBlock E 3 ({0, 1} : Finset (Fin 3)) ⊓ normAnchorFixing E 3)
    {b : normOmega E 3} (hb : b ∈ normBlock E 3 ({2} : Finset (Fin 3))) :
    Commute (κ₁ n) (t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹) := by
  have hn_anchor : n ∈ anchorBlock E (by norm_num : 2 ≤ 3) := by
    rw [← normBlock_pair_zero_one_eq_anchorBlock]
    exact hn.1
  have h1 : Commute (t (Equiv.swap 2 3)) (κ₁ n) :=
    hC (κ₁ n) (Subgroup.mem_map_of_mem κ₁ hn_anchor)
  have h2 : Commute (κ₁ n) (κ₁ b) :=
    Commute.map (commute_of_mem_normBlock_inf_normAnchorFixing E
      (S := ({0, 1} : Finset (Fin 3))) (T := ({2} : Finset (Fin 3)))
      (by decide) hn hb) κ₁
  exact (h1.symm.mul_right h2).mul_right h1.symm.inv_right

private theorem exists_conj_of_mem_normBlock_anchor_pair_one_two {H : Type} [Group H]
    {κ₁ κ₂ : normOmega E 3 →* H}
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    {n : normOmega E 3}
    (hn : n ∈ normBlock E 3 ({1, 2} : Finset (Fin 3)) ⊓ normAnchorFixing E 3) :
    ∃ y' : normOmega E 3, y' ∈ normBlock E 3 ({0, 1} : Finset (Fin 3)) ⊓
      normAnchorFixing E 3 ∧ κ₁ n = κ₂ y' := by
  let cri : normOmega E 3 := normPerm E le_rfl ((finRotate 3)⁻¹)
  let y' : normOmega E 3 := cri * n * cri⁻¹
  have hcri : cri = (normPerm E le_rfl (finRotate 3))⁻¹ := by
    simp [cri]
  have hy'_block : y' ∈ normBlock E 3 ({0, 1} : Finset (Fin 3)) := by
    have h := conj_mem_normBlock E (le_rfl : 3 ≤ 3) ((finRotate 3)⁻¹)
      (S := ({1, 2} : Finset (Fin 3))) hn.1
    rw [show (({1, 2} : Finset (Fin 3)).image
        ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3))) = {0, 1} from by decide] at h
    simpa [y', cri] using h
  have hy'_anchor : y' ∈ normAnchorFixing E 3 := by
    have hcri_anchor : cri ∈ normAnchorFixing E 3 :=
      normPerm_mem_normAnchorFixing E (le_rfl : 3 ≤ 3) _
    simpa [y'] using mul_mem (mul_mem hcri_anchor hn.2) (inv_mem hcri_anchor)
  have hy'_anchorBlock : y' ∈ anchorBlock E (by norm_num : 2 ≤ 3) := by
    rw [← normBlock_pair_zero_one_eq_anchorBlock]
    exact hy'_block
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp hy'_anchorBlock
  have hcy : normPerm E le_rfl (finRotate 3) * y' *
      (normPerm E le_rfl (finRotate 3))⁻¹ = n := by
    rw [show y' = cri * n * cri⁻¹ from rfl, hcri]
    group
  refine ⟨y', ⟨hy'_block, hy'_anchor⟩, ?_⟩
  have h := hpoint y₀
  rw [hy₀, hcy] at h
  exact h

private theorem commute_conj_of_mem_normBlock_anchor_pair_one_two {H : Type} [Group H]
    {κ₁ κ₂ : normOmega E 3 →* H} {t : Equiv.Perm (Fin 4) →* H}
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) =
      κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    {n : normOmega E 3}
    (hn : n ∈ normBlock E 3 ({1, 2} : Finset (Fin 3)) ⊓ normAnchorFixing E 3)
    {b : normOmega E 3} (hb : b ∈ normBlock E 3 ({2} : Finset (Fin 3))) :
    Commute (κ₁ n) (t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹) := by
  classical
  obtain ⟨y', hy'_mem, hky⟩ :=
    exists_conj_of_mem_normBlock_anchor_pair_one_two E hpoint hn
  let cri : normOmega E 3 := normPerm E le_rfl ((finRotate 3)⁻¹)
  let b' : normOmega E 3 := cri * b * cri⁻¹
  have hcri : cri = (normPerm E le_rfl (finRotate 3))⁻¹ := by
    simp [cri]
  have hb'_block : b' ∈ normBlock E 3 ({1} : Finset (Fin 3)) := by
    have h := conj_mem_normBlock E (le_rfl : 3 ≤ 3) ((finRotate 3)⁻¹)
      (S := ({2} : Finset (Fin 3))) hb
    rw [show (({2} : Finset (Fin 3)).image
        ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3))) = {1} from by decide] at h
    simpa [b', cri] using h
  have hb'_anchorBlock : b' ∈ anchorBlock E (by norm_num : 2 ≤ 3) := by
    rw [← normBlock_pair_zero_one_eq_anchorBlock]
    exact normBlock_mono E 3 (by decide : ({1} : Finset (Fin 3)) ⊆ {0, 1}) hb'_block
  obtain ⟨z₀, hz₀⟩ := MonoidHom.mem_range.mp hb'_anchorBlock
  have hcb : normPerm E le_rfl (finRotate 3) * b' *
      (normPerm E le_rfl (finRotate 3))⁻¹ = b := by
    rw [show b' = cri * b * cri⁻¹ from rfl, hcri]
    group
  have hkb : κ₁ b = κ₂ b' := by
    have h := hpoint z₀
    rw [hz₀, hcb] at h
    exact h
  have ht : t (Equiv.swap (2 : Fin 4) 3) =
      κ₂ (normPerm E le_rfl (Equiv.swap (1 : Fin 3) 2)) := by
    have h := DFunLike.congr_fun ht₂ (Equiv.swap (1 : Fin 3) 2)
    simp only [MonoidHom.comp_apply] at h
    rw [← h, CFSG.Permutation.viaEmbeddingHom_swap]
    rw [show (Fin.succEmb 3) (1 : Fin 3) = (2 : Fin 4) from Fin.ext rfl,
      show (Fin.succEmb 3) (2 : Fin 3) = (3 : Fin 4) from Fin.ext rfl]
  let b'' : normOmega E 3 := normPerm E le_rfl (Equiv.swap (1 : Fin 3) 2) * b' *
    (normPerm E le_rfl (Equiv.swap (1 : Fin 3) 2))⁻¹
  have hb''_block : b'' ∈ normBlock E 3 ({2} : Finset (Fin 3)) := by
    have h := conj_mem_normBlock E (le_rfl : 3 ≤ 3) (Equiv.swap (1 : Fin 3) 2)
      (S := ({1} : Finset (Fin 3))) hb'_block
    rw [show (({1} : Finset (Fin 3)).image (Equiv.swap (1 : Fin 3) 2)) = {2}
      from by decide] at h
    simpa [b''] using h
  have hcomm : Commute (κ₂ y') (κ₂ b'') :=
    Commute.map (commute_of_mem_normBlock_inf_normAnchorFixing E
      (S := ({0, 1} : Finset (Fin 3))) (T := ({2} : Finset (Fin 3)))
      (by decide) hy'_mem hb''_block) κ₂
  rw [hky, hkb, ht]
  simpa [b'', map_mul, map_inv] using hcomm

private theorem commute_conj_of_mem_normBlock_anchor_pair_zero_two {H : Type} [Group H]
    {κ₁ κ₂ : normOmega E 3 →* H} {t : Equiv.Perm (Fin 4) →* H}
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁,
      Commute (t (Equiv.swap 2 3)) y)
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) =
      κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    {n : normOmega E 3}
    (hn : n ∈ normBlock E 3 ({0, 2} : Finset (Fin 3)) ⊓ normAnchorFixing E 3)
    {b : normOmega E 3} (hb : b ∈ normBlock E 3 ({2} : Finset (Fin 3))) :
    Commute (κ₁ n) (t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹) := by
  classical
  set X : H := t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹
  let s₀ : normOmega E 3 := normPerm E le_rfl (Equiv.swap (0 : Fin 3) 1)
  have hs₀_block : s₀ ∈ normBlock E 3 ({0, 1} : Finset (Fin 3)) := by
    simpa [s₀] using normPerm_swap_mem_normBlock E (le_rfl : 3 ≤ 3) (0 : Fin 3) 1
  have hs₀_anchor : s₀ ∈ normAnchorFixing E 3 := by
    simpa [s₀] using
      normPerm_mem_normAnchorFixing E (le_rfl : 3 ≤ 3) (Equiv.swap (0 : Fin 3) 1)
  have h0 : Commute (κ₁ s₀) X :=
    commute_conj_of_mem_normBlock_anchor_pair_zero_one E hC ⟨hs₀_block, hs₀_anchor⟩ hb
  let n'' : normOmega E 3 := s₀ * n * s₀⁻¹
  have hn''_block : n'' ∈ normBlock E 3 ({1, 2} : Finset (Fin 3)) := by
    have h := conj_mem_normBlock E (le_rfl : 3 ≤ 3) (Equiv.swap (0 : Fin 3) 1)
      (S := ({0, 2} : Finset (Fin 3))) hn.1
    rw [show (({0, 2} : Finset (Fin 3)).image (Equiv.swap (0 : Fin 3) 1)) = {1, 2}
      from by decide] at h
    simpa [n'', s₀] using h
  have hn''_anchor : n'' ∈ normAnchorFixing E 3 := by
    have h := mul_mem (mul_mem hs₀_anchor hn.2) (inv_mem hs₀_anchor)
    simpa [n''] using h
  have h12 : Commute (κ₁ n'') X :=
    commute_conj_of_mem_normBlock_anchor_pair_one_two E ht₂ hpoint
      ⟨hn''_block, hn''_anchor⟩ hb
  have hn_eq : n = s₀⁻¹ * n'' * s₀ := by
    rw [show n'' = s₀ * n * s₀⁻¹ from rfl]
    group
  have hκ : κ₁ n = (κ₁ s₀)⁻¹ * κ₁ n'' * κ₁ s₀ := by
    rw [hn_eq, map_mul, map_mul, map_inv]
  have hfinal : Commute ((κ₁ s₀)⁻¹ * κ₁ n'' * κ₁ s₀) X :=
    (h0.inv_left.mul_left h12).mul_left h0
  rwa [← hκ] at hfinal

private theorem card_two_finset_fin_three {S : Finset (Fin 3)} (hS : S.card = 2) :
    S = ({0, 1} : Finset (Fin 3)) ∨ S = ({0, 2} : Finset (Fin 3)) ∨
      S = ({1, 2} : Finset (Fin 3)) := by
  obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hS
  rw [hSab]
  fin_cases a <;> fin_cases b <;> simp_all <;> decide

theorem commute_conj_of_mem_normBlock_inf_normAnchorFixing_three {H : Type} [Group H]
    {κ₁ κ₂ : normOmega E 3 →* H} {t : Equiv.Perm (Fin 4) →* H}
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁, Commute (t (Equiv.swap 2 3)) y)
    {S : Finset (Fin 3)} (hS : S.card = 2) {n : normOmega E 3}
    (hn : n ∈ normBlock E 3 S ⊓ normAnchorFixing E 3) {b : normOmega E 3}
    (hb : b ∈ normBlock E 3 {2}) :
    Commute (κ₁ n) (t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹) := by
  rcases card_two_finset_fin_three hS with hS01 | hS02 | hS12
  · rw [hS01] at hn
    exact commute_conj_of_mem_normBlock_anchor_pair_zero_one E hC hn hb
  · rw [hS02] at hn
    exact commute_conj_of_mem_normBlock_anchor_pair_zero_two E hC ht₂ hpoint hn hb
  · rw [hS12] at hn
    exact commute_conj_of_mem_normBlock_anchor_pair_one_two E ht₂ hpoint hn hb

variable (χ : Multiplicative (ZMod 3) →* Kˣ)

@[expose] noncomputable def qTwoRTwoD : normOmega E 3 :=
  normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
    fun _ => Multiplicative.ofAdd 1

@[expose] noncomputable def qTwoRTwoA : normOmega E 3 :=
  normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
    ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2]

@[expose] noncomputable def qTwoRTwoU : Subgroup (normOmega E 3) :=
  Subgroup.closure {qTwoRTwoD E χ, qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)}

private theorem mem_iSup_pairs_of_mem {S : Finset (Fin 3)} (hS : S.card = 2)
    {g : normOmega E 3} (hg : g ∈ normBlock E 3 S ⊓ normAnchorFixing E 3) :
    g ∈ ⨆ (S : Finset (Fin 3)) (_ : S.card = 2),
      normBlock E 3 S ⊓ normAnchorFixing E 3 :=
  Subgroup.mem_iSup_of_mem S (Subgroup.mem_iSup_of_mem hS hg)

private theorem normPlaneTorus_mem_pair (u : Fin 3 → Multiplicative (ZMod 3))
    {S : Finset (Fin 3)} (hu : ∀ i, i ∉ S → u i = 1) :
    normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ u ∈
      normBlock E 3 S ⊓ normAnchorFixing E 3 := by
  constructor
  · exact normPlaneTorus_mem_normBlock_of_support E (by norm_num) χ S u hu
  · change normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ u ∈
      normAnchorFixing E 3
    rw [mem_normAnchorFixing_iff]
    intro w
    rw [normPlaneTorus_apply]
    simp
    rfl

private theorem normPerm_swap_mem_pair (i j : Fin 3) (hij : i ≠ j) :
    normPerm E le_rfl (Equiv.swap i j) ∈
      ⨆ (S : Finset (Fin 3)) (_ : S.card = 2),
        normBlock E 3 S ⊓ normAnchorFixing E 3 := by
  refine Subgroup.mem_iSup_of_mem ({i, j} : Finset (Fin 3))
    (Subgroup.mem_iSup_of_mem (Finset.card_pair hij) ?_)
  constructor
  · exact normPerm_swap_mem_normBlock E le_rfl i j
  · change normPerm E le_rfl (Equiv.swap i j) ∈ normAnchorFixing E 3
    rw [mem_normAnchorFixing_iff]
    intro w
    rw [normPerm_apply]
    simp
    rfl

private theorem qTwoRTwoD_eq_pairProduct :
    qTwoRTwoD E χ =
      normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
        ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 2, 1] *
      normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
        ![1, Multiplicative.ofAdd 2, Multiplicative.ofAdd 1] := by
  have hd0 : qTwoRTwoD E χ = normPlaneTorus E (by norm_num : 2 ≤ 3)
      (by decide : 3 ∣ 2 ^ 1 + 1) χ (fun _ => Multiplicative.ofAdd 1) := rfl
  have hcoord : (fun _ : Fin 3 => Multiplicative.ofAdd (1 : ZMod 3)) =
      ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 2, 1] *
        ![1, Multiplicative.ofAdd 2, Multiplicative.ofAdd 1] := by
    funext i
    fin_cases i
    · change Multiplicative.ofAdd (1 : ZMod 3) =
        Multiplicative.ofAdd 1 * (1 : Multiplicative (ZMod 3))
      rw [mul_one]
    · change Multiplicative.ofAdd (1 : ZMod 3) =
        Multiplicative.ofAdd 2 * Multiplicative.ofAdd 2
      rw [← ofAdd_add, show (2 : ZMod 3) + 2 = 1 by decide]
    · change Multiplicative.ofAdd (1 : ZMod 3) =
        (1 : Multiplicative (ZMod 3)) * Multiplicative.ofAdd 1
      rw [one_mul]
  rw [hd0, ← map_mul]
  exact congrArg (normPlaneTorus E (by norm_num : 2 ≤ 3)
    (by decide : 3 ∣ 2 ^ 1 + 1) χ) hcoord

theorem qTwoRTwoU_le_iSup_pairs :
    qTwoRTwoU E χ ≤ ⨆ (S : Finset (Fin 3)) (_ : S.card = 2),
      normBlock E 3 S ⊓ normAnchorFixing E 3 := by
  change Subgroup.closure
      {qTwoRTwoD E χ, qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} ≤
    ⨆ (S : Finset (Fin 3)) (_ : S.card = 2), normBlock E 3 S ⊓ normAnchorFixing E 3
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [qTwoRTwoD_eq_pairProduct]
    refine mul_mem ?_ ?_
    · refine mem_iSup_pairs_of_mem (E := E) (S := {0, 1}) (by decide) ?_
      exact normPlaneTorus_mem_pair (E := E) (χ := χ)
        ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 2, 1] (by
          intro i hi
          fin_cases i
          · simp at hi
          · simp at hi
          · rfl)
    · refine mem_iSup_pairs_of_mem (E := E) (S := {1, 2}) (by decide) ?_
      exact normPlaneTorus_mem_pair (E := E) (χ := χ)
        ![1, Multiplicative.ofAdd 2, Multiplicative.ofAdd 1] (by
          intro i hi
          fin_cases i
          · rfl
          · simp at hi
          · simp at hi)
  · refine mem_iSup_pairs_of_mem (E := E) (S := {1, 2}) (by decide) ?_
    exact normPlaneTorus_mem_pair (E := E) (χ := χ)
      ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2] (by
        intro i hi
        fin_cases i
        · rfl
        · simp at hi
        · simp at hi)
  · have hc : normPerm E le_rfl (finRotate 3) =
        normPerm E le_rfl (Equiv.swap 0 1) * normPerm E le_rfl (Equiv.swap 1 2) := by
      rw [show finRotate 3 = Equiv.swap 0 1 * Equiv.swap 1 2 from by decide, map_mul]
    rw [hc]
    exact mul_mem (normPerm_swap_mem_pair (E := E) 0 1 (by decide))
      (normPerm_swap_mem_pair (E := E) 1 2 (by decide))

omit [Finite K] [CharP K 2] in
theorem one_add_add_sq_eq_zero_of_injective {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hχ : Function.Injective χ) :
    1 + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 =
      0 := by
  set ω : K := ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) with hω
  have h3 : ω ^ 3 = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val, ← map_pow]
    have hcube : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide
    rw [hcube, map_one, Units.val_one]
  have h1 : ω ≠ 1 := by
    intro h
    rw [hω] at h
    have hunit : χ (Multiplicative.ofAdd 1) = χ 1 := by
      rw [map_one χ]
      exact Units.ext h
    have hof : (Multiplicative.ofAdd (1 : ZMod 3)) = 1 := hχ hunit
    exact absurd hof (by decide)
  have hprod : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 := by ring
    rw [h, h3, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

theorem unitaryInvolution_two_one_apply (ω : K) : unitaryInvolution K 2 1 ω = ω ^ 2 := by
  rw [unitaryInvolution_apply, pow_one]

private theorem qTwoRTwoD_apply (v : (F × F) × (Fin 3 → K)) :
    ((qTwoRTwoD E χ : normOmega E 3) :
      ((F × F) × (Fin 3 → K)) ≃ₗ[F] ((F × F) × (Fin 3 → K))) v =
      (v.1, ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) • v.2) := by
  simp only [qTwoRTwoD, normPlaneTorus_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  simp [Pi.smul_apply, smul_eq_mul]

private theorem threePlaneFourier_apply {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (v : (F × F) × (Fin 3 → K)) :
    ((threePlaneFourier E hσ hs : normOmega E 3) :
      ((F × F) × (Fin 3 → K)) ≃ₗ[F] ((F × F) × (Fin 3 → K))) v =
      (v.1, Matrix.mulVec (CFSG.AGLEmbedding.fourierMatThree ω) v.2) := by
  simp only [threePlaneFourier, suEmb_apply, CFSG.ClassicalGroups.Unitary.smul_def,
    CFSG.AGLEmbedding.fourierElt,
    CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.coe_mkSUid]

private theorem qTwoRTwoA_eq_suEmb
    (hσ : unitaryInvolution K 2 1 ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) =
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) +
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 = 0) :
    qTwoRTwoA E χ = suEmb E 3 (CFSG.AGLEmbedding.heisXSU hσ hs) := by
  have hω2 : ((χ (Multiplicative.ofAdd (2 : ZMod 3)) : Kˣ) : K) =
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 := by
    have h2 : Multiplicative.ofAdd (2 : ZMod 3) =
        (Multiplicative.ofAdd 1 : Multiplicative (ZMod 3)) ^ 2 := by
      have h : (2 : ZMod 3) = 1 + 1 := by norm_num
      rw [h, pow_two]
      rfl
    rw [h2, map_pow]
    rfl
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [qTwoRTwoA, normPlaneTorus_apply, suEmb_apply,
    CFSG.ClassicalGroups.Unitary.smul_def, CFSG.AGLEmbedding.heisXSU,
    CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.coe_mkSUid]
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i <;>
    simp [CFSG.AGLEmbedding.heisXMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hω2]

private theorem normPerm_finRotate_eq_suEmb :
    normPerm E le_rfl (finRotate 3) = suEmb E 3 CFSG.AGLEmbedding.heisYSU := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [normPerm_apply, suEmb_apply, CFSG.ClassicalGroups.Unitary.smul_def,
    CFSG.AGLEmbedding.heisYSU,
    CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.coe_mkSUid]
  refine Prod.ext rfl (funext fun j => ?_)
  fin_cases j <;>
    simp [CFSG.AGLEmbedding.heisYMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      show (finRotate 3)⁻¹ (0 : Fin 3) = 2 by decide,
      show (finRotate 3)⁻¹ (1 : Fin 3) = 0 by decide,
      show (finRotate 3)⁻¹ (2 : Fin 3) = 1 by decide]

private theorem qTwoRTwoD_commute_threePlaneFourier
    (hσ : unitaryInvolution K 2 1 ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) =
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) +
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 = 0) :
    threePlaneFourier E hσ hs * qTwoRTwoD E χ =
      qTwoRTwoD E χ * threePlaneFourier E hσ hs := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, qTwoRTwoD_apply,
    threePlaneFourier_apply, Matrix.mulVec_smul]

private theorem qTwoRTwoD_conj_threePlaneFourier
    (hσ : unitaryInvolution K 2 1 ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) =
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) +
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 = 0) :
    threePlaneFourier E hσ hs * qTwoRTwoD E χ * (threePlaneFourier E hσ hs)⁻¹ =
      qTwoRTwoD E χ := by
  have hcomm := qTwoRTwoD_commute_threePlaneFourier (E := E) (χ := χ) hσ hs
  rw [hcomm, mul_inv_cancel_right]

private theorem threePlaneFourier_mem_normalizer_pair
    (hσ : unitaryInvolution K 2 1 ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) =
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) +
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 = 0) :
    threePlaneFourier E hσ hs ∈ Subgroup.normalizer (Subgroup.closure
      ({qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} : Set (normOmega E 3))) := by
  have hX : qTwoRTwoA E χ = suEmb E 3 (CFSG.AGLEmbedding.heisXSU hσ hs) :=
    qTwoRTwoA_eq_suEmb (E := E) (χ := χ) hσ hs
  have hY : normPerm E le_rfl (finRotate 3) = suEmb E 3 CFSG.AGLEmbedding.heisYSU :=
    normPerm_finRotate_eq_suEmb E
  have hmap : (Subgroup.closure ({CFSG.AGLEmbedding.heisXSU hσ hs,
      CFSG.AGLEmbedding.heisYSU} :
        Set (CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution K 2 1) 3))).map
        (suEmb E 3) =
      Subgroup.closure ({qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} :
        Set (normOmega E 3)) := by
    rw [MonoidHom.map_closure, Set.image_pair, ← hX, ← hY]
  have hmem : threePlaneFourier E hσ hs ∈
      (Subgroup.normalizer (Subgroup.closure ({CFSG.AGLEmbedding.heisXSU hσ hs,
        CFSG.AGLEmbedding.heisYSU} :
          Set (CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution K 2 1) 3)))).map
          (suEmb E 3) :=
    Subgroup.mem_map_of_mem (suEmb E 3)
      (CFSG.AGLEmbedding.fourierElt_mem_normalizer hσ hs)
  have hmem' := Subgroup.le_normalizer_map (suEmb E 3) hmem
  rw [hmap] at hmem'
  exact hmem'

theorem map_conj_threePlaneFourier_qTwoRTwoU
    (hσ : unitaryInvolution K 2 1 ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) =
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) +
      ((χ (Multiplicative.ofAdd 1) : Kˣ) : K) ^ 2 = 0) :
    (qTwoRTwoU E χ).map (MulAut.conj (threePlaneFourier E hσ hs)).toMonoidHom = qTwoRTwoU E χ :=
  letI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  letI : Finite (normOmega E 3) := Subtype.finite
  (Subgroup.mem_normalizer_iff_map_conj_eq).mp (by
    have hD := qTwoRTwoD_conj_threePlaneFourier (E := E) (χ := χ) hσ hs
    have hpair := threePlaneFourier_mem_normalizer_pair (E := E) (χ := χ) hσ hs
    have hpair' : ∀ x : normOmega E 3,
        x ∈ Subgroup.closure ({qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} :
          Set (normOmega E 3)) ↔
        threePlaneFourier E hσ hs * x * (threePlaneFourier E hσ hs)⁻¹ ∈
          Subgroup.closure ({qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} :
            Set (normOmega E 3)) :=
      Subgroup.mem_normalizer_iff.mp hpair
    have hsub : Subgroup.closure ({qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} :
          Set (normOmega E 3)) ≤
        Subgroup.closure ({qTwoRTwoD E χ, qTwoRTwoA E χ,
          normPerm E le_rfl (finRotate 3)} : Set (normOmega E 3)) :=
      Subgroup.closure_mono (by rintro x (rfl | rfl) <;> simp)
    change threePlaneFourier E hσ hs ∈ Subgroup.normalizer (Subgroup.closure
      ({qTwoRTwoD E χ, qTwoRTwoA E χ, normPerm E le_rfl (finRotate 3)} :
        Set (normOmega E 3)))
    refine CFSG.AGLEmbedding.mem_normalizer_closure_of_forall_conj_mem ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · rw [hD]
      exact Subgroup.subset_closure (by simp)
    · exact hsub ((hpair' _).mp (Subgroup.subset_closure (by simp)))
    · exact hsub ((hpair' _).mp (Subgroup.subset_closure (by simp))))

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
