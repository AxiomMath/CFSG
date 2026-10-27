module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LP16
public import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {P : Type} [Group P]

theorem y2l_conj_pow_mem {T : Subgroup P} {a : P} (ha : ∀ y ∈ T, a⁻¹ * y * a ∈ T) :
    ∀ k : ℕ, ∀ y ∈ T, (a ^ k)⁻¹ * y * a ^ k ∈ T
  | 0, y, hy => by simpa using hy
  | k + 1, y, hy => by
    have e : (a ^ (k + 1))⁻¹ * y * a ^ (k + 1) = a⁻¹ * ((a ^ k)⁻¹ * y * a ^ k) * a := by
      rw [pow_succ]
      group
    rw [e]
    exact ha _ (y2l_conj_pow_mem ha k y hy)

theorem y2l_normal_of_gen [Finite P] {X S : Set P} (hX : closure X = ⊤)
    (h : ∀ x ∈ X, ∀ y ∈ S, x⁻¹ * y * x ∈ closure S) : (closure S).Normal := by
  have hS : ∀ a : P, (∀ y ∈ S, a⁻¹ * y * a ∈ closure S) →
      ∀ y ∈ closure S, a⁻¹ * y * a ∈ closure S := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact ha y hy
    | one => simp
    | mul y z _ _ hy hz =>
      rw [show a⁻¹ * (y * z) * a = a⁻¹ * y * a * (a⁻¹ * z * a) by group]
      exact mul_mem hy hz
    | inv y _ hy =>
      rw [show a⁻¹ * y⁻¹ * a = (a⁻¹ * y * a)⁻¹ by group]
      exact inv_mem hy
  have key : ∀ g ∈ closure X, ∀ y ∈ closure S, g⁻¹ * y * g ∈ closure S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hS x (h x hx)
    | one => simp
    | mul a b _ _ ha hb =>
      intro y hy
      rw [show (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b by group]
      exact hb _ (ha y hy)
    | inv a _ ha =>
      have hn : a⁻¹ = a ^ (orderOf a - 1) := (eq_inv_of_mul_eq_one_left (by
        rw [pow_sub_one_mul (orderOf_pos a).ne', pow_orderOf_eq_one])).symm
      rw [hn]
      exact y2l_conj_pow_mem ha _
  refine ⟨fun y hy g => ?_⟩
  have h' := key g⁻¹ (by rw [hX]; exact mem_top _) y hy
  rwa [inv_inv] at h'

theorem y2l_closure_eq_top {n : ℕ} {e : Bool} {u v w r s : P}
    (hP : IsPres26 n e P u v w r s) : closure ({u, v, w, r, s} : Set P) = ⊤ := by
  obtain ⟨h, hb⟩ := hP
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨p, rfl⟩ := hb.2 x
  have hmem : ∀ i : Fin 5,
      (![u, v, w, r, s] : Fin 5 → P) i ∈ closure ({u, v, w, r, s} : Set P) := by
    intro i
    apply Subgroup.subset_closure
    fin_cases i <;> simp
  exact PresentedGroup.generated_by _
    ((Subgroup.closure ({u, v, w, r, s} : Set P)).comap (PresentedGroup.toGroup h))
    (fun j => by rw [Subgroup.mem_comap, PresentedGroup.toGroup.of]; exact hmem j) p

theorem y2l_commute_of_mem {u v w : P} (huv : Commute u v) (huw : Commute u w)
    (hvw : Commute v w) {a b : P} (ha : a ∈ closure ({u, v, w} : Set P))
    (hb : b ∈ closure ({u, v, w} : Set P)) : Commute a b := by
  have h1 : ∀ x ∈ ({u, v, w} : Set P), ∀ y ∈ ({u, v, w} : Set P), Commute x y := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption | exact Commute.symm ‹_›
  have h2 : ∀ x ∈ ({u, v, w} : Set P), ∀ y ∈ closure ({u, v, w} : Set P), Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h1 x hx y hy
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx b hb
  | one => exact Commute.one_left b
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem y2l_mem_omega1 {u v w : P} (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w)
    {y : P} (hy : y ∈ omega1 (closure ({u, v, w} : Set P))) :
    y ∈ closure ({u, v, w} : Set P) ∧ y ^ 2 = 1 := by
  rw [omega1] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨one_mem _, one_pow 2⟩
  | mul a b _ _ ha hb =>
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [(y2l_commute_of_mem huv huw hvw ha.1 hb.1).mul_pow, ha.2, hb.2, one_mul]
  | inv a _ ha => exact ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem y2l_omega1_normal {T : Subgroup P} (hT : T.Normal) : (omega1 T).Normal := by
  rw [omega1]
  refine Subgroup.closure_normal_of_forall_conj_mem fun g y hy => ⟨hT.conj_mem y hy.1 g, ?_⟩
  rw [conj_pow, hy.2, mul_one, mul_inv_cancel]

@[expose] def y2l_qTop (N : Subgroup P) [(N.subgroupOf ⊤).Normal] :
    P →* ↥(⊤ : Subgroup P) ⧸ N.subgroupOf ⊤ :=
  (QuotientGroup.mk' (N.subgroupOf ⊤)).comp
    (Subgroup.topEquiv.symm : P ≃* ↥(⊤ : Subgroup P)).toMonoidHom

theorem y2l_qTop_eq_one_iff (N : Subgroup P) [(N.subgroupOf ⊤).Normal] (x : P) :
    y2l_qTop N x = 1 ↔ x ∈ N := by
  change QuotientGroup.mk (Subgroup.topEquiv.symm x) =
    (1 : ↥(⊤ : Subgroup P) ⧸ N.subgroupOf ⊤) ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem y2l_qTop_surjective (N : Subgroup P) [(N.subgroupOf ⊤).Normal] :
    Function.Surjective (y2l_qTop N) := fun q => by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨(z : P), rfl⟩

variable [Finite P] {u v w r s : P}

theorem y2l_T_normal {n : ℕ} {e : Bool} (hP : IsPres26 n e P u v w r s) :
    (closure ({u, v, w} : Set P)).Normal := by
  have hR := y2l_rels_iff.mp hP.1
  have hT : ∀ z ∈ ({u, v, w} : Set P), z ∈ closure ({u, v, w} : Set P) :=
    fun z hz => subset_closure hz
  refine y2l_normal_of_gen (y2l_closure_eq_top hP) fun x hx y hy => ?_
  have hyT := hT y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact mul_mem (mul_mem (inv_mem (hT _ (by simp))) hyT) (hT _ (by simp))
  · exact mul_mem (mul_mem (inv_mem (hT _ (by simp))) hyT) (hT _ (by simp))
  · exact mul_mem (mul_mem (inv_mem (hT _ (by simp))) hyT) (hT _ (by simp))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hR.cru]
      exact inv_mem (hT _ (by simp))
    · rw [hR.crv]
      exact inv_mem (hT _ (by simp))
    · rw [hR.crw]
      exact inv_mem (hT _ (by simp))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hR.csu]
      exact hT _ (by simp)
    · rw [hR.csv]
      exact hT _ (by simp)
    · rw [hR.csw]
      exact mul_mem (mul_mem (hT _ (by simp)) (inv_mem (hT _ (by simp)))) (hT _ (by simp))

theorem y2l_omega1_subgroupOf_normal {n : ℕ} {e : Bool} (hP : IsPres26 n e P u v w r s) :
    ((omega1 (closure ({u, v, w} : Set P))).subgroupOf ⊤).Normal :=
  (y2l_omega1_normal (y2l_T_normal hP)).subgroupOf ⊤

section Quot

variable (N : Subgroup P) [(N.subgroupOf ⊤).Normal]

theorem y2l_quot_rels (hP : IsPres26 2 true P u v w r s)
    (hN : N = omega1 (closure ({u, v, w} : Set P))) :
    Y2LRels 1 true (y2l_qTop N u) (y2l_qTop N v) (y2l_qTop N w) (y2l_qTop N r)
      (y2l_qTop N s) := by
  subst hN
  have hR := y2l_rels_iff.mp hP.1
  set q := y2l_qTop (omega1 (closure ({u, v, w} : Set P)))
  have hsq : ∀ x : P, x ∈ closure ({u, v, w} : Set P) → x ^ 2 ^ 2 = 1 → q x ^ 2 ^ 1 = 1 := by
    intro x hx h4
    rw [← map_pow, y2l_qTop_eq_one_iff]
    refine subset_closure ⟨pow_mem hx _, ?_⟩
    rw [← pow_mul, show 2 ^ 1 * 2 = 2 ^ 2 by norm_num]
    exact h4
  refine ⟨hR.cuv.map q, hR.cuw.map q, hR.cvw.map q, hsq u (subset_closure (by simp)) hR.pu,
    hsq v (subset_closure (by simp)) hR.pv, hsq w (subset_closure (by simp)) hR.pw,
    by simpa only [map_pow, map_one] using congrArg q hR.r2,
    by simpa only [map_mul, map_inv] using congrArg q hR.crs,
    by simpa only [map_mul, map_inv] using congrArg q hR.cru,
    by simpa only [map_mul, map_inv] using congrArg q hR.crv,
    by simpa only [map_mul, map_inv] using congrArg q hR.crw,
    by simpa only [map_mul, map_inv] using congrArg q hR.csu,
    by simpa only [map_mul, map_inv] using congrArg q hR.csv,
    by simpa only [map_mul, map_inv] using congrArg q hR.csw, ?_⟩
  rw [← map_pow, hR.s4, if_pos rfl, if_pos rfl, map_mul]

theorem y2l_quot_seven (hP : IsPres26 2 true P u v w r s)
    (hN : N = omega1 (closure ({u, v, w} : Set P))) :
    ∀ y ∈ y2l_ws7 1, FreeGroup.lift (![y2l_qTop N u, y2l_qTop N v, y2l_qTop N w,
      y2l_qTop N r, y2l_qTop N s] : Fin 5 → ↥(⊤ : Subgroup P) ⧸ N.subgroupOf ⊤)
      (FreeGroup.mk y) ≠ 1 := by
  subst hN
  have hR := y2l_rels_iff.mp hP.1
  intro y hy h1
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  rw [y2l_lift_ws7_word] at h1
  have h2 : u ^ (1 * t.1) * v ^ (1 * t.2.1) * w ^ (1 * t.2.2) ∈
      omega1 (closure ({u, v, w} : Set P)) := by
    rw [← y2l_qTop_eq_one_iff, map_mul, map_mul, map_pow, map_pow, map_pow]
    exact h1
  obtain ⟨-, h3⟩ := y2l_mem_omega1 hR.cuv hR.cuw hR.cvw h2
  rw [one_mul, one_mul, one_mul,
    ((hR.cuw.pow_pow t.1 t.2.2).mul_left (hR.cvw.pow_pow t.2.1 t.2.2)).mul_pow,
    (hR.cuv.pow_pow t.1 t.2.1).mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at h3
  apply y2l_seven_of_pres hP _ (y2l_mem_ws7 ht)
  rw [y2l_lift_ws7_word]
  show u ^ (2 * t.1) * v ^ (2 * t.2.1) * w ^ (2 * t.2.2) = 1
  rw [mul_comm 2 t.1, mul_comm 2 t.2.1, mul_comm 2 t.2.2]
  exact h3

theorem y2l_quot_pres (hP : IsPres26 2 true P u v w r s)
    (hN : N = omega1 (closure ({u, v, w} : Set P))) :
    IsPres26 1 true (↥(⊤ : Subgroup P) ⧸ N.subgroupOf ⊤) (y2l_qTop N u) (y2l_qTop N v)
      (y2l_qTop N w) (y2l_qTop N r) (y2l_qTop N s) := by
  have hrel := y2l_rels_iff.mpr (y2l_quot_rels N hP hN)
  have hgen : closure ({y2l_qTop N u, y2l_qTop N v, y2l_qTop N w, y2l_qTop N r,
      y2l_qTop N s} : Set (↥(⊤ : Subgroup P) ⧸ N.subgroupOf ⊤)) = ⊤ := by
    rw [show ({y2l_qTop N u, y2l_qTop N v, y2l_qTop N w, y2l_qTop N r, y2l_qTop N s} :
        Set (↥(⊤ : Subgroup P) ⧸ N.subgroupOf ⊤)) = y2l_qTop N '' {u, v, w, r, s} by
      simp only [Set.image_insert_eq, Set.image_singleton], ← MonoidHom.map_closure,
      y2l_closure_eq_top hP, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact y2l_qTop_surjective N
  obtain ⟨hfin, hle⟩ := y2l_card_P26_le.2.2
  obtain ⟨-, h64⟩ := y2l_isPres26_one hrel (y2l_quot_seven N hP hN)
  exact y2l_isPres26_of_card hrel hgen (hle.trans (by
    rw [← h64]
    exact Subgroup.card_le_card_group _))

end Quot

end CFSG.OddStandard.HigherRank.G2Three.Sec2
