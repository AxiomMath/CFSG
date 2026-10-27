module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95L3U3
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open scoped MatrixGroups commutatorElement

structure Ivk95Cfg {J : Type} [Group J] [Finite J] (z : J) : Prop where
  ord : orderOf z = 2
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
    Nonempty (SL(2, F) ≃* ↥(Ez z))
  quasi : IsQuasisimple ↥(Ez z)
  mem : z ∈ Ez z
  uniq : ∀ v ∈ Ez z, v * v = 1 → v = 1 ∨ v = z
  central : ∀ k ∈ Ez z, k * z = z * k
  conj_mem : ∀ c : J, c * z = z * c → ∀ k ∈ Ez z, c * k * c⁻¹ ∈ Ez z
  cyc : ∀ T : Subgroup J, (∀ t ∈ T, ∀ k ∈ Ez z, t * k = k * t) → IsPGroup 2 ↥T → IsCyclic ↥T

theorem Ivk95Cfg.of_hyps {J : Type} [Group J] [Finite J] {z : J} (hz : orderOf z = 2) {q : ℕ}
    (hodd : Odd q) (h5 : 5 ≤ q) (hsl : HasSL2Model ↥(Ez z) (fun r => r = q))
    (hcyc : ∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) :
    Ivk95Cfg z := by
  obtain ⟨hzK, hu, hc⟩ := ivk95_z_facts hz hodd hsl hcyc
  obtain ⟨F, hF, hFin, hFq, he⟩ := CFSG.GH74.Generic.S1.exists_sl2_equiv hsl
  have hcyc' : ∀ T : Subgroup J, (∀ t ∈ T, ∀ k ∈ Ez z, t * k = k * t) → IsPGroup 2 ↥T →
      IsCyclic ↥T := by
    intro T hT hT2
    set C := centralizer ((Ez z : Subgroup J) : Set J) with hC
    have hTC : T ≤ C := fun t ht => mem_centralizer_iff.mpr fun k hk => (hT t ht k hk).symm
    have hT'2 : IsPGroup 2 ↥(T.subgroupOf C) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
    obtain ⟨S, hS⟩ := hT'2.exists_le_sylow
    have hSc := hcyc S
    have h1 : IsCyclic ↥(T.subgroupOf C) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hS).surjective
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTC).surjective
  refine ⟨hz, ⟨F, hF, hFin, ?_, ?_, he⟩,
    CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 (by omega) hsl, hzK, hu, hc, Ez_conj_mem z, hcyc'⟩
  · rw [hFq]
    exact hodd
  · rw [hFq]
    exact h5


theorem Ez_map_equiv' {J J' : Type} [Group J] [Group J'] (Φ : J ≃* J') (z : J) :
    (Ez z).map Φ.toMonoidHom = Ez (Φ z) := by
  unfold Ez
  rw [Subgroup.map_map, ← CFSG.GH74.GLS.Stage2.Final.ModelLT.layer_map_equiv
    (CFSG.GH74.GLS.Stage2.Final.ModelLT.centralizerEquiv Φ z), Subgroup.map_map,
    CFSG.GH74.GLS.Stage2.Final.ModelLT.subtype_comp_centralizerEquiv]

theorem Ivk95Cfg.of_equiv {J J' : Type} [Group J] [Finite J] [Group J'] [Finite J'] (Φ : J ≃* J')
    {z : J} (h : Ivk95Cfg z) : Ivk95Cfg (Φ z) := by
  have hEz := Ez_map_equiv' Φ z
  have hmem : ∀ y : J', y ∈ Ez (Φ z) ↔ Φ.symm y ∈ Ez z := by
    intro y
    rw [← hEz]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨Φ.symm y, hy, by simp⟩
  let ψ : ↥(Ez z) ≃* ↥(Ez (Φ z)) :=
    ((Ez z).equivMapOfInjective Φ.toMonoidHom Φ.injective).trans (MulEquiv.subgroupCongr hEz)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.ord
  · obtain ⟨F, hF, hFin, hodd, h5, ⟨e⟩⟩ := h.sl2
    exact ⟨F, hF, hFin, hodd, h5, ⟨e.trans ψ⟩⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv ψ h.quasi
  · rw [hmem]
    simpa using h.mem
  · intro v hv hvv
    rw [hmem] at hv
    have h1 : Φ.symm v * Φ.symm v = 1 := by rw [← map_mul, hvv, map_one]
    rcases h.uniq _ hv h1 with h2 | h2
    · left
      simpa using congrArg Φ h2
    · right
      simpa using congrArg Φ h2
  · intro k hk
    rw [hmem] at hk
    apply Φ.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact h.central _ hk
  · intro c hc k hk
    rw [hmem] at hk
    have hc' : Φ.symm c * z = z * Φ.symm c := by
      apply Φ.injective
      simpa using hc
    have := h.conj_mem _ hc' _ hk
    rw [hmem]
    simpa using this
  · intro T' hT' hT'2
    set T : Subgroup J := T'.map Φ.symm.toMonoidHom with hT
    have hTc : ∀ t ∈ T, ∀ k ∈ Ez z, t * k = k * t := by
      rintro _ ⟨t', ht', rfl⟩ k hk
      have hk' : Φ k ∈ Ez (Φ z) := by
        rw [← hEz]
        exact ⟨k, hk, rfl⟩
      have := hT' t' ht' (Φ k) hk'
      apply Φ.injective
      simpa using this
    have hT2 : IsPGroup 2 ↥T := hT'2.map Φ.symm.toMonoidHom
    have hTcyc := h.cyc T hTc hT2
    exact isCyclic_of_surjective
      ((T'.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective).symm.toMonoidHom)
      ((T'.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective).symm.surjective)

theorem ivk95_empty_of_cfg {P : (X : Type) → [Group X] → Prop}
    (h : ∀ (J : Type) [Group J] [Finite J], P J → ∀ z : J, Ivk95Cfg z → False) : Ivk95Empty P :=
  fun J _ _ hJ z hz _ hodd h5 hsl hcyc => h J hJ z (Ivk95Cfg.of_hyps hz hodd h5 hsl hcyc)

theorem sl2_exists_order_four {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ g : SL(2, F), g ^ 2 ≠ 1 ∧ g ^ 4 = 1 := by
  let g : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have hg2 : g ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨g, ?_, ?_⟩
  · rw [hg2]
    exact CFSG.GH74.KGroups.L3Eps.neg_one_ne_one h2
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hg2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem le_Ez_of_isComponent {J : Type} [Group J] {z : J}
    {B : Subgroup ↥(centralizer ({z} : Set J))} (hB : IsComponent B) :
    B.map (centralizer ({z} : Set J)).subtype ≤ Ez z :=
  Subgroup.map_mono (le_sSup hB)

open Polynomial in
theorem sl2_exists_quaternion {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ H : Subgroup SL(2, F), IsPGroup 2 H ∧ ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := (X ^ 2 : F[X])) (g := (X ^ 2 + 1 : F[X])) (by compute_degree!) (by compute_degree!) hcard
  have hab' : a ^ 2 + b ^ 2 = -1 := by
    simp at hab
    linear_combination hab
  let i : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let j : SL(2, F) := ⟨!![a, b; b, -a], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * hab'⟩
  have hi2 : i ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [i, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hj2 : j ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [j, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hab'
  have hij : i * j = -(j * i) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_mul]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [i, j, Matrix.mul_apply, Fin.sum_univ_two]
  have hne : (-1 : SL(2, F)) ≠ 1 := CFSG.GH74.KGroups.L3Eps.neg_one_ne_one h2
  have hneg1 : ∀ x : SL(2, F), -x = (-1 : SL(2, F)) * x := by
    intro x
    apply Subtype.ext
    simp
  have hz : (-1 : SL(2, F)) * (-1) = 1 := by
    apply Subtype.ext
    simp
  have hzc : ∀ x : SL(2, F), (-1 : SL(2, F)) * x = x * (-1) := by
    intro x
    apply Subtype.ext
    simp
  have hi4 : i ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi2, pow_two, hz]
  have hinv : i⁻¹ = i ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact hi4
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi2]
    exact (hneg1 i).symm
  have hji : j * i = i ^ 3 * j := by
    rw [hi3, neg_mul, hij, neg_neg]
  have hjk : ∀ k : ℕ, j * i ^ k = i ^ (3 * k) * j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hji, ← mul_assoc, ← pow_add]
      congr 2
  have hjinv : j⁻¹ = i ^ 2 * j := by
    apply inv_eq_of_mul_eq_one_right
    rw [hi2, ← mul_assoc, ← hzc j, mul_assoc, ← pow_two, hj2]
    exact hz
  set H := Subgroup.closure ({i, j} : Set SL(2, F)) with hH
  have hmem : ∀ h ∈ H, ∃ n : ℕ, h = i ^ n ∨ h = i ^ n * j := by
    intro h hh
    refine Subgroup.closure_induction_right
      (p := fun x _ => ∃ n : ℕ, x = i ^ n ∨ x = i ^ n * j) ?_ ?_ ?_ hh
    · exact ⟨0, Or.inl (pow_zero i).symm⟩
    · intro x hx y hy hp
      obtain ⟨n, hn⟩ := hp
      rcases hy with rfl | hy
      · rcases hn with rfl | rfl
        · exact ⟨n + 1, Or.inl (pow_succ i n).symm⟩
        · refine ⟨n + 3, Or.inr ?_⟩
          rw [mul_assoc, hji, ← mul_assoc, ← pow_add]
      · have hyj : y = j := by simpa using hy
        subst hyj
        rcases hn with rfl | rfl
        · exact ⟨n, Or.inr rfl⟩
        · refine ⟨n + 2, Or.inl ?_⟩
          rw [mul_assoc, ← pow_two, hj2, ← hi2, ← pow_add]
    · intro x hx y hy hp
      obtain ⟨n, hn⟩ := hp
      rcases hy with rfl | hy
      · rcases hn with rfl | rfl
        · exact ⟨n + 3, Or.inl (by rw [hinv, pow_add])⟩
        · refine ⟨n + 9, Or.inr ?_⟩
          rw [hinv, mul_assoc, hjk 3, ← mul_assoc, ← pow_add]
      · have hyj : y = j := by simpa using hy
        subst hyj
        rcases hn with rfl | rfl
        · exact ⟨n + 2, Or.inr (by rw [hjinv, ← mul_assoc, ← pow_add])⟩
        · exact ⟨n, Or.inl (mul_inv_cancel_right _ _)⟩
  have hsq : ∀ n : ℕ, (i ^ n * j) ^ 2 = -1 := by
    intro n
    have h1 : (i ^ n * j) * (i ^ n * j) = i ^ (n + 3 * n) * (j * j) := by
      calc (i ^ n * j) * (i ^ n * j) = i ^ n * (j * i ^ n) * j := by simp only [mul_assoc]
        _ = i ^ n * (i ^ (3 * n) * j) * j := by rw [hjk n]
        _ = i ^ (n + 3 * n) * (j * j) := by rw [pow_add]; simp only [mul_assoc]
    rw [pow_two, h1, ← pow_two, hj2, show n + 3 * n = 4 * n by ring, pow_mul, hi4, one_pow, one_mul]
  refine ⟨H, ?_, i, Subgroup.subset_closure (by simp), j, Subgroup.subset_closure (by simp), ?_⟩
  · intro g
    refine ⟨2, ?_⟩
    obtain ⟨n, hn | hn⟩ := hmem g g.2
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hn]
      show (i ^ n) ^ (2 ^ 2) = 1
      rw [← pow_mul, mul_comm, pow_mul, show 2 ^ 2 = 4 from rfl, hi4, one_pow]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hn]
      show (i ^ n * j) ^ (2 ^ 2) = 1
      rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, hsq, pow_two, hz]
  · intro h
    apply hne
    have h1 : i * j = (-1 : SL(2, F)) * (i * j) := by
      rw [← hneg1]
      calc i * j = -(j * i) := hij
        _ = -(i * j) := by rw [h]
    have h3 : (-1 : SL(2, F)) * (i * j) = 1 * (i * j) := by
      rw [one_mul]
      exact h1.symm
    exact mul_right_cancel h3

namespace Ivk95Cfg

variable {J : Type} [Group J] [Finite J] {z : J}

theorem le_cent (_h : Ivk95Cfg z) : Ez z ≤ centralizer ({z} : Set J) := Ez_le_centralizer z

theorem card_eq (h : Ivk95Cfg z) :
    ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ Nat.card ↥(Ez z) = q * (q ^ 2 - 1) := by
  obtain ⟨F, hF, hFin, hodd, h5, ⟨e⟩⟩ := h.sl2
  refine ⟨Nat.card F, hodd, h5, ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F

theorem exists_order_four (h : Ivk95Cfg z) : ∃ g ∈ Ez z, g ^ 2 ≠ 1 ∧ g ^ 4 = 1 := by
  obtain ⟨F, hF, hFin, hodd, h5, ⟨e⟩⟩ := h.sl2
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  obtain ⟨g, hg2, hg4⟩ := sl2_exists_order_four h2
  refine ⟨((e g : ↥(Ez z)) : J), (e g).2, ?_, ?_⟩
  · intro h1
    apply hg2
    apply e.injective
    apply Subtype.ext
    simpa [map_pow] using h1
  · have : e (g ^ 4) = 1 := by rw [hg4, map_one]
    have h4 : ((e g : ↥(Ez z)) : J) ^ 4 = 1 := by
      have := congrArg Subtype.val this
      simpa [map_pow] using this
    exact h4

theorem not_solvable (h : Ivk95Cfg z) : ¬ Group.IsSolvable ↥(Ez z) :=
  CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple h.quasi

theorem perfect (h : Ivk95Cfg z) : ⁅Ez z, Ez z⁆ = Ez z :=
  Subgroup.isPerfect_iff.mp h.quasi.1

omit [Finite J] in
theorem subgroupOf_eq : (Ez z).subgroupOf (centralizer ({z} : Set J)) =
    layer ↥(centralizer ({z} : Set J)) := by
  show (Subgroup.map _ (layer ↥(centralizer ({z} : Set J)))).comap _ = _
  exact Subgroup.comap_map_eq_self_of_injective (centralizer ({z} : Set J)).subtype_injective _

theorem normal_in (_h : Ivk95Cfg z) : ((Ez z).subgroupOf (centralizer ({z} : Set J))).Normal := by
  rw [subgroupOf_eq]
  have : (layer ↥(centralizer ({z} : Set J))).Characteristic := LocalCores.layer_characteristic
  infer_instance

theorem card_subgroupOf (h : Ivk95Cfg z) :
    Nat.card ↥((Ez z).subgroupOf (centralizer ({z} : Set J))) = Nat.card ↥(Ez z) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_cent).toEquiv

theorem isComponent (h : Ivk95Cfg z) :
    IsComponent ((Ez z).subgroupOf (centralizer ({z} : Set J))) :=
  ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.le_cent).symm h.quasi,
    haveI := h.normal_in
    Subgroup.Normal.isSubnormal inferInstance⟩

theorem false_of_solvable (h : Ivk95Cfg z) (hs : Group.IsSolvable ↥(centralizer ({z} : Set J))) :
    False :=
  h.not_solvable (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion h.le_cent) (Subgroup.inclusion_injective h.le_cent))

theorem false_of_no_order_four (h : Ivk95Cfg z) (hJ : ∀ g : J, g ^ 4 = 1 → g ^ 2 = 1) : False := by
  obtain ⟨g, -, hg2, hg4⟩ := h.exists_order_four
  exact hg2 (hJ g hg4)

theorem false_of_derived_le (h : Ivk95Cfg z) {F : Subgroup J} (hF : Nat.card ↥F < 120)
    (hD : ∀ x ∈ centralizer ({z} : Set J), ∀ y ∈ centralizer ({z} : Set J), ⁅x, y⁆ ∈ F) :
    False := by
  have hKF : Ez z ≤ F := by
    rw [← h.perfect]
    exact Subgroup.commutator_le.mpr fun x hx y hy => hD x (h.le_cent hx) y (h.le_cent hy)
  obtain ⟨q, hq, hq5, hKq⟩ := h.card_eq
  have h1 : Nat.card ↥(Ez z) ≤ Nat.card ↥F := Subgroup.card_le_of_le hKF
  have h2 : 120 ≤ Nat.card ↥(Ez z) := by
    rw [hKq]
    have : 5 ≤ q := hq5
    nlinarith [Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)]
  omega

theorem arith_perfect {q N : ℕ} (hodd : Odd q) (h5 : 5 ≤ q) (hN : N = 1920 ∨ N = 2688)
    (hdvd : q * (q ^ 2 - 1) ∣ N) : (q = 5 ∧ N = 1920) ∨ (q = 7 ∧ N = 2688) := by
  have hle : q * (q ^ 2 - 1) ≤ N := Nat.le_of_dvd (by omega) hdvd
  have hq14 : q ≤ 14 := by
    by_contra hcon
    have h15 : 15 ≤ q := by omega
    have : 15 * (15 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
      apply Nat.mul_le_mul h15
      apply Nat.sub_le_sub_right
      exact Nat.pow_le_pow_left h15 2
    omega
  obtain ⟨k, hk⟩ := hodd
  interval_cases q <;> omega

theorem false_of_perfect (h : Ivk95Cfg z) (hperf : Group.IsPerfect ↥(centralizer ({z} : Set J)))
    (hN : Nat.card ↥(centralizer ({z} : Set J)) = 1920 ∨
      Nat.card ↥(centralizer ({z} : Set J)) = 2688) : False := by
  set C := centralizer ({z} : Set J) with hC
  set K : Subgroup ↥C := (Ez z).subgroupOf C with hK
  have hKn : K.Normal := h.normal_in
  obtain ⟨q, hq, hq5, hKq⟩ := h.card_eq
  have hKcard : Nat.card ↥K = q * (q ^ 2 - 1) := by rw [hK, h.card_subgroupOf, hKq]
  have hdvd : q * (q ^ 2 - 1) ∣ Nat.card ↥C := by
    rw [← hKcard]
    exact Subgroup.card_subgroup_dvd_card K
  have hmul : Nat.card (↥C ⧸ K) * Nat.card ↥K = Nat.card ↥C := by
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup K).symm
  have hQ : IsPGroup 2 (↥C ⧸ K) ∧ Nat.card (↥C ⧸ K) ≠ 1 := by
    rcases arith_perfect hq hq5 hN hdvd with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
    · have h16 : Nat.card (↥C ⧸ K) = 16 := by
        rw [hKcard, h1] at hmul
        omega
      exact ⟨IsPGroup.of_card (n := 4) (by rw [h16]; norm_num), by omega⟩
    · have h8 : Nat.card (↥C ⧸ K) = 8 := by
        rw [hKcard, h1] at hmul
        omega
      exact ⟨IsPGroup.of_card (n := 3) (by rw [h8]; norm_num), by omega⟩
  obtain ⟨hp, hne⟩ := hQ
  have : Nontrivial (↥C ⧸ K) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hne (Nat.card_of_subsingleton (1 : (↥C ⧸ K)))
  have : Group.IsPerfect ↥C := hperf
  exact Group.IsPerfect.not_isNilpotent (↥C ⧸ K) hp.isNilpotent

theorem false_of_quasisimple_centralizer (h : Ivk95Cfg z)
    (hq : IsQuasisimple ↥(centralizer ({z} : Set J)))
    (hcard : ∀ q : ℕ, 5 ≤ q → Nat.card ↥(centralizer ({z} : Set J)) ≠ q * (q ^ 2 - 1)) :
    False := by
  have hKn := h.normal_in
  rcases LocalCores.quasisimple_normal_subgroups hq hKn with htop | hle
  · have hCK : centralizer ({z} : Set J) ≤ Ez z := Subgroup.subgroupOf_eq_top.mp htop
    have hEq : Ez z = centralizer ({z} : Set J) := le_antisymm h.le_cent hCK
    obtain ⟨q, -, hq5, hKq⟩ := h.card_eq
    exact hcard q hq5 (by rw [← hEq]; exact hKq)
  · apply h.not_solvable
    have hcomm : ∀ a b : ↥((Ez z).subgroupOf (centralizer ({z} : Set J))), a * b = b * a := by
      intro a b
      have ha := hle a.2
      have hb := hle b.2
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hb) a)
    have hsolv : Group.IsSolvable ↥((Ez z).subgroupOf (centralizer ({z} : Set J))) :=
      Group.isSolvable_of_comm hcomm
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h.le_cent).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h.le_cent).symm.injective


theorem exists_nonabelian_two_subgroup (h : Ivk95Cfg z) :
    ∃ H : Subgroup J, H ≤ Ez z ∧ IsPGroup 2 H ∧ ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x := by
  obtain ⟨F, hF, hFin, hodd, h5, ⟨e⟩⟩ := h.sl2
  obtain ⟨Q, hQ, x, hx, y, hy, hxy⟩ := sl2_exists_quaternion hodd
  refine ⟨(Q.map e.toMonoidHom).map (Ez z).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · have h1 : IsPGroup 2 ↥(Q.map e.toMonoidHom) := hQ.map e.toMonoidHom
    exact h1.map _
  · refine ⟨((e x : ↥(Ez z)) : J), ⟨e x, ⟨x, hx, rfl⟩, rfl⟩, ((e y : ↥(Ez z)) : J),
      ⟨e y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
    intro hc
    apply hxy
    apply e.injective
    apply Subtype.ext
    simpa using hc

theorem false_of_abelian_sylow (h : Ivk95Cfg z) (hab : CFSG.Walter.HasAbelianSylowTwo J) : False := by
  obtain ⟨H, -, hH2, x, hx, y, hy, hxy⟩ := h.exists_nonabelian_two_subgroup
  obtain ⟨P, hP⟩ := hH2.exists_le_sylow
  apply hxy
  have hc := (hab P).is_comm.comm
  exact hc ⟨x, hP hx⟩ ⟨y, hP hy⟩ |> congrArg Subtype.val

theorem false_of_sl2_centralizing (h : Ivk95Cfg z) {I : Subgroup J} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : SL(2, F) ≃* ↥I)
    (hI : ∀ x ∈ I, ∀ k ∈ Ez z, x * k = k * x) : False := by
  obtain ⟨Q, hQ, x, hx, y, hy, hxy⟩ := sl2_exists_quaternion hodd
  set H : Subgroup J := (Q.map e.toMonoidHom).map I.subtype with hH
  have hHc : ∀ t ∈ H, ∀ k ∈ Ez z, t * k = k * t := by
    rintro _ ⟨u, -, rfl⟩ k hk
    exact hI u.1 u.2 k hk
  have hH2 : IsPGroup 2 ↥H := by
    have h1 : IsPGroup 2 ↥(Q.map e.toMonoidHom) := hQ.map e.toMonoidHom
    exact h1.map _
  have hcyc := h.cyc H hHc hH2
  have hcomm : IsMulCommutative ↥H :=
    (MonoidHom.id ↥H).isMulCommutative_of_isCyclic_of_ker_le_center (by simp)
  have hxH : ((e x : ↥I) : J) ∈ H := ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  have hyH : ((e y : ↥I) : J) ∈ H := ⟨e y, ⟨y, hy, rfl⟩, rfl⟩
  have hc : (⟨_, hxH⟩ : ↥H) * ⟨_, hyH⟩ = ⟨_, hyH⟩ * ⟨_, hxH⟩ := hcomm.is_comm.comm _ _
  apply hxy
  apply e.injective
  apply Subtype.ext
  have := congrArg (fun u : ↥H => (u : J)) hc
  simpa using this

end Ivk95Cfg

end CFSG.GH74.GLS.IVK.Proofs2
