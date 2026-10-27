module

public import CFSG.LocalAnalysis.OddStandard.ONanFusLoc
public import CFSG.LocalAnalysis.OddStandard.ONanFusRows

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

@[expose] def bE : AlpE := gen 0 ^ 2 * gen 1 ^ 2

theorem invE_one : invE 1 = bE := by decide

theorem invE_zero : invE 0 = zc := by decide

set_option maxRecDepth 100000 in
theorem conj_bE : ∀ c : AlpE, c⁻¹ * bE * c = bE ∨ c⁻¹ * bE * c = zc * bE := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conj_bE_zc : ∃ c : AlpE, c⁻¹ * bE * c = zc * bE := by decide +kernel

set_option maxRecDepth 100000 in
theorem conj_v1sq : ∃ c : AlpE, c⁻¹ * invE 2 * c = invE 2 * bE := by decide +kernel

set_option maxRecDepth 100000 in
theorem conj_v3sq : ∃ c : AlpE, c⁻¹ * invE 2 * c = invE 2 * (zc * bE) := by decide +kernel

theorem fE_one_eq : fE 1 = fE 0 * zc := by decide

@[expose] def YE : List AlpE :=
  [1, bE, zc, stE, bE * zc, bE * stE, zc * stE, bE * zc * stE]

set_option maxRecDepth 100000 in
theorem YE_nodup : YE.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem YE_comm : ∀ y ∈ YE, y * fE 0 = fE 0 * y := by decide +kernel

set_option maxRecDepth 100000 in
theorem YE_sq : ∀ y ∈ YE, y * y = 1 := by decide +kernel

theorem YE_length : YE.length = 8 := rfl

theorem sq_d_zero_of_pow_four (hF : f2Check = true) {y : AlpE} (h4 : y ^ 4 = 1) :
    (y * y).d = 0 := by
  rw [mul_d]
  by_cases hodd : y.d = 1 ∨ y.d = 3
  · have h16 := orderOf_of_d_odd hF hodd
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h16] at this
    norm_num at this
  · push Not at hodd
    revert hodd
    generalize y.d = d
    decide +revert

theorem sq_eq_zc_of_ne_coset (hF : f2Check = true) {y0 y1 : AlpE} (hd0 : y0.d ≠ 0)
    (hd1 : y1.d ≠ 0) (hne : y0.d ≠ y1.d) (h04 : y0 ^ 4 = 1) (h02 : y0 ^ 2 ≠ 1)
    (h14 : y1 ^ 4 = 1) (h12 : y1 ^ 2 ≠ 1) (hsq : y0 ^ 2 = y1 ^ 2) : y0 ^ 2 = zc := by
  have hnodd : ∀ y : AlpE, y ^ 4 = 1 → ¬ (y.d = 1 ∨ y.d = 3) := fun y hy hodd => by
    have h16 := orderOf_of_d_odd hF hodd
    have := orderOf_dvd_of_pow_eq_one hy
    rw [h16] at this
    norm_num at this
  have hc0 := hnodd y0 h04
  have hc1 := hnodd y1 h14
  by_cases h246 : y0.d = 2 ∨ y0.d = 4 ∨ y0.d = 6
  · exact sq_of_order_four_d246 hF h246 h04 h02
  by_cases h246' : y1.d = 2 ∨ y1.d = 4 ∨ y1.d = 6
  · rw [hsq]
    exact sq_of_order_four_d246 hF h246' h14 h12
  exfalso
  have h57 : ∀ y : AlpE, y.d ≠ 0 → ¬ (y.d = 1 ∨ y.d = 3) → ¬ (y.d = 2 ∨ y.d = 4 ∨ y.d = 6) →
      y.d = 5 ∨ y.d = 7 := fun y => by
    generalize y.d = d
    decide +revert
  have hne57 : gen 0 ^ 2 * gen 1 ^ 2 ≠ gen 1 ^ 2 * gen 2 ^ 2 := by decide
  rcases h57 y0 hd0 hc0 h246 with h0 | h0 <;> rcases h57 y1 hd1 hc1 h246' with h1 | h1
  · exact hne (h0.trans h1.symm)
  · rw [sq_of_order_four_d5 hF h0 h04 h02, sq_of_order_four_d7 hF h1 h14 h12] at hsq
    exact hne57 hsq
  · rw [sq_of_order_four_d7 hF h0 h04 h02, sq_of_order_four_d5 hF h1 h14 h12] at hsq
    exact hne57 hsq.symm
  · exact hne (h0.trans h1.symm)

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem inClass_of_model {i : Fin 7} {y : AlpE} (h : ∃ c : AlpE, c⁻¹ * invE i * c = y) :
    D.InClass i (D.E.φ y) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨D.E.φ c, AlpEmb.φ_mem D.E c, by rw [← AlpEmb.φ_invE D.E, ← map_inv, ← map_mul,
    ← map_mul]⟩

theorem invRep_eq (i : Fin 7) : invRep v1 v2 v3 s t i = D.E.φ (invE i) :=
  (AlpEmb.φ_invE D.E i).symm

theorem z_mem_P : invRep v1 v2 v3 s t 0 ∈ alpP v1 v2 v3 s t := AlpEmb.invRep_mem D.E 0

theorem z_central {c : G} (hc : c ∈ alpP v1 v2 v3 s t) :
    c⁻¹ * invRep v1 v2 v3 s t 0 * c = invRep v1 v2 v3 s t 0 := by
  have h := ((AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl)) c hc
  rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem rep_mem_V {i : Fin 7} (hi : i.val ≤ 2) : invRep v1 v2 v3 s t i ∈ alpV v1 v2 v3 := by
  have hW : ∀ j : Fin 7, j.val ≤ 2 → invRep v1 v2 v3 s t j ∈ alpW v1 v2 v3 := by
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact sq_mul_sq_mem_alpW v1 v2 v3
    · show v1 ^ 2 * v2 ^ 2 ∈ alpW v1 v2 v3
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · show v2 ^ 2 ∈ alpW v1 v2 v3
      exact subset_closure (by simp)
  exact D.W_le_V (hW i hi)

theorem not_fus_AC (hAB : ¬ D.Fus 0 1) : ¬ D.Fus 0 2 := by
  intro hAC
  obtain ⟨g0, hg0⟩ := id hAC
  obtain ⟨n, hn, hnz⟩ := D.fuse_V (D.V_le_centralizer_V (D.rep_mem_V (i := 0) (by decide)))
    (D.V_le_centralizer_V (D.rep_mem_V (i := 2) (by decide))) ⟨g0⁻¹, by rw [inv_inv]; exact hg0⟩
  have hninv : n⁻¹ ∈ normalizer (alpV v1 v2 v3 : Set G) := inv_mem hn
  have hconjV : ∀ v ∈ alpV v1 v2 v3, n⁻¹ * v * n ∈ alpV v1 v2 v3 := fun v hv => by
    have := (mem_normalizer_iff.1 hninv v).1 hv
    rwa [inv_inv] at this
  set x := n⁻¹ * invRep v1 v2 v3 s t 1 * n with hx
  have hxV : x ∈ alpV v1 v2 v3 := hconjV _ (D.rep_mem_V (i := 1) (by decide))
  have hx2 : x * x = 1 := by
    calc x * x = n⁻¹ * (invRep v1 v2 v3 s t 1 * invRep v1 v2 v3 s t 1) * n := by rw [hx]; group
      _ = 1 := by rw [D.rep_sq 1]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply D.rep_ne_one 1
    calc invRep v1 v2 v3 s t 1 = n * x * n⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h]; group
  obtain ⟨i, hi⟩ := D.exists_inClass (D.V_le_P hxV) hx2 hx1
  have hi2 := D.le_two_of_inClass_mem_V hi hxV
  have hfus1 : D.Fus 1 i := D.inClass_fus (D.inClass_rep 1) hi n rfl
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact hAB (Fus.symm D hfus1)
  · obtain ⟨c, hcP, hcx⟩ := hi
    obtain ⟨c', rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hcP
    have hx' : x = D.E.φ bE ∨ x = D.E.φ (zc * bE) := by
      rw [← hcx, D.invRep_eq 1, invE_one, ← map_inv, ← map_mul, ← map_mul]
      rcases conj_bE c' with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    have hzb : D.InClass 1 (D.E.φ (zc * bE)) :=
      D.inClass_of_model (by rw [invE_one]; exact conj_bE_zc)
    have hy : n⁻¹ * D.E.φ (zc * bE) * n = invRep v1 v2 v3 s t 2 * x := by
      rw [map_mul, ← invE_zero, ← invE_one, ← D.invRep_eq 0, ← D.invRep_eq 1, hx, ← hnz]
      group
    have hyC : D.InClass 2 (invRep v1 v2 v3 s t 2 * x) := by
      rcases hx' with h | h
      · rw [h, D.invRep_eq 2, ← map_mul]
        exact D.inClass_of_model conj_v1sq
      · rw [h, D.invRep_eq 2, ← map_mul]
        exact D.inClass_of_model conj_v3sq
    exact hAB (hAC.trans D (Fus.symm D (D.inClass_fus hzb hyC n hy)))
  · exact hAB (hAC.trans D (Fus.symm D hfus1))

theorem fus_AB : D.Fus 0 1 := by
  classical
  by_contra hAB
  have hAC := D.not_fus_AC hAB
  have hAE : D.Fus 0 4 := by
    rcases D.fus_A_BCE with h | h | h
    · exact absurd h hAB
    · exact absurd h hAC
    · exact h
  obtain ⟨h0, hh0⟩ := hAE
  have hst : invRep v1 v2 v3 s t 4 = s * t := rfl
  have hzc : ∀ c ∈ alpP v1 v2 v3 s t, c * invRep v1 v2 v3 s t 0 = invRep v1 v2 v3 s t 0 * c :=
    (AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl)
  have hzSyl : IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 0} : Set G))
      (centralizer ({invRep v1 v2 v3 s t 0} : Set G)) :=
    isSylowOf_inf_centralizer_of_le D.isSylowOf_P fun c hc =>
      mem_centralizer_singleton_iff.2 (hzc c hc)
  obtain ⟨g, hg1, hg2⟩ := exists_conj_extremal D.isPGroup_P hzSyl hh0
  have hfst : ∀ i : Fin 2, D.fG i ∈ alpP v1 v2 v3 s t ⊓
      centralizer ({invRep v1 v2 v3 s t 4} : Set G) := fun i =>
    ⟨D.V_le_P (D.fG_mem_V i), mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (D.st_mem_K i)).symm⟩
  have hxP : ∀ i : Fin 2, g⁻¹ * D.fG i * g ∈ alpP v1 v2 v3 s t := fun i => (hg2 _ (hfst i)).1
  have hxnV : ∀ i : Fin 2, g⁻¹ * D.fG i * g ∉ alpV v1 v2 v3 := by
    intro i hxV
    obtain ⟨n, hn, hnx⟩ := D.fuse_V (D.V_le_centralizer_V hxV)
      (D.V_le_centralizer_V (D.fG_mem_V i)) ⟨g, by group⟩
    have hk : g * n ∈ centralizer ({D.fG i} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : (g * n)⁻¹ * D.fG i * (g * n) = D.fG i :=
        calc (g * n)⁻¹ * D.fG i * (g * n) = n⁻¹ * (g⁻¹ * D.fG i * g) * n := by group
          _ = D.fG i := hnx
      calc g * n * D.fG i = g * n * ((g * n)⁻¹ * D.fG i * (g * n)) := by rw [h1]
        _ = D.fG i * (g * n) := by group
    apply D.conj_st_not_mem_V hAB i hk
    have hninv : n⁻¹ ∈ normalizer (alpV v1 v2 v3 : Set G) := inv_mem hn
    have h2 := (mem_normalizer_iff.1 hninv (invRep v1 v2 v3 s t 0)).1
      (D.rep_mem_V (i := 0) (by decide))
    rw [inv_inv] at h2
    rw [show (g * n)⁻¹ * (s * t) * (g * n) = n⁻¹ * (g⁻¹ * invRep v1 v2 v3 s t 4 * g) * n by
      rw [hst]; group, hg1]
    exact h2
  have hfsq : ∀ i : Fin 2, D.fG i * D.fG i = invRep v1 v2 v3 s t 1 := fun i => D.fG_sq i
  have hx4 : ∀ i : Fin 2, (g⁻¹ * D.fG i * g) ^ 4 = 1 := fun i => by
    rw [conj_pow_inv, ← D.orderOf_fG i, pow_orderOf_eq_one]
    group
  have hx2 : ∀ i : Fin 2, (g⁻¹ * D.fG i * g) ^ 2 = g⁻¹ * invRep v1 v2 v3 s t 1 * g := fun i => by
    rw [conj_pow_inv, pow_two, hfsq i]
  have hb1 : g⁻¹ * invRep v1 v2 v3 s t 1 * g ≠ 1 := by
    intro h
    apply D.rep_ne_one 1
    calc invRep v1 v2 v3 s t 1 = g * (g⁻¹ * invRep v1 v2 v3 s t 1 * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨y0, hy0⟩ := (AlpEmb.mem_alpP_iff D.E).1 (hxP 0)
  obtain ⟨y1, hy1⟩ := (AlpEmb.mem_alpP_iff D.E).1 (hxP 1)
  have hy4 : ∀ {y : AlpE} (i : Fin 2), D.E.φ y = g⁻¹ * D.fG i * g → y ^ 4 = 1 := fun {y} i h =>
    D.E.inj (by rw [map_pow, h, hx4 i, map_one])
  have hy2 : ∀ {y : AlpE} (i : Fin 2), D.E.φ y = g⁻¹ * D.fG i * g →
      D.E.φ (y ^ 2) = g⁻¹ * invRep v1 v2 v3 s t 1 * g := fun {y} i h => by
    rw [map_pow, h, hx2 i]
  have hbV : g⁻¹ * invRep v1 v2 v3 s t 1 * g ∈ alpV v1 v2 v3 := by
    rw [← hy2 0 hy0, AlpEmb.alpV_eq_map D.E]
    refine Subgroup.mem_map_of_mem _ (mem_Vsub.2 ?_)
    rw [pow_two]
    exact sq_d_zero_of_pow_four D.hF (hy4 0 hy0)
  have hznV : g⁻¹ * invRep v1 v2 v3 s t 0 * g ∉ alpV v1 v2 v3 := by
    intro hzV
    have hψmul : ∀ a b : AlpE, g⁻¹ * D.E.φ (a * b) * g =
        (g⁻¹ * D.E.φ a * g) * (g⁻¹ * D.E.φ b * g) := fun a b => by rw [map_mul]; group
    have hψb : g⁻¹ * D.E.φ bE * g ∈ alpV v1 v2 v3 := by
      rw [← invE_one, ← D.invRep_eq 1]
      exact hbV
    have hψz : g⁻¹ * D.E.φ zc * g ∈ alpV v1 v2 v3 := by
      rw [← invE_zero, ← D.invRep_eq 0]
      exact hzV
    have hψst : g⁻¹ * D.E.φ stE * g ∈ alpV v1 v2 v3 := by
      rw [← D.st_eq, ← hst, hg1]
      exact D.rep_mem_V (i := 0) (by decide)
    have hψ1 : g⁻¹ * D.E.φ 1 * g ∈ alpV v1 v2 v3 := by
      rw [map_one, mul_one, inv_mul_cancel]
      exact one_mem _
    have hψV : ∀ y ∈ YE, g⁻¹ * D.E.φ y * g ∈ alpV v1 v2 v3 := by
      intro y hy
      simp only [YE, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hψ1
      · exact hψb
      · exact hψz
      · exact hψst
      · rw [hψmul]; exact mul_mem hψb hψz
      · rw [hψmul]; exact mul_mem hψb hψst
      · rw [hψmul]; exact mul_mem hψz hψst
      · rw [hψmul, hψmul]; exact mul_mem (mul_mem hψb hψz) hψst
    have hψW : ∀ y ∈ YE, g⁻¹ * D.E.φ y * g ∈ alpW v1 v2 v3 := fun y hy =>
      D.mem_W_iff.2 ⟨hψV y hy, by rw [← hψmul, YE_sq y hy, map_one, mul_one, inv_mul_cancel]⟩
    let F : {y : AlpE // y ∈ YE.toFinset} → alpW v1 v2 v3 :=
      fun y => ⟨g⁻¹ * D.E.φ y * g, hψW y (List.mem_toFinset.1 y.2)⟩
    have hF : Function.Injective F := by
      intro a b h
      have h1 := congrArg Subtype.val h
      simp only [F, mul_left_inj, mul_right_inj] at h1
      exact Subtype.ext (D.E.inj h1)
    have hcard : Nat.card (alpW v1 v2 v3) ≤ Nat.card {y : AlpE // y ∈ YE.toFinset} := by
      rw [AlpEmb.card_alpW D.E D.hF, Nat.card_eq_fintype_card, Fintype.card_coe,
        List.toFinset_card_of_nodup YE_nodup, YE_length]
    have hbij := hF.bijective_of_nat_card_le hcard
    have hx0W : g⁻¹ * D.fG 0 * g ∈ centralizer (alpW v1 v2 v3 : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨⟨y, hy⟩, hyw⟩ := hbij.2 ⟨w, hw⟩
      have hyw' : g⁻¹ * D.E.φ y * g = w := congrArg Subtype.val hyw
      rw [← hyw']
      have hc := YE_comm y (List.mem_toFinset.1 hy)
      calc g⁻¹ * D.E.φ y * g * (g⁻¹ * D.fG 0 * g) = g⁻¹ * D.E.φ (y * fE 0) * g := by
            rw [fG, map_mul]; group
        _ = g⁻¹ * D.E.φ (fE 0 * y) * g := by rw [hc]
        _ = g⁻¹ * D.fG 0 * g * (g⁻¹ * D.E.φ y * g) := by rw [map_mul, fG]; group
    have hmem : g⁻¹ * D.fG 0 * g ∈ alpP v1 v2 v3 s t ⊓ centralizer (alpW v1 v2 v3 : Set G) :=
      ⟨hxP 0, hx0W⟩
    rw [D.P_inf_centralizer_W] at hmem
    exact hxnV 0 hmem
  have hd : ∀ {y : AlpE} (i : Fin 2), D.E.φ y = g⁻¹ * D.fG i * g → y.d ≠ 0 := fun {y} i h hd =>
    hxnV i (by
      rw [← h, AlpEmb.alpV_eq_map D.E]
      exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 hd))
  have hne : y0.d ≠ y1.d := by
    intro h
    apply hznV
    have hv : D.E.φ (y0⁻¹ * y1) ∈ alpV v1 v2 v3 := by
      rw [AlpEmb.alpV_eq_map D.E]
      refine Subgroup.mem_map_of_mem _ (mem_Vsub.2 ?_)
      rw [mul_d, inv_d, h, dmul_dinv]
    have hf1 : D.fG 1 = D.fG 0 * invRep v1 v2 v3 s t 0 := by
      rw [fG, fG, fE_one_eq, map_mul, D.invRep_eq 0, invE_zero]
    have e : D.E.φ (y0⁻¹ * y1) = g⁻¹ * invRep v1 v2 v3 s t 0 * g := by
      rw [map_mul, map_inv, hy0, hy1, hf1]
      group
    rwa [e] at hv
  have hy2ne : ∀ {y : AlpE} (i : Fin 2), D.E.φ y = g⁻¹ * D.fG i * g → y ^ 2 ≠ 1 :=
    fun {y} i h h1 => hb1 (by rw [← hy2 i h, h1, map_one])
  have hsq : y0 ^ 2 = y1 ^ 2 := D.E.inj (by rw [hy2 0 hy0, hy2 1 hy1])
  have hz := sq_eq_zc_of_ne_coset D.hF (hd 0 hy0) (hd 1 hy1) hne (hy4 0 hy0) (hy2ne 0 hy0)
    (hy4 1 hy1) (hy2ne 1 hy1) hsq
  apply hAB
  refine Fus.symm D ⟨g, ?_⟩
  rw [← hy2 0 hy0, hz, D.invRep_eq 0, invE_zero]

end FusCtx

end CFSG.OddStandard.ONanRec
