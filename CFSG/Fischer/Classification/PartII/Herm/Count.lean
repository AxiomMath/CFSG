module

public import CFSG.Fischer.Classification.Unitary.Model
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer.Classification

open CFSG.ClassicalGroups.Unitary CFSG.Fischer.Classification.Unitary Module
open CFSG.Blueprint.Fischer (K)
open scoped LinearAlgebra.Projectivization

namespace Herm

theorem add_frob_eq_one_iff (c : K) : c + frob c = 1 ↔ c = ω ∨ c = ω + 1 := by
  obtain ⟨c, rfl⟩ := eF4.surjective c
  rw [frob_eF4, omega_eq, ← map_one eF4, ← map_add, ← map_add, eF4_inj, eF4_inj, eF4_inj]
  revert c
  decide

theorem omega_ne_omega_add_one : ω ≠ ω + 1 := by
  intro h
  have h' : (0 : K) + ω = 1 + ω := by rw [zero_add, add_comm]; exact h
  exact zero_ne_one (add_right_cancel h')

theorem natCard_trace_eq {t : K} (ht : t = 0 ∨ t = 1) :
    Nat.card {c : K // c + frob c = t} = 2 := by
  rcases ht with rfl | rfl
  · have e : ∀ c : K, c + frob c = 0 ↔ c ∈ ({0, 1} : Set K) := fun c => by
      rw [add_frob_eq_zero_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [Nat.card_congr (Equiv.subtypeEquivRight e), Nat.card_coe_set_eq,
      Set.ncard_pair zero_ne_one]
  · have e : ∀ c : K, c + frob c = 1 ↔ c ∈ ({ω, ω + 1} : Set K) := fun c => by
      rw [add_frob_eq_one_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [Nat.card_congr (Equiv.subtypeEquivRight e), Nat.card_coe_set_eq,
      Set.ncard_pair omega_ne_omega_add_one]

variable {N : ℕ}

@[expose] noncomputable def perp2 (v u : Fin N → K) : Submodule K (Fin N → K) :=
  LinearMap.ker ((hermL frob v).prod (hermL frob u))

theorem mem_perp2 {v u w : Fin N → K} :
    w ∈ perp2 v u ↔ herm frob v w = 0 ∧ herm frob u w = 0 := by
  rw [perp2, LinearMap.mem_ker, LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero,
    hermL_apply, hermL_apply]

variable {v u : Fin N → K} (hv : herm frob v v = 0) (hu : herm frob u u = 0)
  (hvu : herm frob v u = 1)
include hv hu hvu

theorem natCard_perp2 : 2 ≤ N ∧ Nat.card (perp2 v u) = 4 ^ (N - 2) := by
  set f := (hermL frob v).prod (hermL frob u)
  have huv : herm frob u v = 1 := by rw [herm_conj frob frob_frob, hvu, map_one]
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨a • u + b • v, ?_⟩
    simp only [f, LinearMap.prod_apply, Function.prod_apply, hermL_apply, herm_add_right,
      herm_smul_right, hv, hu, hvu, huv, mul_one, mul_zero, add_zero, zero_add]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at h1
  have hk : finrank K (LinearMap.ker f) = N - 2 := by omega
  refine ⟨by omega, ?_⟩
  change Nat.card (LinearMap.ker f) = _
  rw [Module.natCard_eq_pow_finrank (K := K), card_K, hk]
  norm_num

theorem herm_decomp {w : Fin N → K} (hw : w ∈ perp2 v u) (c : K) :
    herm frob (c • v + u + w) (c • v + u + w) = c + frob c + herm frob w w ∧
      herm frob v (c • v + u + w) = 1 ∧ herm frob u (c • v + u + w) = c := by
  obtain ⟨hvw, huw⟩ := mem_perp2.1 hw
  have huv : herm frob u v = 1 := by rw [herm_conj frob frob_frob, hvu, map_one]
  have hwv : herm frob w v = 0 := herm_eq_zero_comm frob frob_frob hvw
  have hwu : herm frob w u = 0 := herm_eq_zero_comm frob frob_frob huw
  refine ⟨?_, ?_, ?_⟩
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hv, hu, hvu, huv,
      hvw, huw, hwv, hwu, mul_zero, mul_one, add_zero, zero_add]
  · simp only [herm_add_right, herm_smul_right, hv, hvu, hvw, mul_zero, zero_add, add_zero]
  · simp only [herm_add_right, herm_smul_right, huv, hu, huw, mul_one, add_zero]

theorem sub_mem_perp2 {x : Fin N → K} (hx : herm frob v x = 1) :
    x - herm frob u x • v - u ∈ perp2 v u := by
  have huv : herm frob u v = 1 := by rw [herm_conj frob frob_frob, hvu, map_one]
  refine mem_perp2.2 ⟨?_, ?_⟩
  · rw [herm_sub_right, herm_sub_right, herm_smul_right, hv, hvu, hx, mul_zero, sub_zero, sub_self]
  · rw [herm_sub_right, herm_sub_right, herm_smul_right, huv, hu, mul_one, sub_self, sub_zero]

@[expose] noncomputable def normEquiv :
    {x : Fin N → K // herm frob x x = 0 ∧ herm frob v x = 1} ≃
      {p : perp2 v u × K // p.2 + frob p.2 = herm frob (p.1 : Fin N → K) p.1} where
  toFun x := ⟨(⟨x.1 - herm frob u x.1 • v - u, sub_mem_perp2 hv hu hvu x.2.2⟩, herm frob u x.1),
    by
      have h := (herm_decomp hv hu hvu (sub_mem_perp2 hv hu hvu x.2.2) (herm frob u x.1)).1
      rw [show herm frob u x.1 • v + u + (x.1 - herm frob u x.1 • v - u) = x.1 by abel, x.2.1]
        at h
      exact (eq_neg_of_add_eq_zero_left h.symm).trans (neg_K _)⟩
  invFun p := ⟨p.1.2 • v + u + p.1.1, by
    rw [(herm_decomp hv hu hvu p.1.1.2 p.1.2).1, p.2, add_self_K],
    (herm_decomp hv hu hvu p.1.1.2 p.1.2).2.1⟩
  left_inv x := Subtype.ext
    (show herm frob u x.1 • v + u + (x.1 - herm frob u x.1 • v - u) = x.1 by abel)
  right_inv p := by
    obtain ⟨-, -, h3⟩ := herm_decomp hv hu hvu p.1.1.2 p.1.2
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)
    · simp only [h3]
      abel
    · exact h3

end Herm

open Herm

variable {N : ℕ}

theorem natCard_isotropic_herm_eq_one {v : Fin N → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    Nat.card {x : Fin N → K // herm frob x x = 0 ∧ herm frob v x = 1} = 4 ^ N / 8 := by
  obtain ⟨u, -, hu, hvu⟩ := exists_partner_frob hv0 hv
  obtain ⟨hN, hW⟩ := natCard_perp2 hv hu hvu
  rw [Nat.card_congr ((normEquiv hv hu hvu).trans (Equiv.subtypeProdEquivSigmaSubtype
    fun (w : perp2 v u) (c : K) => c + frob c = herm frob (w : Fin N → K) w))]
  have : Fintype (perp2 v u) := Fintype.ofFinite _
  rw [Nat.card_sigma, Finset.sum_congr rfl fun (w : perp2 v u) _ =>
    natCard_trace_eq (herm_self_eq_zero_or_one (w : Fin N → K)), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, hW, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)).symm

theorem natCard_isoPts_herm_ne_zero {v : Fin N → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    Nat.card {p : isoPts frob N // herm frob v (p : ℙ K (Fin N → K)).rep ≠ 0} = 4 ^ N / 8 := by
  rw [← natCard_isotropic_herm_eq_one hv0 hv]
  have hx0 : ∀ x : {x : Fin N → K // herm frob x x = 0 ∧ herm frob v x = 1}, x.1 ≠ 0 :=
    fun x h => by
      have := x.2.2
      rw [h, herm_zero_right] at this
      exact zero_ne_one this
  have hrep : ∀ x : {x : Fin N → K // herm frob x x = 0 ∧ herm frob v x = 1},
      herm frob v (pt x.1 (hx0 x) x.2.1 : ℙ K (Fin N → K)).rep ≠ 0 := fun x => by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x.1 (hx0 x)
    change herm frob v (Projectivization.mk K x.1 (hx0 x)).rep ≠ 0
    rw [← ha, Units.smul_def, herm_smul_right, x.2.2, mul_one]
    exact a.ne_zero
  symm
  refine Nat.card_eq_of_bijective (fun x => ⟨pt x.1 (hx0 x) x.2.1, hrep x⟩) ⟨fun x y h => ?_,
    fun p => ?_⟩
  · obtain ⟨c, hc⟩ := (pt_eq_pt_iff (hx0 x) (hx0 y) x.2.1 y.2.1).1 (congrArg Subtype.val h)
    have h1 := x.2.2
    rw [← hc, herm_smul_right, y.2.2, mul_one] at h1
    refine Subtype.ext ?_
    rw [← hc, h1, one_smul]
  · set c := herm frob v (p.1 : ℙ K (Fin N → K)).rep with hc
    have hc0 : c ≠ 0 := p.2
    have hr0 := (p.1 : ℙ K (Fin N → K)).rep_nonzero
    have hiso : herm frob (p.1 : ℙ K (Fin N → K)).rep (p.1 : ℙ K (Fin N → K)).rep = 0 := p.1.2
    refine ⟨⟨c⁻¹ • (p.1 : ℙ K (Fin N → K)).rep, ⟨by rw [herm_smul_left, herm_smul_right, hiso,
      mul_zero, mul_zero], by rw [herm_smul_right, ← hc, inv_mul_cancel₀ hc0]⟩⟩,
      Subtype.ext (Subtype.ext ?_)⟩
    change Projectivization.mk K _ _ = (p.1 : ℙ K (Fin N → K))
    conv_rhs => rw [← Projectivization.mk_rep (p.1 : ℙ K (Fin N → K))]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ hr0).2 ⟨c⁻¹, rfl⟩

end CFSG.Fischer.Classification
