module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit
public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Basic

public section

namespace CFSG.OddStandard.AltStdCycTwo.Shape3

open Subgroup Equiv Equiv.Perm
open AltStdBal (Cyc rho rho_of_mem eq_one_of_mem_of_mem_centralizer eq_one_or_eq_of_card_eq_two)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem z_not_mem_L (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (d : Cyc L Q z) :
    z ∉ L := by
  intro hzL
  have h1 := eq_one_of_mem_of_mem_centralizer θ (by omega) hzL (d.le d.mem)
  have := d.order
  rw [h1, orderOf_one] at this
  omega

theorem sign_rho_eq_neg_one (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hc : c ∉ L ⊔ centralizer (L : Set G)) :
    sign (rho θ hn ⟨c, hcN⟩) = -1 := by
  rcases Int.units_eq_one_or (sign (rho θ hn ⟨c, hcN⟩)) with h | h
  · exact absurd (mem_sup_of_rho_mem θ hn hcN (mem_alternatingGroup.2 h)) hc
  · exact h

theorem sign_rho_eq_one (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hc : c ∈ L ⊔ centralizer (L : Set G)) :
    sign (rho θ hn ⟨c, hcN⟩) = 1 :=
  mem_alternatingGroup.1 ((mem_evenAct_iff θ hn hcN).1 (sup_le_evenAct θ hn hc))

theorem inv_mul_mem_sup (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {u c : G}
    (huN : u ∈ normalizer (L : Set G)) (hcN : c ∈ normalizer (L : Set G))
    (hu : u ∉ L ⊔ centralizer (L : Set G)) (hc : c ∉ L ⊔ centralizer (L : Set G)) :
    u⁻¹ * c ∈ L ⊔ centralizer (L : Set G) := by
  have hN : u⁻¹ * c ∈ normalizer (L : Set G) := mul_mem (inv_mem huN) hcN
  refine mem_sup_of_rho_mem θ hn hN (mem_alternatingGroup.2 ?_)
  have h : (⟨u⁻¹ * c, hN⟩ : normalizer (L : Set G)) =
      (⟨u, huN⟩ : normalizer (L : Set G))⁻¹ * ⟨c, hcN⟩ := rfl
  rw [h]
  simp only [map_mul, map_inv]
  rw [sign_rho_eq_neg_one θ hn huN hu, sign_rho_eq_neg_one θ hn hcN hc]
  decide

theorem conj_mem_sup (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {c x : G}
    (hcN : c ∈ normalizer (L : Set G)) (hx : x ∈ L ⊔ centralizer (L : Set G)) :
    c * x * c⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
  have hxN : x ∈ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _) hx
  have hN : c * x * c⁻¹ ∈ normalizer (L : Set G) := mul_mem (mul_mem hcN hxN) (inv_mem hcN)
  refine mem_sup_of_rho_mem θ hn hN (mem_alternatingGroup.2 ?_)
  have h : (⟨c * x * c⁻¹, hN⟩ : normalizer (L : Set G)) =
      ⟨c, hcN⟩ * ⟨x, hxN⟩ * (⟨c, hcN⟩ : normalizer (L : Set G))⁻¹ := rfl
  rw [h]
  simp only [map_mul, map_inv]
  rw [sign_rho_eq_one θ hn hxN hx, mul_one, mul_inv_cancel]

theorem exists_mul_of_two_pow (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {c : G}
    (hcC : c ∈ centralizer ({z} : Set G)) (hc : c ∈ L ⊔ centralizer (L : Set G)) {k : ℕ}
    (hck : c ^ 2 ^ k = 1) : ∃ l ∈ L, ∃ q ∈ Q, l * q = c := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
    (Subgroup.centralizer_le_normalizer _)
  have hc' : c ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hmul]
    exact hc
  obtain ⟨l, hl, m, hm, rfl⟩ := Set.mem_mul.1 hc'
  have hmC : m ∈ centralizer ({z} : Set G) := by
    have h1 : m = l⁻¹ * (l * m) := by group
    rw [h1]
    exact mul_mem (inv_mem (le_cent_single hS d hl)) hcC
  have hlm : Commute l m := mem_centralizer_iff.1 hm l hl
  rw [hlm.mul_pow] at hck
  have hl1 : l ^ 2 ^ k = 1 := by
    refine eq_one_of_mem_of_mem_centralizer θ (by omega) (pow_mem hl _) ?_
    rw [eq_inv_of_mul_eq_one_left hck]
    exact inv_mem (pow_mem hm _)
  rw [hl1, one_mul] at hck
  exact ⟨l, hl, m, zpowers_le.2 d.mem (mem_zpowers_of_two_pow d hQ2 ⟨hm, hmC⟩ hck), rfl⟩

theorem exists_sq_eq_mul (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huO : u ∉ L ⊔ centralizer (L : Set G))
    (hu2 : u ^ 2 = z) {r : G} (hr : r ∈ centralizer ({z} : Set G))
    (hrO : r ∉ L ⊔ centralizer (L : Set G)) {k : ℕ} (hrk : r ^ 2 ^ k = 1) :
    ∃ l ∈ L, r * r = z * l := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hC
  have hCN := cent_le_normalizer hS d
  have hu4 : orderOf u = 4 := AltStdSec.orderOf_eq_four_of_sq_eq d hu2
  have hup : IsPGroup 2 (zpowers (⟨u, hu⟩ : C)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu4]; norm_num)
  have hrp : IsPGroup 2 (zpowers (⟨r, hr⟩ : C)) := by
    have h1 : (⟨r, hr⟩ : C) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hrk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hP⟩ := hup.exists_le_sylow
  obtain ⟨T, hT⟩ := hrp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P T
  have hcu : c * (⟨u, hu⟩ : C) * c⁻¹ ∈ (T : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hP (mem_zpowers _), by simp [MulAut.conj_apply]⟩
  have hrT : (⟨r, hr⟩ : C) ∈ (T : Subgroup C) := hT (mem_zpowers _)
  set v : G := (c : G) * u * (c : G)⁻¹ with hv
  have hvC : v ∈ C := mul_mem (mul_mem c.2 hu) (inv_mem c.2)
  have hvO : v ∉ L ⊔ centralizer (L : Set G) := by
    intro hmem
    apply huO
    have := conj_mem_sup θ hn (hCN (inv_mem c.2)) hmem
    simpa [hv, mul_assoc] using this
  have hv2 : v ^ 2 = z := by
    have hzc : (c : G) * z * (c : G)⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.1 c.2]
      group
    calc v ^ 2 = (c : G) * u ^ 2 * (c : G)⁻¹ := by rw [hv, sq, sq]; group
      _ = z := by rw [hu2, hzc]
  have hvrT : (⟨v⁻¹ * r, mul_mem (inv_mem hvC) hr⟩ : C) ∈ (T : Subgroup C) := by
    have h1 : (⟨v⁻¹ * r, mul_mem (inv_mem hvC) hr⟩ : C) = (c * ⟨u, hu⟩ * c⁻¹)⁻¹ * ⟨r, hr⟩ := rfl
    rw [h1]
    exact mul_mem (inv_mem hcu) hrT
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 T.isPGroup' ⟨_, hvrT⟩
  have hvrj : (v⁻¹ * r) ^ 2 ^ j = 1 := by
    have h1 := pow_orderOf_eq_one (⟨_, hvrT⟩ : (T : Subgroup C))
    rw [hj] at h1
    have h2 := congrArg (fun x : (T : Subgroup C) => ((x : C) : G)) h1
    simpa using h2
  obtain ⟨l, hl, q, hq, hlq⟩ := exists_mul_of_two_pow hS θ hn d hQ2
    (mul_mem (inv_mem hvC) hr) (inv_mul_mem_sup θ hn (hCN hvC) (hCN hr) hvO hrO) hvrj
  have hqv : v * q = q * v := AltStdSec.comm_of_mem_Q d hQ2 hq hvC
  have hql : l * q = q * l := d.comm_L hq hl
  have hqq : q * q = 1 := by
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
    · simp
    · exact d.mul_self
  have hl' : v⁻¹ * l * v ∈ L := by
    have := (mem_normalizer_iff.1 (hCN (inv_mem hvC)) l).1 hl
    simpa using this
  have hr' : r = v * (l * q) := by rw [hlq]; group
  refine ⟨v⁻¹ * l * v * l, mul_mem hl' hl, ?_⟩
  rw [hr']
  calc v * (l * q) * (v * (l * q)) = v * l * (q * v) * l * q := by group
    _ = v * l * (v * q) * l * q := by rw [hqv]
    _ = v * l * v * (q * l) * q := by group
    _ = v * l * v * (l * q) * q := by rw [hql]
    _ = v * l * v * l * (q * q) := by group
    _ = v * l * v * l := by rw [hqq, mul_one]
    _ = (v * v) * (v⁻¹ * l * v * l) := by group
    _ = z * (v⁻¹ * l * v * l) := by rw [← sq, hv2]

end CFSG.OddStandard.AltStdCycTwo.Shape3
