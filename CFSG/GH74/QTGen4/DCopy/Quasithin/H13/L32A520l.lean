module

public import CFSG.Quasithin.H13.L32A520l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Holt
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace E9R_F4
open CFSG.Quasithin.H13.L32A.E9R_F4

variable {T L V H Y R : Subgroup G} (B : E9R_F4 T L V H Y R)
include B

theorem D_le_M_F4 : dT T L V H Y ≤ Subgroup.normalizer (L : Set G) := (dT_le_T T L V H Y).trans B.TL_F4

theorem H_le_N_l1_F4 : H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have h := B.toE9Ctx_F4.HL1Q_F4.trans (normalizer_le_normalizer_oTwoUpper (l1 T L V ⊔ pCoreOf 2 Y))
  rwa [B.toE9Ctx_F4.oTwoUpper_L1Q_F4] at h

theorem mem_D_of_two_F4 {x : G} (hx : x ∈ dT T L V H Y ⊔ R) {n : ℕ} (hn : x ^ 2 ^ n = 1) :
    x ∈ dT T L V H Y := by
  obtain ⟨d, hd, r, hr, rfl⟩ := B.mem_Yp_F4 hx
  have h2 : r ^ 2 ^ n ∈ dT T L V H Y := by
    have := mul_pow_mem_of_mem (N := dT T L V H Y) (n := d) (g := r) hd (B.R_le_N_D_F4 hr) (2 ^ n)
    rw [hn, one_mul] at this
    simpa using (dT T L V H Y).inv_mem this
  have h3 : r ^ 2 ^ n = 1 := by
    have : r ^ 2 ^ n ∈ dT T L V H Y ⊓ R := ⟨h2, R.pow_mem hr _⟩
    rw [B.D_inf_R_F4] at this
    exact this
  rw [B.eq_one_of_two_F4 hr h3, mul_one]
  exact hd

theorem YD_le_F4 : Y ⊔ dT T L V H Y ≤ dT T L V H Y ⊔ R := sup_le B.YX le_sup_left

theorem L1D_le_YD_F4 : (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y ≤ Y ⊔ dT T L V H Y :=
  sup_le_sup_right B.toE9Ctx_F4.L1Q_le_F4 _

theorem Yp_le_N_YD_F4 : dT T L V H Y ⊔ R ≤
    Subgroup.normalizer ((Y ⊔ dT T L V H Y : Subgroup G) : Set G) := fun _ hg =>
  F6.mem_normalizer_sup (B.HY (B.Yp_le_H_F4 hg)) (B.Yp_le_N_D_F4 hg)

theorem Yp_le_N_L1D_F4 : dT T L V H Y ⊔ R ≤
    Subgroup.normalizer (((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y : Subgroup G) : Set G) :=
  fun _ hg => F6.mem_normalizer_sup (B.toE9Ctx_F4.HL1Q_F4 (B.Yp_le_H_F4 hg)) (B.Yp_le_N_D_F4 hg)

theorem T_le_N_YD_F4 : T ≤ Subgroup.normalizer ((Y ⊔ dT T L V H Y : Subgroup G) : Set G) :=
  fun _ ht => F6.mem_normalizer_sup (B.TY_F4 ht) (B.toE9Ctx_F4.T_le_N_D_F4 ht)

theorem T_le_N_L1D_F4 : T ≤
    Subgroup.normalizer (((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y : Subgroup G) : Set G) :=
  fun _ ht => F6.mem_normalizer_sup (B.toE9Ctx_F4.T_le_N_L1Q_F4 ht) (B.toE9Ctx_F4.T_le_N_D_F4 ht)

theorem D_inf_F4 {W : Subgroup G} (hQW : pCoreOf 2 Y ≤ W) (hWY : W ≤ Y) :
    dT T L V H Y ⊓ W = pCoreOf 2 Y := by
  refine le_antisymm (fun x hx => ?_) (le_inf B.Q_le_D_F4 hQW)
  rw [← B.Y_inf_D_F4]
  exact ⟨hWY hx.2, hx.1⟩

theorem relIndex_WD_F4 {W : Subgroup G} (hQW : pCoreOf 2 Y ≤ W) (hWY : W ≤ Y) :
    (dT T L V H Y).relIndex (W ⊔ dT T L V H Y) = (pCoreOf 2 Y).relIndex W := by
  rw [relIndex_sup_of_le_normalizer (hWY.trans B.toE9Ctx_F4.Y_le_N_D_F4),
    ← Subgroup.inf_relIndex_right (dT T L V H Y) W, B.D_inf_F4 hQW hWY]

theorem R_inf_YD_F4 : R ⊓ (Y ⊔ dT T L V H Y) = pP Y R :=
  le_antisymm (fun _ hr => ⟨hr.1, B.mem_Y_of_mem_YD_F4 hr.1 hr.2⟩)
    (le_inf inf_le_left (inf_le_right.trans le_sup_left))

theorem indices_F4 :
    (dT T L V H Y).relIndex (Y ⊔ dT T L V H Y) = 9 ∧
      (dT T L V H Y).relIndex ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y) = 3 ∧
      (Y ⊔ dT T L V H Y).relIndex (dT T L V H Y ⊔ R) = 3 := by
  refine ⟨by rw [B.relIndex_WD_F4 (pCoreOf_le 2 Y) le_rfl, B.toE9Ctx_F4.card_F4],
    by rw [B.relIndex_WD_F4 le_sup_right B.toE9Ctx_F4.L1Q_le_F4, B.toE9Ctx_F4.L1Q3_F4], ?_⟩
  have hRN : R ≤ Subgroup.normalizer ((Y ⊔ dT T L V H Y : Subgroup G) : Set G) :=
    le_sup_right.trans B.Yp_le_N_YD_F4
  have h := relIndex_sup_of_le_normalizer hRN
  have hsup : R ⊔ (Y ⊔ dT T L V H Y) = dT T L V H Y ⊔ R :=
    le_antisymm (sup_le le_sup_right B.YD_le_F4) (sup_le (le_sup_right.trans le_sup_right) le_sup_left)
  rw [hsup, ← Subgroup.inf_relIndex_right (Y ⊔ dT T L V H Y) R, inf_comm, B.R_inf_YD_F4] at h
  rw [h, B.relIndex_P_F4.1]

theorem cube_mem_L1D_F4 {g : G} (hg : g ∈ dT T L V H Y ⊔ R) :
    g ^ 3 ∈ (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y := by
  obtain ⟨d, hd, r, hr, rfl⟩ := B.mem_Yp_F4 hg
  have h1 := mul_pow_mem_of_mem (N := dT T L V H Y) hd (B.R_le_N_D_F4 hr) 3
  rw [show (d * r) ^ 3 = (d * r) ^ 3 * (r ^ 3)⁻¹ * r ^ 3 by group]
  exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (B.cube_mem_P1_F4 hr).2)

theorem mem_YD_of_M_F4 {g : G} (hg : g ∈ dT T L V H Y ⊔ R)
    (hgM : g ∈ Subgroup.normalizer (L : Set G)) : g ∈ Y ⊔ dT T L V H Y := by
  obtain ⟨d, hd, r, hr, rfl⟩ := B.mem_Yp_F4 hg
  have hrM : r ∈ Subgroup.normalizer (L : Set G) := by
    rw [show r = d⁻¹ * (d * r) by group]
    exact mul_mem (inv_mem (B.D_le_M_F4 hd)) hgM
  rw [sup_comm]
  exact mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right (B.inf_M_le_P_F4 hr hrM).2)

theorem exists_N_F4 : ∃ N : Subgroup G, (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y ≤ N ∧
    N ≤ dT T L V H Y ⊔ R ∧ T ≤ Subgroup.normalizer (N : Set G) ∧
    ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y).relIndex N = 3 ∧
    (dT T L V H Y).relIndex N = 9 ∧ ¬ N ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYD9, hL1D3, hYp3⟩ := B.indices_F4
  have hconj : ∀ {K : Subgroup G}, T ≤ Subgroup.normalizer (K : Set G) →
      ∀ d ∈ T, ∀ x ∈ K, d * x * d⁻¹ ∈ K := fun hK d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hK hd) x).mp hx
  have hDL1D : dT T L V H Y ≤ (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y := le_sup_right
  have hL1DYD3 : ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y).relIndex (Y ⊔ dT T L V H Y) = 3 := by
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ hDL1D B.L1D_le_YD_F4
    rw [hYD9, hL1D3] at hm
    omega
  have hL1DYp9 : ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y).relIndex (dT T L V H Y ⊔ R) = 9 := by
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ B.L1D_le_YD_F4 B.YD_le_F4
    rw [hL1DYD3, hYp3] at hm
    omega
  have hL1DYp := B.L1D_le_YD_F4.trans B.YD_le_F4
  have hcommYp := comm_mem_of_relIndex_le' hL1DYp B.Yp_le_N_L1D_F4 (fun k hk => B.cube_mem_L1D_F4 hk)
    hL1DYp9.le
  obtain ⟨N, hL1DN, hNYp, hTN, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := dT T L V H Y ⊔ R)
      (Φ := (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y) (D := T) (T := Y ⊔ dT T L V H Y) hL1DYp
      hcommYp (fun k hk => B.cube_mem_L1D_F4 hk) B.toE9Ctx_F4.coprime_T_F4 (hconj B.TN)
      (hconj B.T_le_N_L1D_F4) B.L1D_le_YD_F4 B.YD_le_F4 (hconj B.T_le_N_YD_F4)
  have hTN' : T ≤ Subgroup.normalizer (N : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun x hx => hTN d hd x hx
  have hN3 : ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y).relIndex N = 3 := by
    have h := relIndex_sup_of_le_normalizer (hNYp.trans B.Yp_le_N_YD_F4)
    rw [sup_comm N (Y ⊔ dT T L V H Y), hsup, ← Subgroup.inf_relIndex_right (Y ⊔ dT T L V H Y) N,
      hinf, hYp3] at h
    exact h.symm
  have hN9 : (dT T L V H Y).relIndex N = 9 := by
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ hDL1D hL1DN
    rw [hL1D3, hN3] at hm
    omega
  refine ⟨N, hL1DN, hNYp, hTN', hN3, hN9, fun hle => ?_⟩
  have h1 : N ≤ (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y := by
    rw [← hinf]
    exact le_inf (fun x hx => B.mem_YD_of_M_F4 (hNYp hx) (hle hx)) le_rfl
  rw [Subgroup.relIndex_eq_one.mpr h1] at hN3
  exact absurd hN3 (by norm_num)

theorem not_exp_three_F4 {N : Subgroup G} (hL1DN : (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y ≤ N)
    (hNYp : N ≤ dT T L V H Y ⊔ R) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y).relIndex N = 3)
    (hN9 : (dT T L V H Y).relIndex N = 9) (hNM : ¬ N ≤ Subgroup.normalizer (L : Set G)) :
    ¬ ∀ n ∈ N, n ^ 3 ∈ dT T L V H Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hA
  apply hNM
  have hconj : ∀ {K : Subgroup G}, T ≤ Subgroup.normalizer (K : Set G) →
      ∀ d ∈ T, ∀ x ∈ K, d * x * d⁻¹ ∈ K := fun hK d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hK hd) x).mp hx
  have hDL1D : dT T L V H Y ≤ (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y := le_sup_right
  have hDN := hDL1D.trans hL1DN
  have hcommN := comm_mem_of_relIndex_le' hDN (hNYp.trans B.Yp_le_N_D_F4) hA hN9.le
  obtain ⟨N₃, hDN₃, hN₃N, hTN₃, hsup₃, hinf₃⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := N) (Φ := dT T L V H Y)
      (D := T) (T := (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y) hDN hcommN hA B.toE9Ctx_F4.coprime_T_F4
      (hconj hTN) (hconj B.toE9Ctx_F4.T_le_N_D_F4) hDL1D hL1DN (hconj B.T_le_N_L1D_F4)
  have hTN₃' : T ≤ Subgroup.normalizer (N₃ : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun x hx => hTN₃ d hd x hx
  have hN₃3 : (dT T L V H Y).relIndex N₃ = 3 := by
    have h := relIndex_sup_of_le_normalizer ((hN₃N.trans hNYp).trans B.Yp_le_N_L1D_F4)
    rw [sup_comm N₃ ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y), hsup₃,
      ← Subgroup.inf_relIndex_right ((l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y) N₃, hinf₃, hN3] at h
    exact h.symm
  have hp := B.pCore_eq_F4
  have hN₃M := le_M_of_three_F4 B.h331 B.hThm B.h1222 B.h1332 B.h1334 B.S B.Yp_le_H_F4
    (B.Yp_le_H_F4.trans B.H_le_N_l1_F4) (by rw [hp]; exact (dT_le_T T L V H Y)) (by rw [hp]; exact hDN₃)
    (hN₃N.trans hNYp) hTN₃' (fun k hk => by rw [hp]; exact hA k (hN₃N hk)) (by rw [hp]; exact hN₃3)
  have hL1DM : (l1 T L V ⊔ pCoreOf 2 Y) ⊔ dT T L V H Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le (l1_le_M T L V) (B.QT_F4.trans B.TL_F4)) B.D_le_M_F4
  rw [← hsup₃]
  exact sup_le hL1DM hN₃M

theorem conclusion_F4 : ∃ Y₀ : Subgroup G, Y₀ ≤ H ∧ l1 T L V ≤ Y₀ ∧
    T ≤ Subgroup.normalizer (Y₀ : Set G) ∧
    Nonempty (↥Y₀ ⧸ (pCoreOf 2 Y₀).subgroupOf Y₀ ≃* Multiplicative (ZMod 9)) ∧
    ¬ Y₀ ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hL1DN, hNYp, hTN, hN3, hN9, hNM⟩ := B.exists_N_F4
  have hDN : dT T L V H Y ≤ N := le_sup_right.trans hL1DN
  have hpN : pCoreOf 2 N = dT T L V H Y := by
    refine le_antisymm (fun x hx => ?_)
      (le_pCoreOf_of_le_normalizer 2 hDN (hNYp.trans B.Yp_le_N_D_F4) B.D2_F4)
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 N ⟨x, hx⟩
    exact B.mem_D_of_two_F4 (hNYp (pCoreOf_le 2 N hx)) (n := n)
      (by simpa using congrArg Subtype.val hn)
  have hA := B.not_exp_three_F4 hL1DN hNYp hTN hN3 hN9 hNM
  push Not at hA
  obtain ⟨n₀, hn₀, hn₀D⟩ := hA
  have hcard : Nat.card (↥N ⧸ (pCoreOf 2 N).subgroupOf N) = 9 := by
    rw [← relIndex_eq_card_quot, hpN, hN9]
  have hq9 : (QuotientGroup.mk' ((pCoreOf 2 N).subgroupOf N) ⟨n₀, hn₀⟩) ^ 9 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hq3 : (QuotientGroup.mk' ((pCoreOf 2 N).subgroupOf N) ⟨n₀, hn₀⟩) ^ 3 ≠ 1 := by
    intro h
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      hpN] at h
    exact hn₀D (by simpa using h)
  have hord : orderOf (QuotientGroup.mk' ((pCoreOf 2 N).subgroupOf N) ⟨n₀, hn₀⟩) = 9 := by
    have hd : orderOf (QuotientGroup.mk' ((pCoreOf 2 N).subgroupOf N) ⟨n₀, hn₀⟩) ∣ 3 ^ 2 :=
      orderOf_dvd_of_pow_eq_one (by norm_num; exact hq9)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases i
    · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [hi']; norm_num)) hq3
    · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [hi']; norm_num)) hq3
    · rw [hi']
      norm_num
  have hcyc : IsCyclic (↥N ⧸ (pCoreOf 2 N).subgroupOf N) :=
    isCyclic_of_orderOf_eq_card _ (by rw [hord, hcard])
  have e := (zmodCyclicMulEquiv hcyc).symm
  rw [hcard] at e
  exact ⟨N, hNYp.trans B.Yp_le_H_F4, (le_sup_left.trans le_sup_left).trans hL1DN, hTN, ⟨e⟩, hNM⟩

end E9R_F4

theorem lemma14_5_20E9_of_F4 (h331 : Stmt3_3_1_F4) (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
      ∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
        (∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) → l1 T L V ≤ Y →
        IsElemAbelianOfRank 3 2 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) →
        ∃ Y₀ : Subgroup G, Y₀ ≤ H ∧ l1 T L V ≤ Y₀ ∧ T ≤ Subgroup.normalizer (Y₀ : Set G) ∧
          Nonempty (↥Y₀ ⧸ (pCoreOf 2 Y₀).subgroupOf Y₀ ≃* Multiplicative (ZMod 9)) ∧
          ¬ Y₀ ≤ Subgroup.normalizer (L : Set G) := by
  intro G _ _ T L V H S Y hYH hHY hY3 hL1Y hE
  have C : E9Ctx_F4 T L V H Y := ⟨h331, hThm, h1222, h1332, h1334, S, hYH, hHY, hY3, hL1Y, hE⟩
  obtain ⟨R, hR, hTN, hYX, hnc0⟩ := C.exists_R1_F4
  exact (⟨C, hR, hTN, hYX, hnc0⟩ : E9R_F4 T L V H Y R).conclusion_F4

end CFSG.Quasithin.H13.L32A
