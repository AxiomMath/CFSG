module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep73
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofResidualMatrices

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard

theorem commute_of_sq_eq_one {Q : Type*} [Group Q] [Finite Q]
    (hS : ∀ S : Sylow 2 Q, IsMulCommutative (S : Subgroup Q)) {a b : Q} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) {k : ℕ} (hab : (a * b) ^ 2 ^ k = 1) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha])
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb])
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc, ← sq, ha, one_mul]
  have hPa : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ha)
  have hPw : IsPGroup 2 (zpowers (a * b)) := IsPGroup.of_card_dvd_pow (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hab)
  have hN : zpowers a ≤ normalizer (zpowers (a * b) : Subgroup Q) := by
    rw [zpowers_le, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (a * (a * b) * a⁻¹) = _
    rw [hconj, zpowers_inv]
  obtain ⟨S, hS'⟩ := (IsPGroup.to_sup_of_normal_right' hPa hPw hN).exists_le_sylow
  have haS : a ∈ S := hS' (mem_sup_left (mem_zpowers a))
  have hwS : a * b ∈ S := hS' (mem_sup_right (mem_zpowers _))
  have h : a * (a * b) = a * b * a :=
    congrArg Subtype.val ((hS S).is_comm.comm ⟨a, haS⟩ ⟨a * b, hwS⟩)
  have hb'' : b = a * b * a := by rw [← h, ← mul_assoc, ← sq, ha, one_mul]
  calc a * b = a * (a * b * a) := by rw [← hb'']
    _ = b * a := by rw [← mul_assoc, ← mul_assoc, ← sq, ha, one_mul]

section Lift

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem Represents.pow {x : G} {X : GL ι K} (hx : Represents e x X) (k : ℕ) :
    Represents e (x ^ k) (X ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact represents_one
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hx

theorem Represents.mem_center {z : G} (hz : Represents e z (1 : GL ι K)) :
    ∃ hzA : z ∈ A, (⟨z, hzA⟩ : ↥A) ∈ center ↥A := by
  obtain ⟨hzA, h1H, hz⟩ := hz
  refine ⟨hzA, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  apply e.injective
  have h1 : (⟨1, h1H⟩ : ↥H) = 1 := rfl
  rw [hz, h1, QuotientGroup.mk_one, map_one]

theorem odd_orderOf_of_represents_one (hZ : Odd (Nat.card (center ↥A))) {z : G}
    (hz : Represents e z (1 : GL ι K)) : Odd (orderOf z) := by
  obtain ⟨hzA, hzZ⟩ := hz.mem_center
  have h := orderOf_dvd_natCard (⟨⟨z, hzA⟩, hzZ⟩ : center ↥A)
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hZ h

theorem odd_orderOf_of_represents (hZ : Odd (Nat.card (center ↥A))) {y : G} {Y : GL ι K}
    (hy : Represents e y Y) {k : ℕ} (hk : Odd k) (hYk : Y ^ k = 1) : Odd (orderOf y) := by
  have h1 : Represents e (y ^ k) (1 : GL ι K) := hYk ▸ hy.pow k
  have h2 := odd_orderOf_of_represents_one hZ h1
  have h3 : y ^ (k * orderOf (y ^ k)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat (hk.mul h2) (orderOf_dvd_of_pow_eq_one h3)

theorem mul_pow_four_eq_one (hZ : Odd (Nat.card (center ↥A))) {x y : G} {X Y : GL ι K}
    (hx : Represents e x X) (hy : Represents e y Y) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hXY : (X * Y) ^ 4 = 1) : (x * y) ^ 4 = 1 := by
  have h1 : Represents e ((x * y) ^ 4) (1 : GL ι K) := hXY ▸ (hx.mul hy).pow 4
  have hodd := odd_orderOf_of_represents_one hZ h1
  obtain ⟨hzA, hzZ⟩ := h1.mem_center
  have hcomm : x * (x * y) ^ 4 = (x * y) ^ 4 * x :=
    congrArg Subtype.val (mem_center_iff.mp hzZ ⟨x, hx.1⟩)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
  have hconj : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hx', hy', ← mul_assoc, ← sq, hx2, one_mul]
  have hinv : x * (x * y) ^ 4 * x⁻¹ = ((x * y) ^ 4)⁻¹ := by
    rw [← conj_pow, hconj, inv_pow]
  have h3 : (x * y) ^ 4 = ((x * y) ^ 4)⁻¹ := by
    rw [← hinv, hcomm, mul_inv_cancel_right]
  have h4 : ((x * y) ^ 4) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, mul_eq_one_iff_eq_inv]
    exact h3
  exact eq_one_of_odd_of_pow hodd h4

end Lift

theorem eq_one_of_card_eq_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {x : K}
    (hx : x ≠ 0) : x = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [Fintype.card_eq_nat_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h

theorem linearTwoResidual : LinearTwoResidual := by
  intro G _ _ A D hD hq _ hZ t ht
  cases D with
  | linear n m hn hm hnm K hK e =>
    have hm1 : m = 1 := by
      have h : 2 ^ m = 2 ^ 1 := hq
      exact Nat.pow_right_injective le_rfl h
    subst hm1
    have hn5 : 5 ≤ n := by
      by_contra h
      exact hnm (by rw [show n = 4 by omega])
    have := charP_two_of_card hK
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨ht2, M, htM, hM2, hr⟩ := ht
    have ht2' : t ^ 2 = 1 := by
      rw [← ht2]
      exact pow_orderOf_eq_one t
    have hrank : ((M : Matrix (Fin n) (Fin n) K) - 1).rank = 2 := hr
    obtain ⟨u, v, d, hu2, hv2, hd3, hud, hvd, huM, hvM, hdM, huv4, hcc, hcM⟩ :=
      exists_residual_elements hn5 M (sub_one_mul_self_eq_zero hM2) hrank
    have hSL : ∀ X : GL (Fin n) K, X ∈ StatedSL n K := by
      intro X
      refine subset_closure ?_
      have h0 : (X : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).mp X.isUnit).ne_zero
      exact eq_one_of_card_eq_two hK2 h0
    choose uu huu2 huuR using fun k => exists_represents_sq_eq_one (e := e) hZ (hSL (u k)) (hu2 k)
    choose vv hvv2 hvvR using fun k => exists_represents_sq_eq_one (e := e) hZ (hSL (v k)) (hv2 k)
    obtain ⟨dd, hddR⟩ := exists_represents_of_mem (e := e) (hSL d)
    have hmemC : ∀ {y : G} {Y : GL (Fin n) K}, Represents e y Y → Y * M = M * Y →
        y ∈ A ⊓ centralizer ({t} : Set G) := by
      intro y Y hy hYM
      refine mem_inf.mpr ⟨hy.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact commute_of_represents hZ hy htM ht2' hYM
    have hoddC : ∀ {y : G} {Y : GL (Fin n) K}, Represents e y Y → Y * M = M * Y → Y ^ 3 = 1 →
        y ∈ oUpperTwo (A ⊓ centralizer ({t} : Set G)) := fun hy hYM hY3 =>
      subset_closure ⟨hmemC hy hYM, odd_orderOf_of_represents hZ hy ⟨1, rfl⟩ hY3⟩
    have hdO := hoddC hddR hdM hd3
    have hcommd : ∀ {Y : GL (Fin n) K}, Y * M = M * Y → Y * d * M = M * (Y * d) := by
      intro Y hYM
      rw [mul_assoc, hdM, ← mul_assoc, hYM, mul_assoc]
    have huO : ∀ k, uu k ∈ oUpperTwo (A ⊓ centralizer ({t} : Set G)) := by
      intro k
      have h := mul_mem (hoddC ((huuR k).mul hddR) (hcommd (huM k)) (hud k)) (inv_mem hdO)
      rwa [mul_inv_cancel_right] at h
    have hvO : ∀ k, vv k ∈ oUpperTwo (A ⊓ centralizer ({t} : Set G)) := by
      intro k
      have h := mul_mem (hoddC ((hvvR k).mul hddR) (hcommd (hvM k)) (hvd k)) (inv_mem hdO)
      rwa [mul_inv_cancel_right] at h
    have huv4' : ∀ k, (uu k * vv k) ^ 4 = 1 := fun k =>
      mul_pow_four_eq_one hZ (huuR k) (hvvR k) (huu2 k) (hvv2 k) (huv4 k)
    have hc2 : ∀ k, ((uu k * vv k) ^ 2) ^ 2 = 1 := fun k => by
      rw [← pow_mul]
      exact huv4' k
    have hcR : ∀ k, Represents e ((uu k * vv k) ^ 2) ((u k * v k) ^ 2) := fun k =>
      ((huuR k).mul (hvvR k)).pow 2
    have hcc' : Commute ((uu 0 * vv 0) ^ 2) ((uu 1 * vv 1) ^ 2) :=
      commute_of_represents hZ (hcR 0) (hcR 1) (hc2 1) hcc
    have htc : t = (uu 0 * vv 0) ^ 2 * (uu 1 * vv 1) ^ 2 := by
      have h1 := (hcR 0).mul (hcR 1)
      rw [hcM] at h1
      refine eq_of_represents hZ htM h1 (k := 1) (k' := 1) (by rw [pow_one]; exact ht2') ?_
      rw [pow_one, hcc'.mul_pow, hc2, hc2, one_mul]
    rw [admResidual, mem_sInf]
    rintro Y ⟨-, hYN, -, hsyl⟩
    have hcY : ∀ k, (uu k * vv k) ^ 2 ∈ Y := by
      intro k
      set X := oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆
      have huX : uu k ∈ X := mem_sup_left (huO k)
      have hvX : vv k ∈ X := mem_sup_left (hvO k)
      let π := QuotientGroup.mk' (Y.subgroupOf X)
      have ha : π ⟨uu k, huX⟩ ^ 2 = 1 := by
        rw [← map_pow, show (⟨uu k, huX⟩ : ↥X) ^ 2 = 1 from Subtype.ext (huu2 k), map_one]
      have hb : π ⟨vv k, hvX⟩ ^ 2 = 1 := by
        rw [← map_pow, show (⟨vv k, hvX⟩ : ↥X) ^ 2 = 1 from Subtype.ext (hvv2 k), map_one]
      have hab : (π ⟨uu k, huX⟩ * π ⟨vv k, hvX⟩) ^ 2 ^ 2 = 1 := by
        rw [← map_mul, ← map_pow,
          show ((⟨uu k, huX⟩ : ↥X) * ⟨vv k, hvX⟩) ^ 2 ^ 2 = 1 from Subtype.ext (huv4' k),
          map_one]
      have hcomm : Commute (π ⟨uu k, huX⟩) (π ⟨vv k, hvX⟩) := commute_of_sq_eq_one hsyl ha hb hab
      have h1 : π (((⟨uu k, huX⟩ : ↥X) * ⟨vv k, hvX⟩) ^ 2) = 1 := by
        rw [map_pow, map_mul, hcomm.mul_pow, ha, hb, one_mul]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact h1
    rw [htc]
    exact mul_mem (hcY 0) (hcY 1)
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
