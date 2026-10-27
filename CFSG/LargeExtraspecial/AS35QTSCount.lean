module

public import CFSG.LargeExtraspecial.AS35QTSGlobal
public import CFSG.LargeExtraspecial.AS35QTSThompson
public import CFSG.LargeExtraspecial.AS35JFiveNineTwo

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup

variable {G : Type} [Group G] (S : Setting G)

theorem iterate_mulC (c : Cd) (m : ℕ) : (fun x => mulC x c)^[m] e0 = powC c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem mem_zpowL {c d : Cd} : d ∈ zpowL c ↔ ∃ m < 72, d = powC c m := by
  rw [zpowL, List.mem_iterate]
  simp only [iterate_mulC]

theorem commute_of_mem_zpowers {x v u : G} (hx : x * x = 1) (hv : v * v = 1)
    (hu : u ∈ zpowers (x * v)) (huu : u * u = 1) : x * u = u * x ∧ v * u = u * v := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  obtain ⟨k, hk⟩ := hu
  simp only at hk
  subst hk
  have h1 : x * (x * v) * x⁻¹ = (x * v)⁻¹ := by
    rw [mul_inv_rev, hxinv, hvinv, ← mul_assoc, hx, one_mul]
  have h2 : v * (x * v) * v⁻¹ = (x * v)⁻¹ := by
    rw [mul_inv_rev, hxinv, hvinv, mul_assoc, mul_assoc, hv, mul_one]
  constructor
  · have := conj_zpow (a := x) (b := x * v) (i := k)
    rw [h1, inv_zpow, huinv] at this
    calc x * (x * v) ^ k = x * (x * v) ^ k * x⁻¹ * x := by group
      _ = (x * v) ^ k * x := by rw [← this]
  · have := conj_zpow (a := v) (b := x * v) (i := k)
    rw [h2, inv_zpow, huinv] at this
    calc v * (x * v) ^ k = v * (x * v) ^ k * v⁻¹ * v := by group
      _ = (x * v) ^ k * v := by rw [← this]

theorem mem_M_of_zpowers {x v : G} (hx : x * x = 1) (hv : v * v = 1)
    (h : S.z ∈ zpowers (x * v)) : x ∈ S.M ∧ v ∈ S.M := by
  obtain ⟨h1, h2⟩ := commute_of_mem_zpowers hx hv h S.z_mul_z
  exact ⟨S.mem_M_iff.mpr h1, S.mem_M_iff.mpr h2⟩

namespace Chart

variable {S} [Finite G] (T : Chart S)

omit [Finite G] in
theorem th_pow72 {y : G} (hy : y ∈ S.M) : pow72 (T.th y) = T.th (y ^ 72) := by
  have hy2 : y ^ 2 ∈ S.M := S.M.pow_mem hy 2
  have hy4 : y ^ 4 ∈ S.M := S.M.pow_mem hy 4
  have hy8 : y ^ 8 ∈ S.M := S.M.pow_mem hy 8
  have hy16 : y ^ 16 ∈ S.M := S.M.pow_mem hy 16
  have hy32 : y ^ 32 ∈ S.M := S.M.pow_mem hy 32
  have hy64 : y ^ 64 ∈ S.M := S.M.pow_mem hy 64
  have h2 : T.th (y ^ 2) = mulC (T.th y) (T.th y) := by rw [← T.th_mul _ hy _ hy, pow_two]
  have h4 : T.th (y ^ 4) = mulC (T.th (y ^ 2)) (T.th (y ^ 2)) := by
    rw [← T.th_mul _ hy2 _ hy2, ← pow_add]
  have h8 : T.th (y ^ 8) = mulC (T.th (y ^ 4)) (T.th (y ^ 4)) := by
    rw [← T.th_mul _ hy4 _ hy4, ← pow_add]
  have h16 : T.th (y ^ 16) = mulC (T.th (y ^ 8)) (T.th (y ^ 8)) := by
    rw [← T.th_mul _ hy8 _ hy8, ← pow_add]
  have h32 : T.th (y ^ 32) = mulC (T.th (y ^ 16)) (T.th (y ^ 16)) := by
    rw [← T.th_mul _ hy16 _ hy16, ← pow_add]
  have h64 : T.th (y ^ 64) = mulC (T.th (y ^ 32)) (T.th (y ^ 32)) := by
    rw [← T.th_mul _ hy32 _ hy32, ← pow_add]
  have h72 : T.th (y ^ 72) = mulC (T.th (y ^ 64)) (T.th (y ^ 8)) := by
    rw [← T.th_mul _ hy64 _ hy8, ← pow_add]
  simp only [pow72]
  rw [← h2, ← h4, ← h8, ← h16, ← h32, ← h64, ← h72]

omit [Finite G] in
theorem mem_zpowers_iff_zpowL {y u : G} (hy : y ∈ S.M) (hu : u ∈ S.M)
    (h72 : pow72 (T.th y) = e0) : u ∈ zpowers y ↔ T.th u ∈ zpowL (T.th y) := by
  have hy72 : y ^ 72 = 1 := by
    rw [T.th_pow72 hy] at h72
    exact (T.th_eq_e0_iff (S.M.pow_mem hy 72)).mp h72
  rw [mem_zpowL]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(k % 72).toNat, by omega, ?_⟩
    rw [← T.th_pow hy]
    congr 1
    change y ^ k = y ^ (k % 72).toNat
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    exact zpow_eq_zpow_emod' k hy72
  · rintro ⟨m, -, hm⟩
    rw [← T.th_pow hy] at hm
    refine ⟨m, ?_⟩
    change y ^ (m : ℤ) = u
    rw [zpow_natCast]
    exact T.th_injOn _ (S.M.pow_mem hy m) _ hu hm.symm

theorem exists_t0 (hS : S.SixHyp) : ∃ t₀ ∈ S.DSet, T.th t₀ = t0c := by
  obtain ⟨t₁, ht₁⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  have ht₁M := S.mem_M_of_mem_ESet hS.sixFour ht₁.1
  have hs := T.th_mem_sl hS.weak ht₁M (S.isConj_of_mem_ESet ht₁.1) (S.ne_z_of_mem_ESet ht₁.1)
  obtain ⟨m, hm, τ₀, hτ₀, hτ, hmτ⟩ := T.exists_conj_t0 ht₁M hs
  refine ⟨τ₀, ?_, hτ⟩
  have := S.conj_mem_DSet (S.M.inv_mem hm) ht₁
  rwa [← hmτ, show m⁻¹ * (m * τ₀ * m⁻¹) * m⁻¹⁻¹ = τ₀ by group] at this

section T0

variable {t₀ : G} (ht₀ : t₀ ∈ S.DSet) (htc : T.th t₀ = t0c)
include ht₀

theorem t0_mem_M (hS : S.SixHyp) : t₀ ∈ S.M := S.mem_M_of_mem_ESet hS.sixFour ht₀.1

omit [Finite G] in
theorem t0_isConj : IsConj S.z t₀ := S.isConj_of_mem_ESet ht₀.1

theorem t0_ne : t₀ ≠ S.z := S.ne_z_of_mem_ESet ht₀.1

theorem w_mul_self (hS : S.SixHyp) : S.z * t₀ * (S.z * t₀) = 1 := by
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp (t0_mem_M ht₀ hS)
  have htt := S.mul_self_of_isConj (t0_isConj ht₀)
  calc S.z * t₀ * (S.z * t₀) = S.z * (t₀ * S.z) * t₀ := by group
    _ = 1 := by rw [hzt, ← mul_assoc, S.z_mul_z, one_mul, htt]

theorem w_ne_one : S.z * t₀ ≠ 1 := by
  intro h
  apply t0_ne ht₀
  calc t₀ = S.z * (S.z * t₀) := by rw [← mul_assoc, S.z_mul_z, one_mul]
    _ = S.z := by rw [h, mul_one]

include T in
theorem isConj_w_iff (hS : S.SixHyp) {v : G} :
    IsConj (S.z * t₀) v ↔ v * v = 1 ∧ v ≠ 1 ∧ ¬ IsConj S.z v := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    refine ⟨?_, ?_, fun h' => T.not_isConj_both hS (t0_mem_M ht₀ hS) (t0_isConj ht₀)
      (t0_ne ht₀) h' h⟩
    · rw [show g * (S.z * t₀) * g⁻¹ * (g * (S.z * t₀) * g⁻¹) =
        g * (S.z * t₀ * (S.z * t₀)) * g⁻¹ by group, w_mul_self ht₀ hS]
      group
    · intro h1
      apply w_ne_one ht₀
      calc S.z * t₀ = g⁻¹ * (g * (S.z * t₀) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
  · rintro ⟨h1, h2, h3⟩
    exact (T.isConj_or_isConj hS (t0_mem_M ht₀ hS) (t0_isConj ht₀) (t0_ne ht₀) h1 h2).resolve_left
      h3

include T in
theorem isConj_w_iff_th (hS : S.SixHyp) {v : G} (hv : v ∈ S.M) :
    IsConj (S.z * t₀) v ↔ T.th v ∈ wl := by
  rw [T.isConj_w_iff ht₀ hS, mem_wl, ← T.mem_D_iff hS hv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨T.th_mem_il hv h1 h2, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨(T.mul_self_of_mem_il hv h1).1, (T.mul_self_of_mem_il hv h1).2, h3⟩

end T0

omit [Finite G] in
theorem ncard_pairs_eq {P : Set (G × G)} {F : Finset (Cd × Cd)}
    (hPM : ∀ p ∈ P, p.1 ∈ S.M ∧ p.2 ∈ S.M)
    (hPF : ∀ p ∈ P, (T.th p.1, T.th p.2) ∈ F)
    (hFP : ∀ x ∈ S.M, ∀ v ∈ S.M, (T.th x, T.th v) ∈ F → (x, v) ∈ P)
    (hFc : ∀ q ∈ F, q.1 ∈ codes ∧ q.2 ∈ codes) : P.ncard = F.card := by
  have hinj : Set.InjOn (fun p : G × G => (T.th p.1, T.th p.2)) P := by
    intro p hp p' hp' h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (T.th_injOn _ (hPM p hp).1 _ (hPM p' hp').1 h.1)
      (T.th_injOn _ (hPM p hp).2 _ (hPM p' hp').2 h.2)
  rw [← hinj.ncard_image, ← Set.ncard_coe_finset]
  congr 1
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hPF p hp
  · intro hq
    obtain ⟨x, hx, hxq⟩ := T.th_surj q.1 (hFc q hq).1
    obtain ⟨v, hv, hvq⟩ := T.th_surj q.2 (hFc q hq).2
    refine ⟨(x, v), hFP x hx v hv ?_, ?_⟩
    · rw [hxq, hvq]
      exact hq
    · simp only [hxq, hvq]

include T in
theorem count_z (hS : S.SixHyp) {t₀ : G} (ht₀ : t₀ ∈ S.DSet) :
    thompsonCount S.z (S.z * t₀) S.z = 1188 := by
  classical
  rw [thompsonCount, ← qts_nz.2]
  refine T.ncard_pairs_eq (fun p hp => ?_) (fun p hp => ?_) (fun x hx v hv hq => ?_) ?_
  · exact mem_M_of_zpowers S (S.mul_self_of_isConj hp.1)
      ((T.isConj_w_iff ht₀ hS).mp hp.2.1).1 hp.2.2
  · obtain ⟨hpM1, hpM2⟩ := mem_M_of_zpowers S (S.mul_self_of_isConj hp.1)
      ((T.isConj_w_iff ht₀ hS).mp hp.2.1).1 hp.2.2
    have h1 := (T.mem_D_iff hS hpM1).mp hp.1
    have h2 := (T.isConj_w_iff_th ht₀ hS hpM2).mp hp.2.1
    simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
    refine ⟨⟨h1, h2⟩, ?_⟩
    have h72 := qts_nz.1 _ h1 _ h2
    rw [← T.th_mul _ hpM1 _ hpM2] at h72 ⊢
    rw [← T.th_z]
    exact (T.mem_zpowers_iff_zpowL (S.M.mul_mem hpM1 hpM2) (z_mem_M S) h72).mp hp.2.2
  · simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at hq
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    refine ⟨(T.mem_D_iff hS hx).mpr h1, (T.isConj_w_iff_th ht₀ hS hv).mpr h2, ?_⟩
    have h72 := qts_nz.1 _ h1 _ h2
    rw [← T.th_mul _ hx _ hv] at h72 h3
    rw [← T.th_z] at h3
    exact (T.mem_zpowers_iff_zpowL (S.M.mul_mem hx hv) (z_mem_M S) h72).mpr h3
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at hq
    exact ⟨mem_dl_codes hq.1.1, (mem_il.mp (mem_wl.mp hq.1.2).1).1⟩

omit [Finite G] in
include T in
theorem ncard_A {t₀' : G} (htc : T.th t₀' = t0c) (ht₀M : t₀' ∈ S.M) :
    {c : G | c ∈ S.M ∧ c * t₀' = t₀' * c}.ncard = 2304 := by
  classical
  have hinj : Set.InjOn T.th {c : G | c ∈ S.M ∧ c * t₀' = t₀' * c} :=
    fun x hx y hy h => T.th_injOn x hx.1 y hy.1 h
  rw [← hinj.ncard_image, ← qts_cent, ← Set.ncard_coe_finset]
  congr 1
  ext c
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_filter, commB_iff,
    t0c] at *
  constructor
  · rintro ⟨x, ⟨hxM, hxt⟩, rfl⟩
    refine ⟨T.th_mem x hxM, ?_⟩
    rw [← htc]
    exact ((T.th_comm ht₀M hxM).mp hxt.symm)
  · rintro ⟨hc, hct⟩
    obtain ⟨x, hxM, rfl⟩ := T.th_surj c hc
    refine ⟨x, ⟨hxM, ?_⟩, rfl⟩
    rw [← htc] at hct
    exact ((T.th_comm ht₀M hxM).mpr hct).symm

include T in
theorem natCard_centralizer_w (hS : S.SixHyp) {t₀ : G} (ht₀ : t₀ ∈ S.DSet)
    (htc : T.th t₀ = t0c) : Nat.card (centralizer ({S.z * t₀} : Set G)) = 4608 := by
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have htt := S.mul_self_of_isConj (t0_isConj ht₀)
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht₀
  obtain ⟨g, hg1, hg2⟩ := S.exists_swap_J hS ht₀ hh
  set A := {c : G | c ∈ S.M ∧ c * t₀ = t₀ * c} with hA
  have hgw : g * (S.z * t₀) = S.z * t₀ * g := by
    calc g * (S.z * t₀) = (g * S.z * g⁻¹) * (g * t₀ * g⁻¹) * g := by group
      _ = S.z * t₀ * g := by rw [hg1, hg2, hzt]
  have hg1' : g⁻¹ * t₀ * g = S.z := by rw [← hg1]; group
  have hg2' : g⁻¹ * S.z * g = t₀ := by rw [← hg2]; group
  have hset : (centralizer ({S.z * t₀} : Set G) : Set G) = A ∪ (fun a => a * g) '' A := by
    ext c
    simp only [SetLike.mem_coe, mem_centralizer_singleton_iff, Set.mem_union, Set.mem_image]
    constructor
    · intro hc
      rcases T.eq_or_eq_of_commute_zt hS ht₀ hc with h1 | h1
      · left
        have hcM : c ∈ S.M := S.mem_M_iff.mpr (by
          calc c * S.z = c * S.z * c⁻¹ * c := by group
            _ = S.z * c := by rw [h1])
        refine ⟨hcM, ?_⟩
        have hcz := S.mem_M_iff.mp hcM
        have : S.z * (c * t₀) = S.z * (t₀ * c) := by
          calc S.z * (c * t₀) = c * (S.z * t₀) := by rw [← mul_assoc, ← hcz, mul_assoc]
            _ = S.z * t₀ * c := hc
            _ = S.z * (t₀ * c) := by group
        exact mul_left_cancel this
      · right
        have hct : c * t₀ * c⁻¹ = S.z := by
          have hcw : c * (S.z * t₀) * c⁻¹ = S.z * t₀ := by rw [hc]; group
          calc c * t₀ * c⁻¹ = (c * S.z * c⁻¹)⁻¹ * (c * (S.z * t₀) * c⁻¹) := by group
            _ = t₀⁻¹ * (S.z * t₀) := by rw [h1, hcw]
            _ = S.z := by
                rw [inv_eq_of_mul_eq_one_right htt, ← mul_assoc, hzt, mul_assoc, htt, mul_one]
        refine ⟨c * g⁻¹, ⟨S.mem_M_iff.mpr ?_, ?_⟩, by group⟩
        · calc c * g⁻¹ * S.z = c * (g⁻¹ * S.z * g) * g⁻¹ := by group
            _ = c * t₀ * c⁻¹ * (c * g⁻¹) := by rw [hg2']; group
            _ = S.z * (c * g⁻¹) := by rw [hct]
        · calc c * g⁻¹ * t₀ = c * (g⁻¹ * t₀ * g) * g⁻¹ := by group
            _ = c * S.z * c⁻¹ * (c * g⁻¹) := by rw [hg1']; group
            _ = t₀ * (c * g⁻¹) := by rw [h1]
    · rintro (⟨hcM, hct⟩ | ⟨a, ⟨haM, hat⟩, rfl⟩)
      · calc c * (S.z * t₀) = c * S.z * t₀ := by group
          _ = S.z * (c * t₀) := by rw [S.mem_M_iff.mp hcM, mul_assoc]
          _ = S.z * t₀ * c := by rw [hct]; group
      · have haw : a * (S.z * t₀) = S.z * t₀ * a := by
          calc a * (S.z * t₀) = a * S.z * t₀ := by group
            _ = S.z * (a * t₀) := by rw [S.mem_M_iff.mp haM, mul_assoc]
            _ = S.z * t₀ * a := by rw [hat]; group
        calc a * g * (S.z * t₀) = a * (S.z * t₀) * g := by rw [mul_assoc, hgw, ← mul_assoc]
          _ = S.z * t₀ * (a * g) := by rw [haw, mul_assoc]
  have hdisj : Disjoint A ((fun a => a * g) '' A) := by
    rw [Set.disjoint_left]
    rintro c ⟨hcM, -⟩ ⟨a, ⟨haM, -⟩, rfl⟩
    have hgM : g ∈ S.M := by
      have := S.M.mul_mem (S.M.inv_mem haM) hcM
      rwa [show a⁻¹ * (a * g) = g by group] at this
    apply t0_ne ht₀
    rw [← hg1, S.conj_z_of_mem_M hgM]
  have hcard : Nat.card (centralizer ({S.z * t₀} : Set G)) =
      ((centralizer ({S.z * t₀} : Set G) : Set G)).ncard := Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_union_eq hdisj,
    Set.InjOn.ncard_image (fun x _ y _ h => mul_right_cancel h), T.ncard_A htc ht₀M]

end Chart

end CFSG.LargeExtraspecial.AS35QTS
