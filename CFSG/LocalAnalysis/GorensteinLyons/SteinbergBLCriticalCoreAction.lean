module

public import CFSG.RankThree.GroupTheory.SteinbergBYSymplecticCritical
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMCyclicTwoExtension

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace CriticalCoreAction

variable {G : Type*} [Group G]

theorem zpow_eq_principal {y : G} {m : ℕ} (hy : orderOf y = 2 ^ (m + 3)) {j : ℤ}
    (h1 : y ^ (j * j) = y) (h2 : y ^ (j * 2 ^ (m + 1)) = y ^ ((2 : ℤ) ^ (m + 1)))
    (h3 : y ^ j ≠ y) : y ^ j = y ^ ((1 + 2 ^ (m + 2) : ℕ) : ℤ) := by
  have hdvd : ∀ a b : ℤ, y ^ a = y ^ b ↔ (2 : ℤ) ^ (m + 3) ∣ b - a := by
    intro a b
    rw [zpow_eq_zpow_iff_modEq, hy, Int.modEq_iff_dvd]
    push_cast
    rfl
  have h1' : (2 : ℤ) ^ (m + 3) ∣ 1 - j * j := (hdvd (j * j) 1).mp (by rw [zpow_one]; exact h1)
  have h2' : (2 : ℤ) ^ (m + 3) ∣ 2 ^ (m + 1) - j * 2 ^ (m + 1) := (hdvd _ _).mp h2
  have h3' : ¬ (2 : ℤ) ^ (m + 3) ∣ 1 - j := fun h => h3 (by
    have := (hdvd j 1).mpr h
    rwa [zpow_one] at this)
  obtain ⟨c, hc⟩ : (4 : ℤ) ∣ 1 - j := by
    have h : (2 : ℤ) ^ (m + 1) * 4 ∣ 2 ^ (m + 1) * (1 - j) := by
      have e1 : (2 : ℤ) ^ (m + 1) * 4 = 2 ^ (m + 3) := by ring
      have e2 : (2 : ℤ) ^ (m + 1) * (1 - j) = 2 ^ (m + 1) - j * 2 ^ (m + 1) := by ring
      rw [e1, e2]
      exact h2'
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp h
  have hj : j = 1 - 4 * c := by linarith
  obtain ⟨b, hb⟩ : (2 : ℤ) ^ m ∣ c := by
    have h : (2 : ℤ) ^ m * 8 ∣ (c * (1 - 2 * c)) * 8 := by
      have e1 : (2 : ℤ) ^ m * 8 = 2 ^ (m + 3) := by ring
      have e2 : c * (1 - 2 * c) * 8 = 1 - j * j := by
        rw [hj]
        ring
      rw [e1, e2]
      exact h1'
    have h' := (mul_dvd_mul_iff_right (by norm_num : (8 : ℤ) ≠ 0)).mp h
    exact (IsCoprime.pow_left ⟨c, 1, by ring⟩ :
      IsCoprime ((2 : ℤ) ^ m) (1 - 2 * c)).dvd_of_dvd_mul_right h'
  obtain ⟨d, hd⟩ : ∃ d, b = 2 * d + 1 := by
    rcases Int.emod_two_eq_zero_or_one b with h | h
    · exfalso
      obtain ⟨q, hq⟩ : ∃ q, b = 2 * q := ⟨b / 2, by omega⟩
      exact h3' ⟨q, by rw [hc, hb, hq]; ring⟩
    · exact ⟨b / 2, by omega⟩
  apply (hdvd _ _).mpr
  push_cast
  exact ⟨d + 1, by rw [hj, hb, hd]; ring⟩

theorem principal_fix_of_pow_four {y : G} {m : ℕ} (hy : orderOf y = 2 ^ (m + 3)) (a : ℤ)
    (ha : (y ^ a) ^ 4 = 1) : (y ^ (1 + 2 ^ (m + 2))) ^ a = y ^ a := by
  have hdvd : (2 : ℤ) ^ (m + 3) ∣ a * 4 := by
    rw [← zpow_natCast, ← zpow_mul] at ha
    have h := orderOf_dvd_iff_zpow_eq_one.mpr ha
    rw [hy] at h
    exact_mod_cast h
  obtain ⟨b, hb⟩ : (2 : ℤ) ^ (m + 1) ∣ a := by
    have h : (2 : ℤ) ^ (m + 1) * 4 ∣ a * 4 := by
      rw [show (2 : ℤ) ^ (m + 1) * 4 = 2 ^ (m + 3) by ring]
      exact hdvd
    exact (mul_dvd_mul_iff_right (by norm_num : (4 : ℤ) ≠ 0)).mp h
  rw [← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_modEq, hy, Int.modEq_iff_dvd]
  push_cast
  exact ⟨-(2 ^ m * b), by rw [hb]; ring⟩

end CriticalCoreAction

open CriticalCoreAction Subgroup CFSG.SectionRank.Ccomm CFSG.RankThree.GroupTheory.SteinbergBY

variable {P : Type*} [Group P]

theorem symplectic_critical_order_four_center_detects_core_action [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    {D : Subgroup P} (hD : ThompsonCritical D) {k : ℕ} (hk : 3 ≤ k)
    (hYk : Nat.card ((center D).map D.subtype) = 2 ^ k) {T : Subgroup P}
    (hTY : T ≤ (center D).map D.subtype) (hT4 : Nat.card T = 4) :
    ∃ L : Subgroup P, (L : Set P) = {d | d ∈ D ∧ d ^ 4 = 1} ∧ L.Characteristic ∧
      centralizer ((center D).map D.subtype : Set P) = D ∧ centralizer (T : Set P) = D ∧
      centralizer (L : Set P) = (center D).map D.subtype ∧ D.index ≤ 2 ∧
      Nat.card (MulAut T) = 2 ∧ (IsCyclic D → D = (center D).map D.subtype ∧ L = T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  obtain ⟨-, hcp⟩ := symplectic_critical_subgroup_central_product hP hsymp
  obtain ⟨-, hcyc, hZchar, z, hzZ, hz, -, -, -, hcZ, E, R, hEZ, hR, hER, -, hRZ, -, hRn,
    hcases, hφex, -⟩ := hcp D hD
  set Y := (center D).map D.subtype with hYdef
  obtain ⟨φ, hφ, hφker⟩ := hφex
  have hYn : Y.Normal := normal_of_characteristic Y
  have hYD : Y ≤ D := map_center_le D
  have hDcY : D ≤ centralizer (Y : Set P) := le_centralizer_iff.mp (map_center_le_centralizer D)
  have hEE : E ≤ D := by
    rw [← hEZ]
    exact le_sup_left
  have hYR : Y ≤ R := by
    rw [hR]
    exact le_centralizer_iff.mp (hEE.trans hDcY)
  have hRc : ∀ r ∈ R, ∀ x ∈ E, x * r = r * x := fun r hr x hx =>
    mem_centralizer_iff.mp (hR ▸ hr : r ∈ centralizer (E : Set P)) x hx
  obtain ⟨⟨y, hyY⟩, hy⟩ := @IsCyclic.exists_generator _ _ hcyc
  have hoy : orderOf y = 2 ^ (m + 3) := by
    rw [← Subgroup.orderOf_mk y hyY, orderOf_eq_card_of_forall_mem_zpowers hy, hYk]
  have hYa : ∀ x ∈ Y, ∃ n : ℤ, y ^ n = x := fun x hx => by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hy ⟨x, hx⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hcent_of : ∀ g : P, g * y * g⁻¹ = y → g ∈ centralizer (Y : Set P) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := hYa x hx
    have hc : y * g = g * y := by
      calc y * g = g * y * g⁻¹ * g := by rw [hg]
        _ = g * y := by group
    exact (Commute.zpow_left hc n).eq
  have hT4' : ∀ t ∈ T, t ^ 4 = 1 := fun t ht => by
    have h := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
    rw [hT4] at h
    simpa using congrArg Subtype.val h
  have hTmem : ∀ x ∈ Y, x ^ 4 = 1 → x ∈ T := fun x hx hx4 =>
    mem_of_pow_eq_one_of_isCyclic hcyc hTY (by norm_num) hT4 hx hx4
  have hEcY : ∀ e ∈ E, (∀ x ∈ E, e * x = x * e) → e ∈ Y := by
    intro e he hec
    rcases hcases with ⟨-, hE0, -⟩ | ⟨_, -, -, -, -, -, -, -, -, -, hEcen, -⟩
    · rw [hE0, mem_bot] at he
      rw [he]
      exact one_mem _
    · have hmem : e ∈ (center E).map E.subtype :=
        ⟨⟨e, he⟩, mem_center_iff.mpr fun x => Subtype.ext (hec x x.2).symm, rfl⟩
      rw [hEcen] at hmem
      exact zpowers_le.mpr hzZ hmem
  set L := E ⊔ T with hLdef
  have hLset : (L : Set P) = {d | d ∈ D ∧ d ^ 4 = 1} := by
    rcases hcases with ⟨-, hE0, -⟩ | ⟨_, -, -, -, -, hEx, -, -, -, hEZi, hEcen, -⟩
    · have hDY : D = Y := by rw [← hEZ, hE0, bot_sup_eq]
      rw [hLdef, hE0, bot_sup_eq]
      ext x
      constructor
      · intro hx
        exact ⟨hYD (hTY hx), hT4' x hx⟩
      · rintro ⟨hxD, hx4⟩
        exact hTmem x (hDY ▸ hxD) hx4
    · exact ((extraspecial_cyclic_product_characteristic_exponent_four_layer
        (hP.to_subgroup D) rfl hcyc (by omega) hYk hzZ hz hEE hEx hEZ.symm hEZi hEcen hTY
        hT4).1).symm
  have hmem : ∀ x : P, x ∈ L ↔ x ∈ D ∧ x ^ 4 = 1 := fun x => Set.ext_iff.mp hLset x
  have hLD : L ≤ D := fun x hx => ((hmem x).mp hx).1
  have hLchar : L.Characteristic := by
    refine ⟨fun α => ?_⟩
    ext x
    have h1 : α x ∈ D ↔ x ∈ D := SetLike.ext_iff.mp (hD.1.fixed α) x
    change α x ∈ L ↔ x ∈ L
    rw [hmem, hmem, ← map_pow, MulEquiv.map_eq_one_iff, h1]
  have hYL : Y ≤ centralizer (L : Set P) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro l hl
    exact (mem_centralizer_iff.mp (hDcY (hLD hl)) x hx).symm
  have hCT : centralizer (T : Set P) ≤ D := by
    intro g hgT
    by_contra hgD
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP) g
    have hex : ∃ i, g ^ 2 ^ (i + 1) ∈ D :=
      ⟨n, by rw [pow_succ, pow_mul, ← hn, pow_orderOf_eq_one, one_pow]; exact one_mem D⟩
    obtain ⟨g₁, hg₁T, hg₁D, hg₁2⟩ :
        ∃ g₁ ∈ centralizer (T : Set P), g₁ ∉ D ∧ g₁ ^ 2 ∈ D := by
      refine ⟨g ^ 2 ^ Nat.find hex, pow_mem hgT _, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
        · rw [h0, pow_zero, pow_one]
          exact hgD
        · have h := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
          rwa [Nat.sub_add_cancel hpos] at h
      · rw [← pow_mul, ← pow_succ]
        exact Nat.find_spec hex
    obtain ⟨j, hj⟩ := hYa _ (hYn.conj_mem y hyY g₁)
    have hconj : ∀ i : ℤ, g₁ * y ^ i * g₁⁻¹ = y ^ (j * i) := fun i => by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hj, ← zpow_mul]
    have h1 : y ^ (j * j) = y := by
      have hc : y * g₁ ^ 2 = g₁ ^ 2 * y := mem_centralizer_iff.mp (hDcY hg₁2) y hyY
      rw [← hconj j, hj]
      calc g₁ * (g₁ * y * g₁⁻¹) * g₁⁻¹ = g₁ ^ 2 * y * (g₁ ^ 2)⁻¹ := by rw [pow_two]; group
        _ = y := by rw [← hc, mul_inv_cancel_right]
    have ht₀ : y ^ ((2 : ℤ) ^ (m + 1)) ∈ T := by
      apply hTmem _ (zpow_mem hyY _)
      rw [← zpow_natCast, ← zpow_mul,
        show (2 : ℤ) ^ (m + 1) * ((4 : ℕ) : ℤ) = ((2 ^ (m + 3) : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, ← hoy, pow_orderOf_eq_one]
    have h2 : y ^ (j * 2 ^ (m + 1)) = y ^ ((2 : ℤ) ^ (m + 1)) := by
      rw [← hconj]
      have hc := mem_centralizer_iff.mp hg₁T _ ht₀
      rw [← hc, mul_inv_cancel_right]
    have h3 : y ^ j ≠ y := by
      intro h
      apply hg₁D
      rw [← hcZ]
      exact hcent_of g₁ (by rw [← hj, h])
    have hσ := zpow_eq_principal hoy h1 h2 h3
    rw [zpow_natCast] at hσ
    have hg₁σ : g₁ * y * g₁⁻¹ = y ^ (1 + 2 ^ (m + 2)) := by rw [← hj, hσ]
    have := hRn
    obtain ⟨e, he, r, hr, hgr⟩ := mem_sup_of_normal_right.mp
      (show g₁ ∈ E ⊔ R by rw [hER]; exact mem_top g₁)
    have hecY : ∀ x ∈ Y, e * x = x * e := fun x hx =>
      (mem_centralizer_iff.mp (hDcY (hEE he)) x hx).symm
    have hrσ : r * y * r⁻¹ = y ^ (1 + 2 ^ (m + 2)) := by
      have hr' : r = e⁻¹ * g₁ := by rw [← hgr]; group
      rw [hr', mul_inv_rev, inv_inv]
      calc e⁻¹ * g₁ * y * (g₁⁻¹ * e) = e⁻¹ * (g₁ * y * g₁⁻¹) * e := by group
        _ = e⁻¹ * y ^ (1 + 2 ^ (m + 2)) * e := by rw [hg₁σ]
        _ = y ^ (1 + 2 ^ (m + 2)) := by
          rw [mul_assoc, ← hecY _ (pow_mem hyY _), inv_mul_cancel_left]
    have hz1 : y ^ 2 ^ (m + 2) ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [hoy]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hrY : r ∉ Y := by
      intro hrY'
      have hc : r * y * r⁻¹ = y := by
        obtain ⟨a, rfl⟩ := hYa r hrY'
        rw [((Commute.refl y).zpow_left a).eq, mul_inv_cancel_right]
      rw [hrσ, pow_add, pow_one] at hc
      exact hz1 (mul_left_cancel (by rw [hc, mul_one] : y * y ^ 2 ^ (m + 2) = y * 1))
    have hrD : r ∉ D := by
      intro hrD'
      have hc : r * y * r⁻¹ = y := by
        rw [mem_centralizer_iff.mp (hDcY hrD') y hyY |>.symm, mul_inv_cancel_right]
      rw [hrσ, pow_add, pow_one] at hc
      exact hz1 (mul_left_cancel (by rw [hc, mul_one] : y * y ^ 2 ^ (m + 2) = y * 1))
    have hjj : y ^ ((1 + 2 ^ (m + 2)) * (1 + 2 ^ (m + 2))) = y := by
      have e1 : (1 + 2 ^ (m + 2)) * (1 + 2 ^ (m + 2)) = 1 + 2 ^ (m + 3) * (1 + 2 ^ (m + 1)) := by
        ring
      rw [e1, pow_add, pow_one, pow_mul, ← hoy, pow_orderOf_eq_one, one_pow, mul_one]
    have hr2c : r ^ 2 ∈ centralizer (Y : Set P) := by
      apply hcent_of
      calc r ^ 2 * y * (r ^ 2)⁻¹ = r * (r * y * r⁻¹) * r⁻¹ := by rw [pow_two]; group
        _ = r * y ^ (1 + 2 ^ (m + 2)) * r⁻¹ := by rw [hrσ]
        _ = (r * y * r⁻¹) ^ (1 + 2 ^ (m + 2)) := by rw [conj_pow]
        _ = y := by rw [hrσ, ← pow_mul, hjj]
    have hrT : ∀ t ∈ T, r * t * r⁻¹ = t := by
      intro t ht
      obtain ⟨a, rfl⟩ := hYa t (hTY ht)
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hrσ]
      exact principal_fix_of_pow_four hoy a (hT4' _ ht)
    have hrσ' : r⁻¹ * y * r = y ^ (1 + 2 ^ (m + 2)) := by
      have hc : y * r ^ 2 = r ^ 2 * y := mem_centralizer_iff.mp hr2c y hyY
      rw [← hrσ]
      calc r⁻¹ * y * r = r⁻¹ * (r ^ 2 * y * (r ^ 2)⁻¹) * r := by
            rw [← hc, mul_inv_cancel_right]
        _ = r * y * r⁻¹ := by rw [pow_two]; group
    have hφα : ∀ (α : P ≃* P) (p : P), φ (α p) = φ p := by
      intro α p
      obtain ⟨n, hn⟩ := @MonoidHom.map_cyclic _ _ hcyc (φ p).toMonoidHom
      have hpow : ∀ w ∈ Y, p * w * p⁻¹ = w ^ n := fun w hw =>
        (hφ p ⟨w, hw⟩).symm.trans (congrArg Subtype.val (hn ⟨w, hw⟩))
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hφ, hφ, hpow x x.2]
      obtain ⟨x', hx'Y, hx'⟩ : ∃ x' ∈ Y, α x' = (x : P) :=
        ⟨α.symm x, (SetLike.ext_iff.mp (hZchar.fixed α.symm) (x : P)).mpr x.2,
          α.apply_symm_apply _⟩
      rw [← hx', ← map_inv, ← map_mul, ← map_mul, hpow x' hx'Y, map_zpow]
    set F := (zpowers (φ r)).comap φ with hF
    have hFchar : F.Characteristic := by
      refine ⟨fun α => ?_⟩
      ext p
      change φ (α p) ∈ zpowers (φ r) ↔ φ p ∈ zpowers (φ r)
      rw [hφα]
    set U₀ := F ⊓ centralizer (L : Set P) with hU₀
    have hU₀char : U₀.Characteristic := by
      have := hFchar
      have := hLchar
      show (F ⊓ centralizer (L : Set P)).Characteristic
      infer_instance
    have hYU : Y ≤ U₀ := by
      intro x hx
      refine ⟨?_, hYL hx⟩
      change φ x ∈ zpowers (φ r)
      rw [show φ x = 1 from MonoidHom.mem_ker.mp (by rw [hφker]; exact hYD hx)]
      exact one_mem _
    have hrL : r ∈ centralizer (L : Set P) := by
      have hle : E ⊔ T ≤ centralizer ({r} : Set P) := by
        refine sup_le (fun x hx => ?_) (fun t ht => ?_)
        · rw [mem_centralizer_singleton_iff]
          exact hRc r hr x hx
        · rw [mem_centralizer_singleton_iff]
          calc t * r = r * t * r⁻¹ * r := by rw [hrT t ht]
            _ = r * t := by group
      rw [mem_centralizer_iff]
      intro l hl
      exact mem_centralizer_singleton_iff.mp (hle hl)
    have hrU : r ∈ U₀ := ⟨mem_zpowers (φ r), hrL⟩
    have hφr : orderOf (φ r) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        exact MonoidHom.mem_ker.mp (by rw [hφker, ← hcZ]; exact hr2c)
      · intro h1
        exact hrD (by rw [← hφker]; exact MonoidHom.mem_ker.mpr h1)
    have hU₀sub : ∀ u ∈ U₀, u ∈ Y ∨ u * r ∈ Y := by
      rintro u ⟨huF, huL⟩
      obtain ⟨e', he', r', hr', rfl⟩ := mem_sup_of_normal_right.mp
        (show u ∈ E ⊔ R by rw [hER]; exact mem_top u)
      have he'c : ∀ x ∈ E, e' * x = x * e' := by
        intro x hx
        have h1 : e' * r' * x = x * (e' * r') :=
          (mem_centralizer_iff.mp huL x (le_sup_left (b := T) hx)).symm
        have h2 : r' * x = x * r' := (hRc r' hr' x hx).symm
        have h3 : e' * x * r' = x * e' * r' := by
          calc e' * x * r' = e' * (r' * x) := by rw [mul_assoc, h2]
            _ = x * e' * r' := by rw [← mul_assoc, h1, mul_assoc]
        exact mul_right_cancel h3
      have huR : e' * r' ∈ R := R.mul_mem (hYR (hEcY e' he' he'c)) hr'
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hφr huF with h1 | h1
      · left
        have hD' : e' * r' ∈ D := by
          rw [← hφker]
          exact MonoidHom.mem_ker.mpr h1
        exact hRZ ▸ mem_inf.mpr ⟨huR, hcZ.symm ▸ hD'⟩
      · right
        have hD' : e' * r' * r ∈ D := by
          rw [← hφker, MonoidHom.mem_ker, map_mul, h1, ← pow_two, ← hφr, pow_orderOf_eq_one]
        exact hRZ ▸ mem_inf.mpr ⟨R.mul_mem huR hr, hcZ.symm ▸ hD'⟩
    have hyU : y ∈ U₀ := hYU hyY
    have hzpow : ∀ u : U₀, u ∈ zpowers (⟨y, hyU⟩ : U₀) ↔ (u : P) ∈ Y := by
      intro u
      constructor
      · intro hu
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hu
        exact zpow_mem hyY n
      · intro hu
        obtain ⟨n, hn⟩ := hYa _ hu
        exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    have hnorm : (zpowers (⟨y, hyU⟩ : U₀)).Normal := by
      refine ⟨fun u hu g => ?_⟩
      rw [hzpow] at hu ⊢
      exact hYn.conj_mem _ hu _
    have hidx : (zpowers (⟨y, hyU⟩ : U₀)).index = 2 := by
      rw [index_eq_two_iff]
      refine ⟨⟨r, hrU⟩, fun b => ?_⟩
      rw [hzpow, hzpow]
      by_cases hb : (b : P) ∈ Y
      · refine Or.inr ⟨hb, fun hbr => hrY ?_⟩
        have h := Y.mul_mem (Y.inv_mem hb) hbr
        rwa [Subgroup.coe_mul, inv_mul_cancel_left] at h
      · exact Or.inl ⟨(hU₀sub b b.2).resolve_left hb, hb⟩
    obtain ⟨x, -, -, -, -, -, -, hVchar, hVel, hV4⟩ :=
      principal_cyclic_two_extension_characteristic_four_group (hP.to_subgroup U₀)
        (k := m + 3) (by omega) (y := ⟨y, hyU⟩) (by rw [Subgroup.orderOf_mk]; exact hoy) hnorm
        hidx ⟨⟨r, hrU⟩, fun h => hrY ((hzpow _).mp h),
          Subtype.ext (by rw [show m + 3 - 1 = m + 2 by omega]; exact hrσ')⟩
    set V := closure ({x, (⟨y, hyU⟩ : U₀) ^ 2 ^ (m + 3 - 1)} : Set U₀) with hVdef
    have hV'char : (V.map U₀.subtype).Characteristic := characteristic_map_subtype hU₀char hVchar
    have hV'comm : IsMulCommutative (V.map U₀.subtype) := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb]
      exact congrArg (fun w : V => ((w : U₀) : P))
        (hVel.toIsMulCommutative.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    have hV'cyc := hsymp _ hV'char hV'comm
    have hcard : Nat.card (V.map U₀.subtype) = 4 := by
      rw [card_map_of_injective U₀.subtype_injective, hV4]
    have hexp : Monoid.exponent (V.map U₀.subtype) ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro a
      obtain ⟨a', ha', ha⟩ := a.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← ha, OneMemClass.coe_one]
      exact congrArg (fun w : V => ((w : U₀) : P))
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hVel.exponent_dvd_p ⟨a', ha'⟩)
    rw [@IsCyclic.exponent_eq_card _ _ hV'cyc, hcard] at hexp
    norm_num at hexp
  have hCTeq : centralizer (T : Set P) = D :=
    le_antisymm hCT (hDcY.trans (centralizer_le (show (T : Set P) ⊆ Y from hTY)))
  have hCL : centralizer (L : Set P) = Y := by
    refine le_antisymm (fun x hx => ?_) hYL
    have hxD : x ∈ D :=
      hCT (centralizer_le (SetLike.coe_subset_coe.mpr (le_sup_right : T ≤ E ⊔ T)) hx)
    have := hYn
    obtain ⟨e', he', y', hy', rfl⟩ := mem_sup_of_normal_right.mp
      (show x ∈ E ⊔ Y by rw [hEZ]; exact hxD)
    have he'c : ∀ x ∈ E, e' * x = x * e' := by
      intro x' hx'
      have h1 : e' * y' * x' = x' * (e' * y') :=
        (mem_centralizer_iff.mp hx x' (le_sup_left (b := T) hx')).symm
      have h2 : y' * x' = x' * y' := (mem_centralizer_iff.mp (hDcY (hEE hx')) y' hy')
      have h3 : e' * x' * y' = x' * e' * y' := by
        calc e' * x' * y' = e' * (y' * x') := by rw [mul_assoc, h2]
          _ = x' * e' * y' := by rw [← mul_assoc, h1, mul_assoc]
      exact mul_right_cancel h3
    exact Y.mul_mem (hEcY e' he' he'c) hy'
  have hTcyc : IsCyclic T := by
    have : IsCyclic Y := hcyc
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hTY).toMonoidHom
      (subgroupOfEquivOfLe hTY).surjective
  have hAut : Nat.card (MulAut T) = 2 := by
    rw [@IsCyclic.card_mulAut T _ _ hTcyc, hT4]
    decide
  have hTn : T.Normal := ⟨fun t ht g => hTmem _ (hYn.conj_mem t (hTY ht) g)
    (by rw [conj_pow, hT4' t ht, mul_one, mul_inv_cancel])⟩
  have hidx : D.index ≤ 2 := by
    have : Finite (MulAut T) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
    have hker : (MulAut.conjNormal (H := T)).ker = D := by rw [ker_conjNormal, hCTeq]
    rw [← hker, index_ker, ← hAut]
    exact card_le_card_group _
  have hcycD : IsCyclic D → D = Y ∧ L = T := by
    intro hDc
    have hDY : D = Y := by
      refine le_antisymm (fun d hd => ?_) hYD
      exact ⟨⟨d, hd⟩, mem_center_iff.mpr fun g =>
        (@IsCyclic.isMulCommutative D _ hDc).is_comm.comm g ⟨d, hd⟩, rfl⟩
    refine ⟨hDY, SetLike.ext' ?_⟩
    rw [hLset]
    ext x
    constructor
    · rintro ⟨hxD, hx4⟩
      exact hTmem x (hDY ▸ hxD) hx4
    · intro hx
      exact ⟨hYD (hTY hx), hT4' x hx⟩
  exact ⟨L, hLset, hLchar, hcZ, hCTeq, hCL, hidx, hAut, hcycD⟩

end CFSG.LocalAnalysis.GorensteinLyons
