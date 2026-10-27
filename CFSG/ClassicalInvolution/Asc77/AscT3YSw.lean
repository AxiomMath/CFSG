module

public import CFSG.ClassicalInvolution.Asc77.AscT3YCyc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.y_W_le_X (d : Std20 p f K K' J S R R' W V z t) :
    W ≤ sec20X (CoreAssembly.conjClass K) z K K' := by
  have hJW := d.late_JW
  have hJX : J ⊓ W ≤ sec20X (CoreAssembly.conjClass K) z K K' :=
    le_trans (le_iSup₂ (f := fun (U : Subgroup G) (_ : U ∈ {U : Subgroup G |
      U ∈ USet (CoreAssembly.conjClass K) ∧ U ≤ Subgroup.centralizer ({z} : Set G)}) => U)
      (J ⊓ W) ⟨hJW, (inf_le_right.trans d.hWS).trans d.hSz⟩)
      (le_trans le_sup_left le_sup_left)
  calc W = (W ⊓ K) ⊔ (W ⊓ J) := d.late_hW
    _ ≤ sec20X (CoreAssembly.conjClass K) z K K' :=
      sup_le (inf_le_right.trans le_sec20X_left) (by rw [inf_comm]; exact hJX)

theorem Std20.y_not_mem_K' (d : Std20 p f K K' J S R R' W V z t) {e : G} (heKW : e ∈ K ⊓ W)
    (he2 : e * e = z) : e ∉ K' := by
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  intro heK'
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers e) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS heKW.2))
  have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm hA2
    (Subgroup.zpowers_le.mpr heKW.1) (Subgroup.zpowers_le.mpr heK')
  rw [Nat.card_zpowers] at hcard
  have hpos : 0 < orderOf e := by
    rw [← Nat.card_zpowers]
    exact Nat.card_pos
  have hsq : e * e = 1 := by
    rcases (by omega : orderOf e = 1 ∨ orderOf e = 2) with h | h
    · rw [orderOf_eq_one_iff.mp h, one_mul]
    · rw [← pow_two, ← h, pow_orderOf_eq_one]
  exact hz1 (he2.symm.trans hsq)

theorem Std20.y_CSW_le_W (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z) {c : G}
    (hcS : c ∈ (S : Subgroup G)) (hcW : ∀ w ∈ W, c * w = w * c) : c ∈ W := by
  have hcK : conjSub c K = K := by
    rcases d.y_cases hcS with h | h
    · exact mem_normalizer_iff_conjSub_eq.mp h
    · exfalso
      obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
      have heK' : e ∈ K' := by
        have h1 : c * e * c⁻¹ ∈ conjSub c K := conj_mem_conjSub heKW.1
        have h2 : c * e * c⁻¹ = e := by
          rw [hcW e heKW.2]
          group
        rw [h2, h] at h1
        exact h1
      exact d.y_not_mem_K' heKW he2 heK'
  set X : Subgroup G := Subgroup.zpowers c with hX
  have hXS : X ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hcS
  have hX2 : IsPGroup 2 ↥X := S.isPGroup'.to_le hXS
  have hXN : X ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hcK)
  have hXt : ∀ x ∈ X, x * t = t * x := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute c t from hcW t d.late_t_mem_W) m)).eq
  have hXK : ∀ x ∈ X, conjSub x K = K := fun x hx => mem_normalizer_iff_conjSub_eq.mp (hXN hx)
  obtain ⟨-, h2⟩ := d.late_98 d.late_JW d.late_hW hX2 hXS hXt hXK
  obtain ⟨A, hA1, -, -, hA3, -⟩ := h2 (by
    intro x hx w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute c w from hcW w hw.1) m)).eq)
  have hle : ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ X ≤ (S : Subgroup G) :=
    sup_le (sup_le (inf_le_left.trans d.hWS) (inf_le_left.trans d.hWS)) hXS
  have hAS : A ≤ (S : Subgroup G) := le_sup_right.trans (hA1 ▸ hle)
  have hAz : A ≤ Subgroup.zpowers z := by
    intro a ha
    have h1 : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := ⟨hAS ha, (hA3 ha).2⟩
    rw [c7] at h1
    exact h1
  have hWle : ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ Subgroup.zpowers z ≤ W :=
    sup_le (sup_le inf_le_left inf_le_left) (Subgroup.zpowers_le.mpr d.late_z_mem_W)
  have hcX : c ∈ X := Subgroup.mem_zpowers c
  have h3 : c ∈ ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ X := Subgroup.mem_sup_right hcX
  rw [hA1] at h3
  exact hWle (sup_le_sup_left hAz _ h3)

theorem y_zpow_of_sq {H : Type*} [Group H] {a : H} (ha : a * a = 1) (m : ℤ) :
    (Even m → a ^ m = 1) ∧ (Odd m → a ^ m = a) := by
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  constructor
  · rintro ⟨c, rfl⟩
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · rintro ⟨c, rfl⟩
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem Std20.y_scalar (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) {n : G}
    (hnS : n ∈ (S : Subgroup G)) (hnK : conjSub n K = K) (hnt : n * t * n⁻¹ = t) :
    ∃ l : ℤ, ∀ w ∈ W, n * w * n⁻¹ = w ^ l := by
  obtain ⟨v₀, hv₀, hv₀o, hv₀t, huz, hWgen, huv, hdis⟩ := d.v_W_gen hu huo
  have hnt' : n * t = t * n := by
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [hnt]
  have hnJ : conjSub n J = J := by
    set X : Subgroup G := Subgroup.zpowers n with hX
    have hXS : X ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hnS
    have hX2 : IsPGroup 2 ↥X := S.isPGroup'.to_le hXS
    have hXN : X ≤ Subgroup.normalizer (K : Set G) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hnK)
    have hXt : ∀ x ∈ X, x * t = t * x := by
      intro x hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (show Commute n t from hnt') m).eq
    have hXK : ∀ x ∈ X, conjSub x K = K := fun x hx =>
      mem_normalizer_iff_conjSub_eq.mp (hXN hx)
    exact (d.late_98_iff d.late_JW d.late_hW hX2 hXS hXt).mp hXK n (Subgroup.mem_zpowers n)
  have hWN : ∀ w ∈ W, n * w * n⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (d.hWN hnS) w).mp hw
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hv₀JW : v₀ ∈ J ⊓ W := hv₀ ▸ Subgroup.mem_zpowers v₀
  obtain ⟨l, hl⟩ : ∃ l : ℤ, n * u * n⁻¹ = u ^ l := by
    have h0 : n * u * n⁻¹ ∈ K := by
      have := conj_mem_conjSub (n := n) huKW.1
      rwa [hnK] at this
    have h1 : n * u * n⁻¹ ∈ Subgroup.zpowers u := by
      rw [hu]
      exact Subgroup.mem_inf.mpr ⟨h0, hWN u huKW.2⟩
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact ⟨l, hl.symm⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, n * v₀ * n⁻¹ = v₀ ^ m := by
    have h0 : n * v₀ * n⁻¹ ∈ J := by
      have := conj_mem_conjSub (n := n) hv₀JW.1
      rwa [hnJ] at this
    have h1 : n * v₀ * n⁻¹ ∈ Subgroup.zpowers v₀ := by
      rw [hv₀]
      exact Subgroup.mem_inf.mpr ⟨h0, hWN v₀ hv₀JW.2⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact ⟨m, hm.symm⟩
  obtain ⟨x, -, hxW, -, hxz, hx⟩ := d.v_same_aut hnS hnK hnt
  have hy : x * u * x⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v₀ := by
    rw [← hWgen]
    exact (Subgroup.mem_normalizer_iff.mp hxW u).mp huKW.2
  obtain ⟨a, b, hab⟩ := T3V.mem_sup_zpowers_of_commute huv hy
  have hcomm : ∀ i j : ℤ, u ^ i * v₀ ^ j = v₀ ^ j * u ^ i := fun i j =>
    ((show Commute u v₀ from huv).zpow_zpow i j).eq
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hbodd : Odd b := by
    have h1 : (x * u * x⁻¹) ^ 2 ^ k = t := by
      rw [conj_pow, huz, hxz]
    have h2 : (x * u * x⁻¹) ^ 2 ^ k = z ^ a * t ^ b := by
      rw [hab, ((show Commute (u ^ a) (v₀ ^ b) from
        (show Commute u v₀ from huv).zpow_zpow a b)).mul_pow, ← zpow_natCast (u ^ a),
        ← zpow_natCast (v₀ ^ b), ← zpow_mul, ← zpow_mul, mul_comm a, mul_comm b, zpow_mul,
        zpow_mul, zpow_natCast, zpow_natCast, huz, hv₀t]
    rw [h1] at h2
    by_contra hb
    have hbe : Even b := Int.not_odd_iff_even.mp hb
    have h3 : t ^ b = 1 := (y_zpow_of_sq ht2 b).1 hbe
    rw [h3, mul_one] at h2
    rcases Int.even_or_odd a with ha | ha
    · have := (y_zpow_of_sq hz2 a).1 ha
      rw [this] at h2
      exact d.viol.hzJ.ne_one h2
    · have := (y_zpow_of_sq hz2 a).2 ha
      rw [this] at h2
      exact d.late_ne_inv h2
  have hny : n * (x * u * x⁻¹) * n⁻¹ = (x * u * x⁻¹) ^ l := by
    have h1 := hx u huKW.2
    rw [hl] at h1
    rw [h1, conj_zpow]
  have hny2 : n * (x * u * x⁻¹) * n⁻¹ = (u ^ l) ^ a * (v₀ ^ m) ^ b := by
    rw [hab]
    have : n * (u ^ a * v₀ ^ b) * n⁻¹ = (n * u * n⁻¹) ^ a * (n * v₀ * n⁻¹) ^ b := by
      have e : n * (u ^ a * v₀ ^ b) * n⁻¹ = (n * u ^ a * n⁻¹) * (n * v₀ ^ b * n⁻¹) := by group
      rw [e, ← conj_zpow, ← conj_zpow]
    rw [this, hl, hm]
  have hyl : (x * u * x⁻¹) ^ l = (u ^ a) ^ l * (v₀ ^ b) ^ l := by
    rw [hab]
    exact ((show Commute (u ^ a) (v₀ ^ b) from
      (show Commute u v₀ from huv).zpow_zpow a b)).mul_zpow l
  have hua : (u ^ l) ^ a = (u ^ a) ^ l := by
    rw [← zpow_mul, ← zpow_mul, mul_comm]
  have hvv : v₀ ^ (m * b) = v₀ ^ (b * l) := by
    have h := hny.symm.trans hny2
    rw [hyl, hua] at h
    have h' := mul_left_cancel h
    rw [← zpow_mul, ← zpow_mul] at h'
    exact h'.symm
  have hdvd : ((2 : ℤ) ^ (k + 1)) ∣ b * (m - l) := by
    have h1 : v₀ ^ (b * (m - l)) = 1 := by
      rw [mul_sub, mul_comm b m, zpow_sub, hvv, mul_inv_cancel]
    have h2 := (orderOf_dvd_iff_zpow_eq_one (x := v₀) (i := b * (m - l))).mpr h1
    rw [hv₀o] at h2
    exact_mod_cast h2
  have hcop : IsCoprime ((2 : ℤ) ^ (k + 1)) b := by
    obtain ⟨c, hc⟩ := hbodd
    refine IsCoprime.pow_left ?_
    exact ⟨-c, 1, by rw [hc]; ring⟩
  have hml : v₀ ^ m = v₀ ^ l := by
    have h1 : ((2 : ℤ) ^ (k + 1)) ∣ (m - l) := hcop.dvd_of_dvd_mul_left hdvd
    have h2 : v₀ ^ (m - l) = 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := v₀) (i := m - l)).mp (by
        rw [hv₀o]; exact_mod_cast h1)
      exact this
    rw [zpow_sub, mul_inv_eq_one] at h2
    exact h2
  refine ⟨l, fun w hw => ?_⟩
  rw [hWgen] at hw
  obtain ⟨i, j, rfl⟩ := T3V.mem_sup_zpowers_of_commute huv hw
  have hc2 : Commute (u ^ i) (v₀ ^ j) := (show Commute u v₀ from huv).zpow_zpow i j
  rw [hc2.mul_zpow]
  have : n * (u ^ i * v₀ ^ j) * n⁻¹ = (n * u * n⁻¹) ^ i * (n * v₀ * n⁻¹) ^ j := by
    have e : n * (u ^ i * v₀ ^ j) * n⁻¹ = (n * u ^ i * n⁻¹) * (n * v₀ ^ j * n⁻¹) := by group
    rw [e, ← conj_zpow, ← conj_zpow]
  rw [this, hl, hm, hml, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm l i,
    mul_comm l j]

theorem Std20.y_comm_of_scalar (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z)
    {n : G} (hnS : n ∈ (S : Subgroup G)) {l : ℤ} (hl : ∀ w ∈ W, n * w * n⁻¹ = w ^ l) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : ⁅n, s⁆ ∈ W := by
  have hWs : ∀ s' ∈ (S : Subgroup G), ∀ y ∈ W, s' * y * s'⁻¹ ∈ W := fun s' hs' y hy =>
    (Subgroup.mem_normalizer_iff.mp (d.hWN hs') y).mp hy
  refine d.y_CSW_le_W c7 ?_ ?_
  · rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hnS hsS) (S.inv_mem hnS)) (S.inv_mem hsS)
  · intro w hw
    have hw₁ : s⁻¹ * w * s ∈ W := by
      have := hWs s⁻¹ (S.inv_mem hsS) w hw
      simpa using this
    have hw₂ : n⁻¹ * (s⁻¹ * w * s) * n ∈ W := by
      have := hWs n⁻¹ (S.inv_mem hnS) _ hw₁
      simpa using this
    have h1 : n * (n⁻¹ * (s⁻¹ * w * s) * n) * n⁻¹ = s⁻¹ * w * s := by group
    have h2 := hl _ hw₂
    rw [h1] at h2
    have h3 : n * (s * (n⁻¹ * (s⁻¹ * w * s) * n) * s⁻¹) * n⁻¹ =
        (s * (n⁻¹ * (s⁻¹ * w * s) * n) * s⁻¹) ^ l := hl _ (hWs s hsS _ hw₂)
    rw [conj_zpow, ← h2] at h3
    have h4 : ⁅n, s⁆ * w * ⁅n, s⁆⁻¹ = w := by
      calc ⁅n, s⁆ * w * ⁅n, s⁆⁻¹
          = n * (s * (n⁻¹ * (s⁻¹ * w * s) * n) * s⁻¹) * n⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = s * (s⁻¹ * w * s) * s⁻¹ := h3
        _ = w := by group
    calc ⁅n, s⁆ * w = ⁅n, s⁆ * w * ⁅n, s⁆⁻¹ * ⁅n, s⁆ := by group
      _ = w * ⁅n, s⁆ := by rw [h4]

theorem Std20.y_comm_N (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z) {u : G}
    {k : ℕ} (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) {n : G}
    (hn : n ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : ⁅n, s⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hnS : n ∈ (S : Subgroup G) := (Subgroup.mem_inf.mp hn).1
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_inf.mp hn).2
  obtain ⟨r, hrR, r', hr', -, hrt⟩ := d.late_tor d.late_JW d.late_hW
  have hrX : r ∈ X := le_sec20X_left (d.hR.1 hrR)
  have hrS : r ∈ (S : Subgroup G) := d.hRS hrR
  have hrK : conjSub r K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer (d.hR.1 hrR))
  have hz2 : z * z = 1 := d.viol.hzK.sq
  rcases d.late_S_act_t hnS with hnt | hnt
  · obtain ⟨l, hl⟩ := d.y_scalar hu huo hnS hnK hnt
    exact d.y_W_le_X (d.y_comm_of_scalar c7 hnS hl hsS)
  · set n₀ : G := r⁻¹ * n with hn₀
    have hn₀S : n₀ ∈ (S : Subgroup G) := S.mul_mem (S.inv_mem hrS) hnS
    have hn₀K : conjSub n₀ K = K := by
      rw [hn₀, conjSub_mul]
      have : conjSub r⁻¹ K = K := by
        have h := congrArg (conjSub r⁻¹) hrK
        rw [conjSub_inv_conjSub] at h
        exact h.symm
      rw [hnK, this]
    have hrz : r * z * r⁻¹ = z := d.late_S_act_z hrS
    have hrt' : r⁻¹ * t * r = z * t := by
      have h1 : r⁻¹ * (z * t) * r = t := by
        calc r⁻¹ * (z * t) * r = r⁻¹ * (r * t * r⁻¹) * r := by rw [hrt]
          _ = t := by group
      have h2 : r⁻¹ * z * r = z := by
        have := congrArg (fun y => r⁻¹ * y * r) hrz
        simpa [mul_assoc] using this.symm
      calc r⁻¹ * t * r = z * (z * (r⁻¹ * t * r)) := by
            rw [← mul_assoc, hz2, one_mul]
        _ = z * (r⁻¹ * z * r * (r⁻¹ * t * r)) := by rw [h2]
        _ = z * (r⁻¹ * (z * t) * r) := by group
        _ = z * t := by rw [h1]
    have hn₀t : n₀ * t * n₀⁻¹ = t := by
      calc n₀ * t * n₀⁻¹ = r⁻¹ * (n * t * n⁻¹) * r := by rw [hn₀]; group
        _ = r⁻¹ * (z * t) * r := by rw [hnt]
        _ = (r⁻¹ * z * r) * (r⁻¹ * t * r) := by group
        _ = z * (z * t) := by
          rw [hrt']
          have h2 : r⁻¹ * z * r = z := by
            have := congrArg (fun y => r⁻¹ * y * r) hrz
            simpa [mul_assoc] using this.symm
          rw [h2]
        _ = t := by rw [← mul_assoc, hz2, one_mul]
    obtain ⟨l, hl⟩ := d.y_scalar hu huo hn₀S hn₀K hn₀t
    have h1 : ⁅n₀, s⁆ ∈ X := d.y_W_le_X (d.y_comm_of_scalar c7 hn₀S hl hsS)
    have h2 : ⁅r, s⁆ ∈ X := by
      rw [commutatorElement_def]
      have : s * r⁻¹ * s⁻¹ ∈ X := d.y_S_norm_X hsS (X.inv_mem hrX)
      simpa [mul_assoc] using X.mul_mem hrX this
    have e : ⁅n, s⁆ = r * ⁅n₀, s⁆ * r⁻¹ * ⁅r, s⁆ := by
      simp only [commutatorElement_def, hn₀]
      group
    rw [e]
    exact X.mul_mem (X.mul_mem (X.mul_mem hrX h1) (X.inv_mem hrX)) h2

end Std

section Props

variable (p f : ℕ) [Fact p.Prime]


theorem res10aCyc_proved : Res10aCyc p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb
  obtain ⟨u, k, -, hu, huo, -⟩ := hb.modular
  exact d.y_cyc_of_swapComm c3 c8 (fun n hn w hw _ => d.y_comm_N c7 hu huo hn hw)

theorem swapComm_proved : SwapComm p f :=
  swapComm_of_res10aCyc p f (res10aCyc_proved p f)

end Props

end CFSG.ClassicalInvolution.Asc77.T3CII
