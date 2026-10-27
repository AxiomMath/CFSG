module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step10
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step12

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Thompson
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup G}

section Certified


theorem S7Config.star (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) (hIS : ∀ y ∈ S, y * y = 1 → y ∈ L) {x : G}
    (hxS : x ∈ S) (hx1 : x ≠ 1) :
    ∃ g : G, g * x * g⁻¹ ∈ S ∧ x⁻¹ * (g * x * g⁻¹) ∈ L ∧ (g * x * g⁻¹) ^ (orderOf x / 2) = z := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d⟩ := h.exists_step6 hI hS
  obtain ⟨π, hπz, hπT, hπL⟩ := d.exists_pi hI h hS
  have h2 := two_dvd_orderOf hS.isPGroup hxS hx1
  set k := orderOf x / 2 with hk
  have hk2 : 2 * k = orderOf x := Nat.mul_div_cancel' h2
  have hk0 : k ≠ 0 := fun h0 => by
    have h1 := orderOf_pos x
    omega
  have hklt : k < orderOf x := by
    have h1 := orderOf_pos x
    omega
  set j := x ^ k with hj
  have hjS : j ∈ S := pow_mem hxS k
  have hj2 : j * j = 1 := by rw [hj, ← pow_add, ← two_mul, hk2, pow_orderOf_eq_one]
  have hj1 : j ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
  have hjL : j ∈ L := hIS j hjS hj2
  have hjo : orderOf j = 2 := orderOf_eq_prime (by rw [sq, hj2]) hj1
  by_cases hjz : j = z
  · refine ⟨1, by simpa using hxS, by simp, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact hjz
  have hjZ : (QuotientGroup.mk (⟨j, hjL⟩ : ↥L) : Bar L) ∉ center (Bar L) :=
    fun hc => hjz (h.eq_of_mk_mem_center hjL hjo hc)
  obtain ⟨a, haL, ha⟩ := F3S7.spinSeven_conj_of_involution_three h.hcov hjL d.hz₁L hjo d.hz₁ hjZ
    d.hz₁Z
  have haH : a ∈ centralizer ({z} : Set G) := h.hL.1 haL
  have hxH : x ∈ centralizer ({z} : Set G) := hS.le hxS
  set x' := a * x * a⁻¹ with hx'
  have hx'k : x' ^ k = d.z₁ := by rw [hx', conj_pow]; exact ha
  have hx'z₁ : x' * d.z₁ = d.z₁ * x' := by rw [← hx'k]; exact (Commute.self_pow x' k).eq
  have hx'M : x' ∈ centralizer ({z} : Set G) ⊓ centralizer {d.z₁} :=
    mem_inf.mpr ⟨mul_mem (mul_mem haH hxH) (inv_mem haH), mem_centralizer_singleton_iff.mpr hx'z₁⟩
  obtain ⟨m, hm⟩ := exists_orderOf_eq_two_pow hS.isPGroup hxS
  have hx'n : x' ^ 2 ^ m = 1 := by rw [hx', conj_pow, ← hm, pow_orderOf_eq_one]; group
  obtain ⟨c, hcM, hc⟩ := IsSylowOf.exists_conj_le d.hT (zpowers_le.mpr hx'M)
    (isPGroup_zpowers_of_pow hx'n)
  have hx''T := hc x' (mem_zpowers x')
  have hcH : c ∈ centralizer ({z} : Set G) := (mem_inf.mp hcM).1
  have hcz₁ : c * d.z₁ = d.z₁ * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hcM).2
  have hkx : (c⁻¹ * a) * x * (c⁻¹ * a)⁻¹ = c⁻¹ * x' * c := by rw [hx']; group
  refine ⟨π * (c⁻¹ * a), ?_, ?_, ?_⟩
  · rw [show π * (c⁻¹ * a) * x * (π * (c⁻¹ * a))⁻¹ = π * (c⁻¹ * x' * c) * π⁻¹ by rw [hx']; group]
    exact (mem_inf.mp (hπT _ hx''T)).1
  · have h1 : x⁻¹ * ((c⁻¹ * a) * x * (c⁻¹ * a)⁻¹) ∈ L :=
      h.inv_mul_conj_mem hI hS.le hS.isPGroup hxS (mul_mem (inv_mem hcH) haH)
        (by rw [hkx]; exact (mem_inf.mp hx''T).1)
    rw [hkx] at h1
    have h3 := mul_mem h1 (hπL _ hx''T)
    rwa [show x⁻¹ * (c⁻¹ * x' * c) * ((c⁻¹ * x' * c)⁻¹ * (π * (c⁻¹ * x' * c) * π⁻¹)) =
      x⁻¹ * (π * (c⁻¹ * a) * x * (π * (c⁻¹ * a))⁻¹) by rw [hx']; group] at h3
  · rw [conj_pow, ← hj, show π * (c⁻¹ * a) * j * (π * (c⁻¹ * a))⁻¹ =
      π * (c⁻¹ * (a * j * a⁻¹) * c) * π⁻¹ by group, ha, conj_eq_of_commute hcz₁, hπz]

theorem S7Config.mem_of_mul_self_eq_one (hI : S7Inputs) (h : S7Config G z L)
    {S V : Subgroup G} (hS : IsSylowOf 2 S (centralizer {z})) (hVS : V ≤ S)
    (hVn : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ V)
    (hVz : ∀ v ∈ V, v * v ∈ zpowers z → v ∈ L) {x : G} (hxS : x ∈ S) (hx : x * x = 1) :
    x ∈ L := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hxL
  have hx1 : x ≠ 1 := fun h1 => hxL (h1 ▸ one_mem L)
  have hxV : x ∉ V := fun hxV => hxL (hVz x hxV (hx ▸ one_mem _))
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ S → g⁻¹ * x ^ (2 * k) * g ∈ V := by
    intro g k _
    rw [pow_mul, sq, hx, one_pow, mul_one, inv_mul_cancel]
    exact one_mem V
  have hc : ∀ g : G, g⁻¹ * x * g ∈ S → IsExtremalIn 2 S (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ V ∨ x⁻¹ * (g⁻¹ * x * g) ∈ V := by
    intro g hgS _
    by_cases hy : g⁻¹ * x * g ∈ V
    · exact .inl hy
    · refine .inr (inv_mul_mem_of_sq_mem hVn hcyc hxS hgS hxV hy (hx ▸ one_mem V) ?_)
      rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, hx, mul_one,
        inv_mul_cancel]
      exact one_mem V
  obtain ⟨g, hg⟩ := conj_into_of_transfer h.nonab hS.isPGroup (h.not_dvd_index hI hS) hVn hcyc
    hxS hxV hb hc
  have hy2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, hx, mul_one,
      inv_mul_cancel]
  have hyL : g⁻¹ * x * g ∈ L := hVz _ hg (hy2 ▸ one_mem _)
  have hy1 : g⁻¹ * x * g ≠ 1 := fun h1 => hx1 (by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hyo : orderOf (g⁻¹ * x * g) = 2 := orderOf_eq_prime (by rw [sq, hy2]) hy1
  obtain ⟨g', hg'⟩ := (h.conj_iff hI (hS.le (hVS hg))).mpr ⟨hyL, hyo⟩
  exact hxL ((h.conj_iff hI (hS.le hxS)).mp ⟨g * g', by
    rw [show g * g' * z * (g * g')⁻¹ = g * (g' * z * g'⁻¹) * g⁻¹ by group, hg']
    group⟩).1

theorem S7Config.forall_mem_V (hI : S7Inputs) (h : S7Config G z L) {S V : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) (hVS : V ≤ S) (hLV : S ⊓ L ≤ V)
    (hVn : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ V)
    (hVz : ∀ v ∈ V, v * v ∈ zpowers z → v ∈ L)
    (hVS' : (∃ s ∈ S, s ∉ V) → ∃ x ∈ S, x ∉ L ∧ x * x ∈ zpowers z) : ∀ s ∈ S, s ∈ V := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨x, hxS, hxL, hx2⟩ := hVS' hne
  have hIS : ∀ y ∈ S, y * y = 1 → y ∈ L := fun y hy hy2 =>
    h.mem_of_mul_self_eq_one hI hS hVS hVn hcyc hVz hy hy2
  have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
  have hxz : x * x = z :=
    (T23.eq_one_or_eq_of_mem_zpowers hzz hx2).resolve_left fun h1 => hxL (hIS x hxS h1)
  have hxV : x ∉ V := fun hxV => hxL (hVz x hxV hx2)
  have hzS : z ∈ S := IsSylowOf.mem_of_central hS (mem_centralizer_singleton_iff.mpr rfl)
    (fun k hk => mem_centralizer_singleton_iff.mp hk) (n := 1)
    (by rw [pow_one, ← h.hz, pow_orderOf_eq_one])
  have hzV : z ∈ V := hLV (mem_inf.mpr ⟨hzS, h.hzL⟩)
  have hzconj : ∀ g : G, g⁻¹ * z * g ∈ S → g⁻¹ * z * g ∈ V := fun g hg =>
    hLV (mem_inf.mpr ⟨hg, ((h.conj_iff hI (hS.le hg)).mp ⟨g⁻¹, by group⟩).1⟩)
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ S → g⁻¹ * x ^ (2 * k) * g ∈ V := by
    intro g k hgS
    have h1 : x ^ (2 * k) = z ^ k := by rw [pow_mul, sq, hxz]
    rw [h1] at hgS ⊢
    rcases T23.eq_one_or_eq_of_mem_zpowers hzz (pow_mem (mem_zpowers z) k) with h2 | h2
    · rw [h2, mul_one, inv_mul_cancel]
      exact one_mem V
    · rw [h2] at hgS ⊢
      exact hzconj g hgS
  have hc : ∀ g : G, g⁻¹ * x * g ∈ S → IsExtremalIn 2 S (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ V ∨ x⁻¹ * (g⁻¹ * x * g) ∈ V := by
    intro g hgS _
    by_cases hy : g⁻¹ * x * g ∈ V
    · exact .inl hy
    · have hsq : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * z * g := by
        rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, hxz]
      have hy2 : g⁻¹ * x * g * (g⁻¹ * x * g) ∈ V := by
        rw [hsq]
        exact hzconj g (hsq ▸ mul_mem hgS hgS)
      exact .inr (inv_mul_mem_of_sq_mem hVn hcyc hxS hgS hxV hy (hxz ▸ hzV) hy2)
  obtain ⟨g, hg⟩ := conj_into_of_transfer h.nonab hS.isPGroup (h.not_dvd_index hI hS) hVn hcyc
    hxS hxV hb hc
  have hz1 : z ≠ 1 := fun h1 => by
    have h3 := h.hz
    rw [h1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hx4' : x ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hxz, hzz]
  have hx4 : orderOf x = 4 := by
    have h1 : orderOf x = 2 ^ (1 + 1) := orderOf_eq_prime_pow
      (by rw [pow_one, sq, hxz]; exact hz1)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact hx4')
    exact h1.trans (by norm_num)
  set x₁ := g⁻¹ * x * g with hx₁
  have hx₁o : orderOf x₁ = 4 := by
    rw [hx₁, show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj', hx4]
  have hx₁1 : x₁ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx₁o; exact absurd hx₁o (by norm_num)
  obtain ⟨k, hkS, hkL, hkz⟩ := h.star hI hS hIS (hVS hg) hx₁1
  rw [hx₁o] at hkz
  set y := k * x₁ * k⁻¹ with hy
  have hy2 : y * y = z := by simpa [sq] using hkz
  have hyV : y ∈ V := by
    rw [show y = x₁ * (x₁⁻¹ * y) by group]
    exact mul_mem hg (hLV (mem_inf.mpr ⟨mul_mem (inv_mem (hVS hg)) hkS, hkL⟩))
  have hyc : y = (k * g⁻¹) * x * (k * g⁻¹)⁻¹ := by rw [hy, hx₁]; group
  have hcH : k * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (k * g⁻¹) * z * (k * g⁻¹)⁻¹ = z := by
      calc (k * g⁻¹) * z * (k * g⁻¹)⁻¹ =
          ((k * g⁻¹) * x * (k * g⁻¹)⁻¹) * ((k * g⁻¹) * x * (k * g⁻¹)⁻¹) := by
            rw [← hxz]; group
        _ = z := by rw [← hyc, hy2]
    calc k * g⁻¹ * z = (k * g⁻¹) * z * (k * g⁻¹)⁻¹ * (k * g⁻¹) := by group
      _ = z * (k * g⁻¹) := by rw [h1]
  have h1 := h.inv_mul_conj_mem hI hS.le hS.isPGroup hxS hcH (by rw [← hyc]; exact hVS hyV)
  rw [← hyc] at h1
  apply hxV
  rw [show x = y * (x⁻¹ * y)⁻¹ by group]
  exact mul_mem hyV (inv_mem (hLV (mem_inf.mpr ⟨mul_mem (inv_mem hxS) (hVS hyV), h1⟩)))

theorem S7Config.false (hI : S7Inputs) (h : S7Config G z L) : False := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({z} : Set G))
  obtain ⟨V, hVS, hLV, hVn, hV2, hcyc, hVz, hVS'⟩ := h.exists_V hI hS
  have hIS : ∀ y ∈ S, y * y = 1 → y ∈ L := fun y hy hy2 =>
    h.mem_of_mul_self_eq_one hI hS hVS hVn hcyc hVz hy hy2
  have hSV := h.forall_mem_V hI hS hVS hLV hVn hcyc hVz hVS'
  have hcos : ∀ v ∈ S, ∀ w ∈ S, v ∉ L → w ∉ L → v⁻¹ * w ∈ L := fun v hv w hw =>
    hV2 v (hSV v hv) w (hSV w hw)
  have hLn := h.normal hI
  have hex : ∃ n, ∃ x ∈ S, x ∉ L ∧ orderOf x = n := by
    obtain ⟨s, hs, hsL⟩ := IsConcreteLE.not_le_iff_exists.mp (h.not_le hI hS)
    exact ⟨_, s, hs, hsL, rfl⟩
  obtain ⟨x, hxS, hxL, hxo⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ S, y ∉ L → Nat.find hex ≤ orderOf y := fun y hy hyL =>
    Nat.find_min' hex ⟨y, hy, hyL, rfl⟩
  have hx1 : x ≠ 1 := fun h1 => hxL (h1 ▸ one_mem L)
  have h2 := two_dvd_orderOf hS.isPGroup hxS hx1
  have hVn' : ∀ s ∈ S, ∀ q ∈ S ⊓ L, s * q * s⁻¹ ∈ S ⊓ L := fun s hs q hq =>
    mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hq).1) (inv_mem hs),
      (normal_subgroupOf_iff h.hL.1).mp hLn q s (mem_inf.mp hq).2 (hS.le hs)⟩
  have hcyc' : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ S ⊓ L := by
    refine ⟨x, hxS, fun t ht => ?_⟩
    by_cases htL : t ∈ L
    · exact ⟨0, by simpa using mem_inf.mpr ⟨ht, htL⟩⟩
    · exact ⟨1, by simpa using mem_inf.mpr ⟨mul_mem (inv_mem hxS) ht, hcos x hxS t ht hxL htL⟩⟩
  have hxV' : x ∉ S ⊓ L := fun h1 => hxL (mem_inf.mp h1).2
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ S →
      g⁻¹ * x ^ (2 * k) * g ∈ S ⊓ L := by
    intro g k hgS
    refine mem_inf.mpr ⟨hgS, ?_⟩
    by_contra hgL
    have h1 := hmin _ hgS hgL
    rw [show g⁻¹ * x ^ (2 * k) * g = g⁻¹ * x ^ (2 * k) * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj',
      ← hxo] at h1
    have h3 : (x ^ (2 * k)) ^ (orderOf x / 2) = 1 := by
      rw [← pow_mul, show 2 * k * (orderOf x / 2) = k * (2 * (orderOf x / 2)) by ring,
        Nat.mul_div_cancel' h2, pow_mul', pow_orderOf_eq_one, one_pow]
    have h4 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) h2) (by norm_num))
      (orderOf_dvd_of_pow_eq_one h3)
    have h5 : orderOf x / 2 < orderOf x := Nat.div_lt_self (orderOf_pos x) (by norm_num)
    omega
  have hc : ∀ g : G, g⁻¹ * x * g ∈ S → IsExtremalIn 2 S (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ S ⊓ L ∨ x⁻¹ * (g⁻¹ * x * g) ∈ S ⊓ L := by
    intro g hgS _
    by_cases hgL : g⁻¹ * x * g ∈ L
    · exact .inl (mem_inf.mpr ⟨hgS, hgL⟩)
    · exact .inr (mem_inf.mpr ⟨mul_mem (inv_mem hxS) hgS, hcos x hxS _ hgS hxL hgL⟩)
  obtain ⟨g, hg⟩ := conj_into_of_transfer h.nonab hS.isPGroup (h.not_dvd_index hI hS) hVn'
    hcyc' hxS hxV' hb hc
  set x₁ := g⁻¹ * x * g with hx₁
  have hx₁o : orderOf x₁ = orderOf x := by
    rw [hx₁, show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj']
  have hx₁1 : x₁ ≠ 1 := fun h1 => hx1 (by
    calc x = g * x₁ * g⁻¹ := by rw [hx₁]; group
      _ = 1 := by rw [h1]; group)
  obtain ⟨k, hkS, hkL, hkz⟩ := h.star hI hS hIS hxS hx1
  obtain ⟨k', hk'S, hk'L, hk'z⟩ := h.star hI hS hIS (mem_inf.mp hg).1 hx₁1
  rw [hx₁o] at hk'z
  set w := k * x * k⁻¹ with hw
  set v := k' * x₁ * k'⁻¹ with hv
  have hwL : w ∉ L := fun h1 => hxL (by
    rw [show x = w * (x⁻¹ * w)⁻¹ by group]
    exact mul_mem h1 (inv_mem hkL))
  have hvL : v ∈ L := by
    rw [show v = x₁ * (x₁⁻¹ * v) by group]
    exact mul_mem (mem_inf.mp hg).2 hk'L
  set c := k' * g⁻¹ * k⁻¹ with hcdef
  have hvc : v = c * w * c⁻¹ := by rw [hv, hw, hx₁, hcdef]; group
  have hcH : c ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : c * z * c⁻¹ = z := by
      calc c * z * c⁻¹ = c * w ^ (orderOf x / 2) * c⁻¹ := by rw [hkz]
        _ = (c * w * c⁻¹) ^ (orderOf x / 2) := conj_pow.symm
        _ = z := by rw [← hvc, hk'z]
    calc c * z = c * z * c⁻¹ * c := by group
      _ = z * c := by rw [h1]
  have h1 := h.inv_mul_conj_mem hI hS.le hS.isPGroup hkS hcH (by rw [← hvc]; exact hk'S)
  rw [← hvc] at h1
  apply hwL
  rw [show w = v * (w⁻¹ * v)⁻¹ by group]
  exact mul_mem hvL (inv_mem h1)

theorem harris82Theorem1SpinSevenThree_of_inputs (hI : S7Inputs) :
    Harris82Theorem1SpinSevenThree := by
  intro G _ _ _ hnonab hK hcat z hz L hL hzL p f _ h3 hM hcov
  obtain ⟨rfl, rfl⟩ := (Nat.prime_three.pow_eq_iff).mp h3
  exact S7Config.false hI ⟨inferInstance, hnonab, hK, hcat, hz, hL, hzL, hcov, hM⟩

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
