module

public import CFSG.ClassicalInvolution.AschTight.TzConj
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

structure SDData (P : Subgroup G) (a b : G) (M : ℕ) : Prop where
  ord : orderOf a = 8 * M
  pow2 : ∃ e : ℕ, M = 2 ^ e
  card : Nat.card P = 16 * M
  b2 : b * b = 1
  bA : b ∉ Subgroup.zpowers a
  conj : b * a * b⁻¹ = a ^ (4 * (M : ℤ) - 1)
  eq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = P

theorem exists_sdData [Finite G] {P : Subgroup G} (hP2 : IsPGroup 2 P) (hsd : IsSemidihedral P) :
    ∃ a b : G, ∃ M : ℕ, SDData P a b M := by
  obtain ⟨a, b, ha8, hcard, hb2, hbA, hbab, hcl⟩ := hsd
  have haP : a ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hadvd : orderOf a ∣ 2 ^ n := hn ▸ Subgroup.orderOf_dvd_natCard _ haP
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hadvd
  have he3 : 3 ≤ e := by
    by_contra h
    have : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hord : orderOf a = 8 * 2 ^ (e - 3) := by
    rw [he, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.add_sub_cancel' he3]
  refine ⟨a, b, 2 ^ (e - 3), hord, ⟨e - 3, rfl⟩, by rw [hcard, hord]; ring, hb2, hbA, ?_, ?_⟩
  · rw [hbab, ← zpow_natCast]
    congr 1
    have : 1 ≤ 2 ^ (e - 3) := Nat.one_le_two_pow
    omega
  · rw [← closure_pair_eq_sup_zpowers, hcl]

namespace SDData

variable {P : Subgroup G} {a b : G} {M : ℕ} (h : SDData P a b M)
include h

theorem M_pos : 0 < M := by
  obtain ⟨e, he⟩ := h.pow2
  rw [he]
  positivity

theorem zpow_eq_one_iff (i : ℤ) : a ^ i = 1 ↔ (8 * M : ℤ) ∣ i := by
  rw [← orderOf_dvd_iff_zpow_eq_one, h.ord]
  push_cast
  rfl

theorem binv : b⁻¹ = b := inv_eq_of_mul_eq_one_right h.b2

theorem a_mem : a ∈ P := h.eq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)

theorem b_mem : b ∈ P := h.eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

theorem conj_zpow (i : ℤ) : b * a ^ i * b⁻¹ = a ^ (i * (4 * M - 1)) := by
  rw [← _root_.conj_zpow, h.conj, ← zpow_mul, mul_comm]

theorem b_mem_normalizer : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  refine mem_normalizer_of_mul_self_eq_one h.b2 fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [h.conj_zpow]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _

theorem mem_or {x : G} (hx : x ∈ P) : (∃ i : ℤ, a ^ i = x) ∨ ∃ i : ℤ, a ^ i * b = x := by
  rcases mem_or_mul_mem_of_mem_sup_zpowers h.b2 h.b_mem_normalizer (h.eq ▸ hx) with hx' | hx'
  · exact Or.inl (Subgroup.mem_zpowers_iff.mp hx')
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx'
    refine Or.inr ⟨i, ?_⟩
    rw [hi, mul_assoc, h.b2, mul_one]

theorem sq (i : ℤ) : a ^ i * b * (a ^ i * b) = a ^ (4 * M * i) := by
  calc a ^ i * b * (a ^ i * b) = a ^ i * (b * a ^ i * b⁻¹) := by rw [h.binv]; group
    _ = a ^ (4 * M * i) := by rw [h.conj_zpow, ← zpow_add]; congr 1; ring

theorem conj_mul (i j : ℤ) : a ^ j * (a ^ i * b) * (a ^ j)⁻¹ = a ^ (i + j * (2 - 4 * M)) * b := by
  calc a ^ j * (a ^ i * b) * (a ^ j)⁻¹ = a ^ j * a ^ i * (b * a ^ (-j) * b⁻¹) * b := by
        rw [zpow_neg]; group
    _ = a ^ (i + j * (2 - 4 * M)) * b := by
        rw [h.conj_zpow, ← zpow_add, ← zpow_add]; congr 2; ring

theorem pow_four (i : ℤ) : (a ^ i * b) ^ 4 = 1 := by
  have h2 : (a ^ i * b) ^ 2 = a ^ (4 * M * i) := by rw [_root_.sq]; exact h.sq i
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, ← zpow_natCast, ← zpow_mul,
    h.zpow_eq_one_iff]
  exact ⟨i, by push_cast; ring⟩

theorem zpow_mul_not_mem (i : ℤ) : a ^ i * b ∉ Subgroup.zpowers a := by
  intro hx
  apply h.bA
  have : b = (a ^ i)⁻¹ * (a ^ i * b) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)) hx

theorem exists_centralized [Finite G] {s : G} (hs2 : s * s = 1)
    (hsN : s ∈ Subgroup.normalizer (P : Set G)) :
    ∃ x ∈ P, s * x = x * s ∧ x ≠ 1 ∧ x ≠ a ^ (4 * (M : ℤ)) := by
  have hM := h.M_pos
  have hconjP : ∀ x ∈ P, s * x * s⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
  have hss : ∀ x : G, s * (s * x * s⁻¹) * s⁻¹ = x := fun x => by
    calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
      _ = x := by rw [hs2]; group
  have hcomm : ∀ x : G, s * x * s⁻¹ = x → s * x = x * s := fun x hx => by
    calc s * x = s * x * s⁻¹ * s := by group
      _ = x * s := by rw [hx]
  obtain ⟨u, hu⟩ : ∃ u : ℤ, a ^ u = s * a * s⁻¹ := by
    rcases h.mem_or (hconjP a h.a_mem) with hu | ⟨i, hi⟩
    · exact hu
    · exfalso
      have hord : orderOf (s * a * s⁻¹) = 8 * M := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.ord]
      have hdvd : orderOf (s * a * s⁻¹) ∣ 4 := by
        rw [← hi]
        exact orderOf_dvd_of_pow_eq_one (h.pow_four i)
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  have hσ : ∀ i : ℤ, s * a ^ i * s⁻¹ = a ^ (u * i) := fun i => by
    rw [← _root_.conj_zpow, ← hu, ← zpow_mul]
  obtain ⟨v, hv⟩ : ∃ v : ℤ, a ^ v * b = s * b * s⁻¹ := by
    rcases h.mem_or (hconjP b h.b_mem) with ⟨v, hv⟩ | hv
    · exfalso
      apply h.bA
      rw [← hss b, ← hv, hσ]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · exact hv
  obtain ⟨v', hv'⟩ : ∃ v' : ℤ, v = 2 * v' := by
    have h1 : a ^ v * b * (a ^ v * b) = 1 := by
      rw [hv]
      calc s * b * s⁻¹ * (s * b * s⁻¹) = s * (b * b) * s⁻¹ := by group
        _ = 1 := by rw [h.b2]; group
    rw [h.sq, h.zpow_eq_one_iff] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, mul_left_cancel₀ (show (4 * (M : ℤ)) ≠ 0 by positivity) ?_⟩
    linarith
  have hu2 : (8 * M : ℤ) ∣ u * u - 1 := by
    rw [← h.zpow_eq_one_iff, zpow_sub, zpow_one, ← hσ u, hu, hss, mul_inv_cancel]
  by_cases h4 : (4 : ℤ) ∣ u - 1
  ·
    obtain ⟨c, hc⟩ := h4
    have h1 : a ^ (2 * (M : ℤ)) ≠ 1 := by
      intro h1
      rw [h.zpow_eq_one_iff] at h1
      obtain ⟨d, hd⟩ := h1
      have : (M : ℤ) * (2 - 8 * d) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> omega
    refine ⟨a ^ (2 * (M : ℤ)), P.zpow_mem h.a_mem _, hcomm _ ?_, h1, fun h2 => h1 ?_⟩
    · rw [hσ, ← mul_inv_eq_one, ← zpow_sub, h.zpow_eq_one_iff]
      exact ⟨c, by linear_combination (2 * (M : ℤ)) * hc⟩
    · have : a ^ (4 * (M : ℤ)) = a ^ (2 * (M : ℤ)) * a ^ (2 * (M : ℤ)) := by
        rw [← zpow_add]; ring_nf
      rw [← h2] at this
      exact left_eq_mul.mp this
  ·
    have hu_odd : Odd u := by
      rcases Int.even_or_odd u with ⟨w, hw⟩ | hodd
      · exfalso
        obtain ⟨c, hc⟩ := hu2
        have h2 : (2 : ℤ) ∣ u * u - 1 := ⟨4 * M * c, by linarith⟩
        have h3 : (2 : ℤ) ∣ u * u := ⟨w * u, by rw [hw]; ring⟩
        have h5 := dvd_sub h3 h2
        simp at h5
      · exact hodd
    obtain ⟨c, hc⟩ := hu_odd
    have hc_odd : Odd c := by
      rcases Int.even_or_odd c with ⟨d, hd⟩ | hodd
      · exact absurd ⟨d, by omega⟩ h4
      · exact hodd
    obtain ⟨c', hc'⟩ := hc_odd
    obtain ⟨d, hd⟩ := hu2
    have hcc : (2 * (M : ℤ)) ∣ c * (c + 1) := ⟨d, by subst hc; linarith⟩
    obtain ⟨e, he⟩ := h.pow2
    have hcop : IsCoprime (2 * (M : ℤ)) c := by
      have h2c : IsCoprime (2 : ℤ) c := ⟨-c', 1, by rw [hc']; ring⟩
      have h2M : (2 * (M : ℤ)) = 2 ^ (e + 1) := by rw [he]; push_cast; ring
      rw [h2M]
      exact h2c.pow_left
    obtain ⟨d', hd'⟩ := hcop.dvd_of_dvd_mul_left hcc
    set i : ℤ := v' * (c + 2) with hi
    refine ⟨a ^ i * b, P.mul_mem (P.zpow_mem h.a_mem _) h.b_mem, hcomm _ ?_, ?_, ?_⟩
    · calc s * (a ^ i * b) * s⁻¹ = s * a ^ i * s⁻¹ * (s * b * s⁻¹) := by group
        _ = a ^ (u * i + v) * b := by rw [hσ, ← hv, ← mul_assoc, ← zpow_add]
        _ = a ^ i * b := by
          congr 1
          rw [← mul_inv_eq_one, ← zpow_sub, h.zpow_eq_one_iff]
          refine ⟨v' * M * d' * d', ?_⟩
          rw [hi, hv', hc]
          linear_combination (2 * v' * (c + 1 + 2 * M * d')) * hd'
    · intro h1
      exact h.zpow_mul_not_mem i (h1 ▸ Subgroup.one_mem _)
    · intro h1
      exact h.zpow_mul_not_mem i (h1 ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)

end SDData

theorem conj_of_not_mem_of_isSemidihedral [Finite G] {R : Subgroup G} {z t : G}
    (hR2 : IsPGroup 2 R) (hz : IsUniqueInvolution R z) (hRnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x)
    (ht : t * t = 1) (htR : t ∉ R) (htN : t ∈ Subgroup.normalizer (R : Set G))
    (hsd : IsSemidihedral (R ⊔ Subgroup.zpowers t)) {x : G} (hxP : x ∈ R ⊔ Subgroup.zpowers t)
    (hxR : x ∉ R) (hx : x * x = 1 ∨ x * x = z) :
    x * x = 1 ∧ ∃ y ∈ R ⊔ Subgroup.zpowers t, y * t * y⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := fun h => htR (h ▸ R.one_mem)
  have hord2 : orderOf t = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact ht) ht1
  have hzt2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, hord2]
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr htN
  obtain ⟨a, b, M, h⟩ := exists_sdData (hR2.to_sup_of_normal_left' hzt2 hle) hsd
  have hM := h.M_pos
  have htP : t ∈ R ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hpow2 : ∀ j : ℤ, a ^ (2 * j) ∈ R := fun j => by
    rw [zpow_mul, zpow_two]
    exact R.zpow_mem (mul_self_mem_of_mem_sup_zpowers ht htN h.a_mem) j
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℤ, a ^ (2 * p₀) * b = t := by
    rcases h.mem_or htP with ⟨i₀, hi₀⟩ | ⟨i₀, hi₀⟩
    · exfalso
      apply htR
      have h4 : a ^ (4 * (M : ℤ)) * a ^ (4 * (M : ℤ)) = 1 := by
        rw [← zpow_add, h.zpow_eq_one_iff]
        exact ⟨1, by ring⟩
      have h41 : a ^ (4 * (M : ℤ)) ≠ 1 := by
        rw [Ne, h.zpow_eq_one_iff]
        rintro ⟨c, hc⟩
        have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0 <;> omega
      rw [← hi₀, zpow_eq_zpow_of_mul_self_eq_one (by rw [hi₀]; exact ht) h4
        (by rw [hi₀]; exact ht1) h41, show 4 * (M : ℤ) = 2 * (2 * M) by ring]
      exact hpow2 _
    · have h1 := h.sq i₀
      rw [hi₀, ht, eq_comm, h.zpow_eq_one_iff] at h1
      obtain ⟨c, hc⟩ := h1
      refine ⟨c, ?_⟩
      rw [← hi₀]
      congr 2
      exact mul_left_cancel₀ (show (4 * (M : ℤ)) ≠ 0 by positivity) (by linarith)
  have hcardR : Nat.card R = 8 * M := by
    have h1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R
      (Subgroup.zpowers t) hle (by
        rw [Subgroup.disjoint_def]
        intro y hyR hyt
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
        rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · rw [← two_mul, zpow_mul, zpow_two, ht, one_zpow]
        · exfalso
          rw [zpow_add_one, zpow_mul, zpow_two, ht, one_zpow, one_mul] at hyR
          exact htR hyR)
    rw [h.card, Nat.card_zpowers, hord2] at h1
    omega
  have haR : a ∉ R := by
    intro haR
    have hle' : Subgroup.zpowers a ≤ R := Subgroup.zpowers_le.mpr haR
    have heq : Subgroup.zpowers a = R :=
      Subgroup.eq_of_le_of_card_ge hle' (by rw [hcardR, Nat.card_zpowers, h.ord])
    obtain ⟨y, hy, w, hw, hyw⟩ := hRnc
    rw [← heq] at hy hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact hyw (zpow_mul_comm a i j)
  have hbR : b ∉ R := by
    intro hbR
    apply htR
    rw [← hp₀]
    exact R.mul_mem (hpow2 p₀) hbR
  have hidx : ∀ y ∈ R ⊔ Subgroup.zpowers t, ∀ w ∈ R ⊔ Subgroup.zpowers t, y ∉ R → w ∉ R →
      y * w ∈ R := by
    intro y hy w hw hyR hwR
    have hyt := (mem_or_mul_mem_of_mem_sup_zpowers ht htN hy).resolve_left hyR
    have hwt := (mem_or_mul_mem_of_mem_sup_zpowers ht htN hw).resolve_left hwR
    have htw : t * (w * t) * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp htN _).mp hwt
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have e : y * w = y * t * (t * (w * t) * t⁻¹) := by
      rw [ht']
      calc y * w = y * (t * t) * w * (t * t) := by rw [ht, mul_one, mul_one]
        _ = y * t * (t * (w * t) * t) := by group
    rw [e]
    exact R.mul_mem hyt htw
  have hab : a * b ∈ R := hidx a h.a_mem b h.b_mem haR hbR
  rcases h.mem_or hxP with ⟨i, rfl⟩ | ⟨i, rfl⟩
  ·
    exfalso
    have hi : ¬ (2 : ℤ) ∣ i := by
      rintro ⟨m, rfl⟩
      exact hxR (hpow2 m)
    have hzR : z = a ^ (4 * (M : ℤ)) := by
      have h4 : a ^ (4 * (M : ℤ)) ∈ R := by
        rw [show 4 * (M : ℤ) = 2 * (2 * M) by ring]; exact hpow2 _
      refine ((hz.unique _ h4 ?_).resolve_left ?_).symm
      · rw [← zpow_add, h.zpow_eq_one_iff]; exact ⟨1, by ring⟩
      · rw [h.zpow_eq_one_iff]
        rintro ⟨c, hc⟩
        have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0 <;> omega
    rw [hzR, ← zpow_add] at hx
    rcases hx with hx | hx
    · rw [h.zpow_eq_one_iff] at hx
      obtain ⟨c, hc⟩ := hx
      exact hi ⟨2 * M * c, by linarith⟩
    · rw [← mul_inv_eq_one, ← zpow_sub, h.zpow_eq_one_iff] at hx
      obtain ⟨c, hc⟩ := hx
      exact hi ⟨M + 2 * M * c, by linarith⟩
  ·
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = 2 * p := by
      rcases Int.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m, by omega⟩
      · exfalso
        apply hxR
        rw [hm, zpow_add_one, mul_assoc]
        exact R.mul_mem (hpow2 m) hab
    refine ⟨?_, a ^ ((p - p₀) * (2 * M + 1)), (R ⊔ Subgroup.zpowers t).zpow_mem h.a_mem _, ?_⟩
    · rw [h.sq, h.zpow_eq_one_iff]
      exact ⟨p, by ring⟩
    · rw [← hp₀, h.conj_mul]
      congr 1
      rw [← mul_inv_eq_one, ← zpow_sub, h.zpow_eq_one_iff]
      exact ⟨-(M * (p - p₀)), by ring⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight
