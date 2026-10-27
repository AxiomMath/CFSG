module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndData

public section

open CFSG.Open
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mul_eq {T : Subgroup G} (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {r₀ t : G}
    (ht : t ∈ T) (hconj : r₀ * t * r₀⁻¹ ∈ T) (hr₀ : r₀ * r₀ ∈ T) (j : ℕ) :
    (t * r₀) ^ (2 ^ (j + 1)) = (t * (r₀ * t * r₀⁻¹)) ^ (2 ^ j) * r₀ ^ (2 ^ (j + 1)) := by
  have hsq : (t * r₀) ^ 2 = (t * (r₀ * t * r₀⁻¹)) * (r₀ * r₀) := by
    rw [sq]
    group
  have hc : Commute (t * (r₀ * t * r₀⁻¹)) (r₀ * r₀) :=
    hcomm _ (T.mul_mem ht hconj) _ hr₀
  calc (t * r₀) ^ (2 ^ (j + 1)) = ((t * r₀) ^ 2) ^ (2 ^ j) := by rw [pow_succ', pow_mul]
    _ = ((t * (r₀ * t * r₀⁻¹)) * (r₀ * r₀)) ^ (2 ^ j) := by rw [hsq]
    _ = (t * (r₀ * t * r₀⁻¹)) ^ (2 ^ j) * (r₀ * r₀) ^ (2 ^ j) := hc.mul_pow _
    _ = (t * (r₀ * t * r₀⁻¹)) ^ (2 ^ j) * r₀ ^ (2 ^ (j + 1)) := by
        rw [← sq, ← pow_mul, ← pow_succ']

omit [Finite G] in
theorem pow_mul_mul_eq {T : Subgroup G} (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {r₀ : G}
    (hnorm : ∀ t ∈ T, r₀ * t * r₀⁻¹ ∈ T) (hr₀ : r₀ * r₀ ∈ T) (j : ℕ) {t s : G} (ht : t ∈ T)
    (hs : s ∈ T) :
    (t * r₀) ^ (2 ^ (j + 1)) * (s * r₀) ^ (2 ^ (j + 1)) =
      (t * s * r₀) ^ (2 ^ (j + 1)) * ((1 : G) * r₀) ^ (2 ^ (j + 1)) := by
  have hts := T.mul_mem ht hs
  rw [pow_mul_eq hcomm ht (hnorm t ht) hr₀, pow_mul_eq hcomm hs (hnorm s hs) hr₀,
    pow_mul_eq hcomm hts (hnorm _ hts) hr₀, pow_mul_eq hcomm T.one_mem (hnorm 1 T.one_mem) hr₀]
  set a := t * (r₀ * t * r₀⁻¹) with hadef
  set b := s * (r₀ * s * r₀⁻¹) with hbdef
  set c := r₀ ^ (2 ^ (j + 1)) with hcdef
  have haT : a ∈ T := T.mul_mem ht (hnorm t ht)
  have hbT : b ∈ T := T.mul_mem hs (hnorm s hs)
  have hcT : c ∈ T := by
    rw [hcdef, pow_succ', pow_mul, sq]
    exact T.pow_mem hr₀ _
  have hν : t * s * (r₀ * (t * s) * r₀⁻¹) = a * b := by
    have e : r₀ * (t * s) * r₀⁻¹ = (r₀ * t * r₀⁻¹) * (r₀ * s * r₀⁻¹) := by group
    rw [e, hadef, hbdef]
    have hsw := hcomm s hs _ (hnorm t ht)
    calc t * s * ((r₀ * t * r₀⁻¹) * (r₀ * s * r₀⁻¹))
        = t * (s * (r₀ * t * r₀⁻¹)) * (r₀ * s * r₀⁻¹) := by group
      _ = t * ((r₀ * t * r₀⁻¹) * s) * (r₀ * s * r₀⁻¹) := by rw [hsw]
      _ = t * (r₀ * t * r₀⁻¹) * (s * (r₀ * s * r₀⁻¹)) := by group
  have hν1 : (1 : G) * (r₀ * 1 * r₀⁻¹) = 1 := by group
  rw [hν, hν1, one_pow, one_mul, (show Commute a b from hcomm a haT b hbT).mul_pow]
  have hcb : c * b ^ (2 ^ j) = b ^ (2 ^ j) * c := hcomm c hcT _ (T.pow_mem hbT _)
  calc a ^ (2 ^ j) * c * (b ^ (2 ^ j) * c) = a ^ (2 ^ j) * (c * b ^ (2 ^ j)) * c := by group
    _ = a ^ (2 ^ j) * (b ^ (2 ^ j) * c) * c := by rw [hcb]
    _ = a ^ (2 ^ j) * b ^ (2 ^ j) * c * c := by group

theorem false_of_transitive_fusion {R T : Subgroup G} (hR2 : IsPGroup 2 R) (hTR : T ≤ R)
    (hTab : IsMulCommutative T) (hidx : T.relIndex R = 2)
    (hnoinv : ∀ r ∈ R, r ∉ T → r ^ 2 ≠ 1)
    (hU4 : 4 ≤ Nat.card (AschbacherTheorem3.omegaOne T))
    (htrans : ∀ u ∈ AschbacherTheorem3.omegaOne T, u ≠ 1 →
      ∀ u' ∈ AschbacherTheorem3.omegaOne T, u' ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (T : Set G),
        m⁻¹ * u * m = u') : False := by
  classical
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hidx' : (T.subgroupOf R).index = 2 := hidx
  have hsq : ∀ r ∈ R, r * r ∈ T := fun r hr =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx' ⟨r, hr⟩)
  have hmul : ∀ a ∈ R, ∀ b ∈ R, a ∉ T → b ∉ T → a * b⁻¹ ∈ T := fun a ha b hb haT hbT => by
    have h := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨a, ha⟩) (b := ⟨b, hb⟩⁻¹)
    have h1 : (⟨b, hb⟩ : R)⁻¹ ∉ T.subgroupOf R := fun h2 => hbT (by
      have := (T.subgroupOf R).inv_mem h2
      simpa using Subgroup.mem_subgroupOf.mp this)
    have h2 : (⟨a, ha⟩ : R) ∉ T.subgroupOf R := fun h2 => haT (Subgroup.mem_subgroupOf.mp h2)
    exact Subgroup.mem_subgroupOf.mp (h.mpr (iff_of_false h2 h1))
  have hnormal : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T := fun r hr t ht => by
    have hN := Subgroup.normal_of_index_eq_two hidx'
    exact Subgroup.mem_subgroupOf.mp (hN.conj_mem ⟨t, hTR ht⟩ (Subgroup.mem_subgroupOf.mpr ht)
      ⟨r, hr⟩)
  obtain ⟨⟨r₀, hr₀R⟩, hr₀T⟩ : ∃ x : R, x ∉ T.subgroupOf R := by
    by_contra h
    push Not at h
    have htop : T.subgroupOf R = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, Subgroup.index_top] at hidx'
    omega
  have hr₀T' : r₀ ∉ T := fun h => hr₀T (Subgroup.mem_subgroupOf.mpr h)
  have hex : ∃ k, ∃ r ∈ R, r ∉ T ∧ r ^ (2 ^ k) = 1 := by
    obtain ⟨n, hn⟩ := hR2 ⟨r₀, hr₀R⟩
    exact ⟨n, r₀, hr₀R, hr₀T', by simpa using congrArg Subtype.val hn⟩
  obtain ⟨r₁, hr₁R, hr₁T, hr₁k⟩ := Nat.find_spec hex
  have hmin : ∀ k' < Nat.find hex, ¬ ∃ r ∈ R, r ∉ T ∧ r ^ (2 ^ k') = 1 :=
    fun k' h => Nat.find_min hex h
  have hk2 : 2 ≤ Nat.find hex := by
    by_contra hlt
    push Not at hlt
    interval_cases h : Nat.find hex
    · rw [pow_zero, pow_one] at hr₁k
      exact hr₁T (hr₁k ▸ T.one_mem)
    · rw [pow_one] at hr₁k
      exact hnoinv r₁ hr₁R hr₁T hr₁k
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 2 := ⟨Nat.find hex - 2, by omega⟩
  rw [hj] at hr₁k hmin
  have hne1 : ∀ r ∈ R, r ∉ T → r ^ (2 ^ (j + 1)) ≠ 1 := fun r hr hrT h =>
    hmin (j + 1) (by omega) ⟨r, hr, hrT, h⟩
  have hpowT : ∀ r ∈ R, r ^ (2 ^ (j + 1)) ∈ T := fun r hr => by
    rw [pow_succ', pow_mul, sq]
    exact T.pow_mem (hsq r hr) _
  have hθ₀U : r₁ ^ (2 ^ (j + 1)) ∈ AschbacherTheorem3.omegaOne T := by
    refine mem_omegaOne (hpowT r₁ hr₁R) ?_
    rw [← pow_mul, ← pow_succ]
    exact hr₁k
  have hθ₀1 := hne1 r₁ hr₁R hr₁T
  have hsurj : ∀ u ∈ AschbacherTheorem3.omegaOne T, u ≠ 1 →
      ∃ t ∈ T, (t * r₀) ^ (2 ^ (j + 1)) = u := by
    intro u hu hu1
    obtain ⟨m, ⟨hmR, hmT⟩, hmu⟩ := htrans _ hθ₀U hθ₀1 u hu hu1
    have hrR : m⁻¹ * r₁ * m ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmR) r₁).mp hr₁R
      simpa using this
    have hrT : m⁻¹ * r₁ * m ∉ T := by
      intro h
      apply hr₁T
      have := (Subgroup.mem_normalizer_iff.mp hmT _).mp h
      simpa [mul_assoc] using this
    refine ⟨(m⁻¹ * r₁ * m) * r₀⁻¹, hmul _ hrR _ hr₀R hrT hr₀T', ?_⟩
    rw [inv_mul_cancel_right, ← hmu]
    have := conj_pow (a := m⁻¹) (b := r₁) (i := 2 ^ (j + 1))
    rw [inv_inv] at this
    exact this
  have hg1 : ∀ t ∈ T, (t * r₀) ^ (2 ^ (j + 1)) ≠ 1 := fun t ht => by
    refine hne1 _ (R.mul_mem (hTR ht) hr₀R) fun h => hr₀T' ?_
    have : r₀ = t⁻¹ * (t * r₀) := by group
    rw [this]
    exact T.mul_mem (T.inv_mem ht) h
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, hu₁₂⟩ := AschbacherTheorem3.exists_two_ne_one hU4
  have hel := isElemAbelian_omegaOne hTab
  have hu₃ : u₁ * u₂ ∈ AschbacherTheorem3.omegaOne T :=
    (AschbacherTheorem3.omegaOne T).mul_mem hu₁ hu₂
  have hu₃1 : u₁ * u₂ ≠ 1 := by
    intro h
    apply hu₁₂
    have h1 : u₁ * u₁ = 1 := by rw [← sq]; exact hel.2 u₁ hu₁
    calc u₂ = u₁⁻¹ * (u₁ * u₂) := by group
      _ = u₁ := by rw [h, mul_one, inv_eq_of_mul_eq_one_right h1]
  obtain ⟨t₁, ht₁, ht₁u⟩ := hsurj u₁ hu₁ hu₁1
  obtain ⟨t₂, ht₂, ht₂u⟩ := hsurj u₂ hu₂ hu₂1
  obtain ⟨t₃, ht₃, ht₃u⟩ := hsurj _ hu₃ hu₃1
  have hn : ∀ t ∈ T, r₀ * t * r₀⁻¹ ∈ T := fun t ht => hnormal r₀ hr₀R t ht
  have hr₀2 : r₀ * r₀ ∈ T := hsq r₀ hr₀R
  have hpT : ∀ t ∈ T, (t * r₀) ^ (2 ^ (j + 1)) ∈ T := fun t ht =>
    hpowT _ (R.mul_mem (hTR ht) hr₀R)
  set Y := ((1 : G) * r₀) ^ (2 ^ (j + 1)) with hYdef
  have hYT : Y ∈ T := hpT 1 T.one_mem
  have h12 := T.mul_mem ht₁ ht₂
  have e2 := pow_mul_mul_eq hcomm hn hr₀2 j ht₁ ht₂
  rw [ht₁u, ht₂u] at e2
  set a := t₃ * (t₁ * t₂)⁻¹ with hadef
  have ha : a ∈ T := T.mul_mem ht₃ (T.inv_mem h12)
  have e1 := pow_mul_mul_eq hcomm hn hr₀2 j ha h12
  have hat : a * (t₁ * t₂) * r₀ = t₃ * r₀ := by rw [hadef]; group
  rw [hat, ht₃u, e2] at e1
  set X := (t₁ * t₂ * r₀) ^ (2 ^ (j + 1)) with hXdef
  have hXT : X ∈ T := hpT _ h12
  have hgaT := hpT a ha
  have hga : (a * r₀) ^ (2 ^ (j + 1)) = Y * Y := by
    have h1 : X * (a * r₀) ^ (2 ^ (j + 1)) = X * (Y * Y) := by
      rw [← hcomm _ hgaT _ hXT, e1, mul_assoc]
    exact mul_left_cancel h1
  have e4 := pow_mul_mul_eq hcomm hn hr₀2 j ha (T.inv_mem ha)
  have haa : a * a⁻¹ * r₀ = 1 * r₀ := by group
  rw [haa, hga] at e4
  have h5 : (a⁻¹ * r₀) ^ (2 ^ (j + 1)) = 1 := by
    have h6 : Y * Y * (a⁻¹ * r₀) ^ (2 ^ (j + 1)) = Y * Y * 1 := by
      rw [e4, mul_one]
    exact mul_left_cancel h6
  exact hg1 _ (T.inv_mem ha) h5

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
