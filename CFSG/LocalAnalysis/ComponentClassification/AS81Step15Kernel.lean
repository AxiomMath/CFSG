module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Plane

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

section FourGroup

variable {R : Subgroup G}

theorem eq_or_of_card_four (hR : Nat.card R = 4) {r x : G} (hr : r ∈ R) (hx : x ∈ R)
    (hr1 : r ≠ 1) (hx1 : x ≠ 1) (hrx : r ≠ x) (hx2 : x * x = 1) {z : G} (hz : z ∈ R) :
    z = 1 ∨ z = r ∨ z = x ∨ z = r * x := by
  have hsub : ({1, r, x, r * x} : Set G) ⊆ R := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact hr
    · exact hx
    · exact R.mul_mem hr hx
  have hrx1 : r * x ≠ 1 := fun h => hrx (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hx2])
  have h3 : x ≠ r * x := fun h => hr1 (mul_eq_right.mp h.symm)
  have h2 : r ∉ ({x, r * x} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hrx, fun h => hx1 (mul_eq_left.mp h.symm)⟩
  have h1 : (1 : G) ∉ ({r, x, r * x} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hr1, Ne.symm hx1, Ne.symm hrx1⟩
  have hcard : ({1, r, x, r * x} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  have hRn : (R : Set G).ncard = 4 := by
    rw [← hR, ← Nat.card_coe_set_eq]
    rfl
  have heq : ({1, r, x, r * x} : Set G) = R :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hRn]) (Set.toFinite _)
  have hz' : z ∈ ({1, r, x, r * x} : Set G) := heq ▸ hz
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz'

theorem conj_conj_eq_of_fpf (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4) {k : G}
    (hkR : k ∈ normalizer (R : Set G)) (hfpf : ∀ s ∈ R, s ≠ 1 → k * s * k⁻¹ ≠ s)
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    k * (k * r * k⁻¹) * k⁻¹ = r * (k * r * k⁻¹) := by
  have hcommR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ R, a * a = 1 := fun a ha => by rw [← sq]; exact hRe.2 a ha
  obtain ⟨x, hxdef⟩ : ∃ x, x = k * r * k⁻¹ := ⟨_, rfl⟩
  rw [← hxdef]
  have hxR : x ∈ R := by rw [hxdef]; exact (mem_normalizer_iff.mp hkR r).mp hr
  have hx1 : x ≠ 1 := fun h => hr1 (conj_eq_one_iff.mp (by rw [← hxdef]; exact h))
  have hxr : x ≠ r := by rw [hxdef]; exact hfpf r hr hr1
  obtain ⟨y, hydef⟩ : ∃ y, y = k * x * k⁻¹ := ⟨_, rfl⟩
  rw [← hydef]
  have hyR : y ∈ R := by rw [hydef]; exact (mem_normalizer_iff.mp hkR x).mp hxR
  have hy1 : y ≠ 1 := fun h => hx1 (conj_eq_one_iff.mp (by rw [← hydef]; exact h))
  have hyx : y ≠ x := by rw [hydef]; exact hfpf x hxR hx1
  have hyr : y ≠ r := by
    intro hyr
    have hrx : r * x ∈ R := R.mul_mem hr hxR
    have hrx1 : r * x ≠ 1 := fun h => hxr (by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hsq r hr)])
    apply hfpf (r * x) hrx hrx1
    calc k * (r * x) * k⁻¹ = (k * r * k⁻¹) * (k * x * k⁻¹) := by group
      _ = x * r := by rw [← hxdef, ← hydef, hyr]
      _ = r * x := hcommR x hxR r hr
  rcases eq_or_of_card_four hR4 hr hxR hr1 hx1 hxr.symm (hsq x hxR) hyR with h | h | h | h
  · exact absurd h hy1
  · exact absurd h hyr
  · exact absurd h hyx
  · exact h

end FourGroup

structure PointsData (R E H : Subgroup G) : Prop where
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  H_le : H ≤ E
  R_le : R ≤ E
  inf_H : ∀ Q ∈ pointsIn R E, Q ⊓ H = ⊥
  cover : ∀ e ∈ E, e ∉ H → ∃ Q ∈ pointsIn R E, e ∈ Q
  disj : ∀ Q₁ ∈ pointsIn R E, ∀ Q₂ ∈ pointsIn R E, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥
  eq_mul : ∀ e ∈ E, ∃ h ∈ H, ∃ r ∈ R, e = h * r
  ne_one : ∃ h ∈ H, h ≠ 1
  elem : IsElemAbelian 2 R
  card : Nat.card R = 4

namespace PointsData

variable {R E H : Subgroup G} (hD : PointsData R E H)
include hD

omit [Finite G] in
theorem self_mem : R ∈ pointsIn R E := self_mem_pointsIn hD.R_le

omit [Finite G] in
theorem exists_ne_one : ∃ r ∈ R, r ≠ 1 := by
  have hne : R ≠ ⊥ := fun h => by
    have := hD.card
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  exact ⟨r, hr, fun h => hr1 (Subtype.ext h)⟩

omit [Finite G] in
theorem mem_centralizer_of_fix {k : G} (hkE : k ∈ normalizer (E : Set G))
    (hk : ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) {r₀ : G} (hr₀ : r₀ ∈ R)
    (hr₀1 : r₀ ≠ 1) (hfix : k * r₀ * k⁻¹ = r₀) : k ∈ centralizer (E : Set G) := by
  have hRpt := hD.self_mem
  have hkR := hk R hRpt
  have hnotH : ∀ r ∈ R, r ≠ 1 → r ∉ H := fun r hr hr1 hrH => hr1 (by
    have h : r ∈ R ⊓ H := ⟨hr, hrH⟩
    rwa [hD.inf_H R hRpt, mem_bot] at h)
  have hkH : ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro h hh
    by_contra hnot
    have hE : k * h * k⁻¹ ∈ E := (mem_normalizer_iff.mp hkE h).mp (hD.H_le hh)
    obtain ⟨Q, hQ, hmem⟩ := hD.cover _ hE hnot
    have hhQ : h ∈ Q := (mem_normalizer_iff.mp (hk Q hQ) h).mpr hmem
    have h1 : h ∈ Q ⊓ H := ⟨hhQ, hh⟩
    rw [hD.inf_H Q hQ, mem_bot] at h1
    apply hnot
    rw [h1, mul_one, mul_inv_cancel]
    exact H.one_mem
  have hkH' : ∀ h ∈ H, k * h * k⁻¹ = h := by
    intro h hh
    by_cases hh1 : h = 1
    · rw [hh1, mul_one, mul_inv_cancel]
    have he : r₀ * h ∈ E := E.mul_mem (hD.R_le hr₀) (hD.H_le hh)
    have heH : r₀ * h ∉ H := fun hrh => hnotH r₀ hr₀ hr₀1 (by
      have := H.mul_mem hrh (H.inv_mem hh)
      rwa [mul_inv_cancel_right] at this)
    obtain ⟨Q, hQ, hmem⟩ := hD.cover _ he heH
    have hk' : k * (r₀ * h) * k⁻¹ ∈ Q := (mem_normalizer_iff.mp (hk Q hQ) _).mp hmem
    have hk'' : k * (r₀ * h) * k⁻¹ = r₀ * (k * h * k⁻¹) := by
      calc k * (r₀ * h) * k⁻¹ = (k * r₀ * k⁻¹) * (k * h * k⁻¹) := by group
        _ = r₀ * (k * h * k⁻¹) := by rw [hfix]
    rw [hk''] at hk'
    have hdiff : h⁻¹ * (k * h * k⁻¹) ∈ Q ⊓ H := by
      refine ⟨?_, H.mul_mem (H.inv_mem hh) (hkH h hh)⟩
      have := Q.mul_mem (Q.inv_mem hmem) hk'
      have e : (r₀ * h)⁻¹ * (r₀ * (k * h * k⁻¹)) = h⁻¹ * (k * h * k⁻¹) := by group
      rwa [e] at this
    rw [hD.inf_H Q hQ, mem_bot, inv_mul_eq_one] at hdiff
    exact hdiff.symm
  obtain ⟨h₀, hh₀, hh₀1⟩ := hD.ne_one
  have hkR' : ∀ r ∈ R, k * r * k⁻¹ = r := by
    intro r hr
    by_cases hr1 : r = 1
    · rw [hr1, mul_one, mul_inv_cancel]
    have he : r * h₀ ∈ E := E.mul_mem (hD.R_le hr) (hD.H_le hh₀)
    have heH : r * h₀ ∉ H := fun hrh => hnotH r hr hr1 (by
      have := H.mul_mem hrh (H.inv_mem hh₀)
      rwa [mul_inv_cancel_right] at this)
    obtain ⟨Q, hQ, hmem⟩ := hD.cover _ he heH
    have hQR : Q ≠ R := by
      intro hQR'
      apply hh₀1
      have hrQ : r ∈ Q := hQR' ▸ hr
      have h1 : h₀ ∈ Q ⊓ H := ⟨by simpa using Q.mul_mem (Q.inv_mem hrQ) hmem, hh₀⟩
      rwa [hD.inf_H Q hQ, mem_bot] at h1
    have hk' : k * (r * h₀) * k⁻¹ ∈ Q := (mem_normalizer_iff.mp (hk Q hQ) _).mp hmem
    have hk'' : k * (r * h₀) * k⁻¹ = (k * r * k⁻¹) * h₀ := by
      calc k * (r * h₀) * k⁻¹ = (k * r * k⁻¹) * (k * h₀ * k⁻¹) := by group
        _ = (k * r * k⁻¹) * h₀ := by rw [hkH' h₀ hh₀]
    rw [hk''] at hk'
    have hkrR : k * r * k⁻¹ ∈ R := (mem_normalizer_iff.mp hkR r).mp hr
    have hdiff : (k * r * k⁻¹) * r⁻¹ ∈ Q ⊓ R := by
      refine ⟨?_, R.mul_mem hkrR (R.inv_mem hr)⟩
      have := Q.mul_mem hk' (Q.inv_mem hmem)
      have e : (k * r * k⁻¹) * h₀ * (r * h₀)⁻¹ = (k * r * k⁻¹) * r⁻¹ := by group
      rwa [e] at this
    rw [hD.disj Q hQ R hRpt hQR, mem_bot, mul_inv_eq_one] at hdiff
    exact hdiff
  rw [mem_centralizer_iff]
  intro e he
  obtain ⟨h, hh, r, hr, rfl⟩ := hD.eq_mul e he
  have hke : k * (h * r) * k⁻¹ = h * r := by
    calc k * (h * r) * k⁻¹ = (k * h * k⁻¹) * (k * r * k⁻¹) := by group
      _ = h * r := by rw [hkH' h hh, hkR' r hr]
  exact (mul_inv_eq_iff_eq_mul.mp hke).symm

omit [Finite G] in
theorem fpf {k : G} (hkE : k ∈ normalizer (E : Set G))
    (hk : ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) (hkC : k ∉ centralizer (E : Set G)) :
    ∀ s ∈ R, s ≠ 1 → k * s * k⁻¹ ≠ s := fun _ hs hs1 hfix =>
  hkC (hD.mem_centralizer_of_fix hkE hk hs hs1 hfix)

theorem pow_three_mem_centralizer {k : G} (hkE : k ∈ normalizer (E : Set G))
    (hk : ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) : k ^ 3 ∈ centralizer (E : Set G) := by
  by_cases hkC : k ∈ centralizer (E : Set G)
  · exact pow_mem hkC 3
  have hkR := hk R hD.self_mem
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have h1 := conj_conj_eq_of_fpf hD.elem hD.card hkR (hD.fpf hkE hk hkC) hr hr1
  have hxR : k * r * k⁻¹ ∈ R := (mem_normalizer_iff.mp hkR r).mp hr
  have hcomm : r * (k * r * k⁻¹) = (k * r * k⁻¹) * r :=
    congrArg Subtype.val (hD.elem.1.is_comm.comm ⟨r, hr⟩ ⟨_, hxR⟩)
  have hsq : (k * r * k⁻¹) * (k * r * k⁻¹) = 1 := by rw [← sq]; exact hD.elem.2 _ hxR
  have hfin : ∀ z : G, z * z = 1 → r * z = z * r → z * (r * z) = r := fun z hz2 hzr => by
    rw [← mul_assoc, ← hzr, mul_assoc, hz2, mul_one]
  have h3 : k ^ 3 * r * (k ^ 3)⁻¹ = r := by
    calc k ^ 3 * r * (k ^ 3)⁻¹ = k * (k * (k * r * k⁻¹) * k⁻¹) * k⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
          group
      _ = k * (r * (k * r * k⁻¹)) * k⁻¹ := by rw [h1]
      _ = (k * r * k⁻¹) * (k * (k * r * k⁻¹) * k⁻¹) := by group
      _ = (k * r * k⁻¹) * (r * (k * r * k⁻¹)) := by rw [h1]
      _ = r := hfin _ hsq hcomm
  exact hD.mem_centralizer_of_fix (pow_mem hkE 3) (fun Q hQ => pow_mem (hk Q hQ) 3) hr hr1 h3

theorem mem_centralizer_of_pow_eq_one {k : G} (hkE : k ∈ normalizer (E : Set G))
    (hk : ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) {n : ℕ} (hkn : k ^ 2 ^ n = 1) :
    k ∈ centralizer (E : Set G) := by
  have hk3 := hD.pow_three_mem_centralizer hkE hk
  have hcop : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
  have hb : ((Nat.gcd 3 (2 ^ n) : ℕ) : ℤ) =
      ((3 : ℕ) : ℤ) * Nat.gcdA 3 (2 ^ n) + ((2 ^ n : ℕ) : ℤ) * Nat.gcdB 3 (2 ^ n) :=
    Nat.gcd_eq_gcd_ab 3 (2 ^ n)
  rw [hcop, Nat.cast_one] at hb
  have hk' : k = (k ^ 3) ^ Nat.gcdA 3 (2 ^ n) := by
    calc k = k ^ (1 : ℤ) := (zpow_one k).symm
      _ = k ^ (((3 : ℕ) : ℤ) * Nat.gcdA 3 (2 ^ n) + ((2 ^ n : ℕ) : ℤ) * Nat.gcdB 3 (2 ^ n)) := by
          rw [← hb]
      _ = (k ^ 3) ^ Nat.gcdA 3 (2 ^ n) * (k ^ 2 ^ n) ^ Nat.gcdB 3 (2 ^ n) := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (k ^ 3) ^ Nat.gcdA 3 (2 ^ n) := by rw [hkn, one_zpow, mul_one]
  rw [hk']
  exact zpow_mem hk3 _

theorem mem_or_mem_of_not_mem {k₁ k₂ : G} (hk₁E : k₁ ∈ normalizer (E : Set G))
    (hk₁ : ∀ Q ∈ pointsIn R E, k₁ ∈ normalizer (Q : Set G)) (hk₂E : k₂ ∈ normalizer (E : Set G))
    (hk₂ : ∀ Q ∈ pointsIn R E, k₂ ∈ normalizer (Q : Set G))
    (h₁ : k₁ ∉ centralizer (E : Set G)) (h₂ : k₂ ∉ centralizer (E : Set G)) :
    k₂⁻¹ * k₁ ∈ centralizer (E : Set G) ∨ k₂ * k₁ ∈ centralizer (E : Set G) := by
  have hkR₁ := hk₁ R hD.self_mem
  have hkR₂ := hk₂ R hD.self_mem
  have hfpf₁ := hD.fpf hk₁E hk₁ h₁
  have hfpf₂ := hD.fpf hk₂E hk₂ h₂
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have hx₂R : k₂ * r * k₂⁻¹ ∈ R := (mem_normalizer_iff.mp hkR₂ r).mp hr
  have hx₂1 : k₂ * r * k₂⁻¹ ≠ 1 := fun h => hr1 (conj_eq_one_iff.mp h)
  have hx₂r : k₂ * r * k₂⁻¹ ≠ r := hfpf₂ r hr hr1
  have hx₂2 : (k₂ * r * k₂⁻¹) * (k₂ * r * k₂⁻¹) = 1 := by rw [← sq]; exact hD.elem.2 _ hx₂R
  have hx₁R : k₁ * r * k₁⁻¹ ∈ R := (mem_normalizer_iff.mp hkR₁ r).mp hr
  have hx₁1 : k₁ * r * k₁⁻¹ ≠ 1 := fun h => hr1 (conj_eq_one_iff.mp h)
  have hx₁r : k₁ * r * k₁⁻¹ ≠ r := hfpf₁ r hr hr1
  rcases eq_or_of_card_four hD.card hr hx₂R hr1 hx₂1 hx₂r.symm hx₂2 hx₁R with h | h | h | h
  · exact absurd h hx₁1
  · exact absurd h hx₁r
  · left
    refine hD.mem_centralizer_of_fix (mul_mem (inv_mem hk₂E) hk₁E)
      (fun Q hQ => mul_mem (inv_mem (hk₂ Q hQ)) (hk₁ Q hQ)) hr hr1 ?_
    calc k₂⁻¹ * k₁ * r * (k₂⁻¹ * k₁)⁻¹ = k₂⁻¹ * (k₁ * r * k₁⁻¹) * k₂ := by group
      _ = k₂⁻¹ * (k₂ * r * k₂⁻¹) * k₂ := by rw [h]
      _ = r := by group
  · right
    refine hD.mem_centralizer_of_fix (mul_mem hk₂E hk₁E)
      (fun Q hQ => mul_mem (hk₂ Q hQ) (hk₁ Q hQ)) hr hr1 ?_
    have h3 := conj_conj_eq_of_fpf hD.elem hD.card hkR₂ hfpf₂ hr hr1
    have hcomm : r * (k₂ * r * k₂⁻¹) = (k₂ * r * k₂⁻¹) * r :=
      congrArg Subtype.val (hD.elem.1.is_comm.comm ⟨r, hr⟩ ⟨_, hx₂R⟩)
    have hfin : ∀ z : G, z * z = 1 → r * z = z * r → z * (r * z) = r := fun z hz2 hzr => by
      rw [← mul_assoc, ← hzr, mul_assoc, hz2, mul_one]
    calc k₂ * k₁ * r * (k₂ * k₁)⁻¹ = k₂ * (k₁ * r * k₁⁻¹) * k₂⁻¹ := by group
      _ = k₂ * (r * (k₂ * r * k₂⁻¹)) * k₂⁻¹ := by rw [h]
      _ = (k₂ * r * k₂⁻¹) * (k₂ * (k₂ * r * k₂⁻¹) * k₂⁻¹) := by group
      _ = (k₂ * r * k₂⁻¹) * (r * (k₂ * r * k₂⁻¹)) := by rw [h3]
      _ = r := hfin _ hx₂2 hcomm

end PointsData

structure TranslationData (R E : Subgroup G) (T : Subgroup (Equiv.Perm ↥(pointsIn R E))) :
    Prop where
  card_points : Nat.card (pointsIn R E) = 16
  two_trans : ∀ p₁ p₂ q₁ q₂ : ↥(pointsIn R E), p₁ ≠ p₂ → q₁ ≠ q₂ →
    ∃ n : ↥(normalizer (E : Set G)), pointsAction R E n p₁ = q₁ ∧ pointsAction R E n p₂ = q₂
  le_range : T ≤ (pointsAction R E).range
  range_le : (pointsAction R E).range ≤ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E)))
  elem : IsElemAbelian 2 T
  card : Nat.card T = 16
  trans : ∀ p q : ↥(pointsIn R E), ∃ t ∈ T, t p = q

namespace TranslationData

variable {R E : Subgroup G} {T : Subgroup (Equiv.Perm ↥(pointsIn R E))} (hT : TranslationData R E T)
include hT

omit [Finite G] in
theorem eq_one_of_apply_eq {t : Equiv.Perm ↥(pointsIn R E)} (ht : t ∈ T) {p : ↥(pointsIn R E)}
    (hp : t p = p) : t = 1 := by
  have : Finite ↥(pointsIn R E) := Nat.finite_of_card_ne_zero (by rw [hT.card_points]; omega)
  have : Finite ↥T := Nat.finite_of_card_ne_zero (by rw [hT.card]; omega)
  set f : ↥T → ↥(pointsIn R E) := fun u => (u : Equiv.Perm ↥(pointsIn R E)) p with hf
  have hsurj : Function.Surjective f := fun q => by
    obtain ⟨u, hu, huq⟩ := hT.trans p q
    exact ⟨⟨u, hu⟩, huq⟩
  have hinj := (hsurj.bijective_of_nat_card_le (by rw [hT.card, hT.card_points])).1
  have h : f ⟨t, ht⟩ = f 1 := by
    simp only [hf, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    exact hp
  exact congrArg Subtype.val (hinj h)

omit [Finite G] in
theorem exists_conj_eq (hRE : R ≤ E) {t₁ t₂ : Equiv.Perm ↥(pointsIn R E)} (ht₁ : t₁ ∈ T)
    (ht₂ : t₂ ∈ T) (ht₁1 : t₁ ≠ 1) (ht₂1 : t₂ ≠ 1) :
    ∃ m : ↥(normalizer (E : Set G)),
      pointsAction R E m * t₁ * (pointsAction R E m)⁻¹ = t₂ := by
  set p₀ : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hRE⟩
  have h₁ : t₁ p₀ ≠ p₀ := fun h => ht₁1 (hT.eq_one_of_apply_eq ht₁ h)
  have h₂ : t₂ p₀ ≠ p₀ := fun h => ht₂1 (hT.eq_one_of_apply_eq ht₂ h)
  obtain ⟨m, hm₁, hm₂⟩ := hT.two_trans p₀ (t₁ p₀) p₀ (t₂ p₀) h₁.symm h₂.symm
  refine ⟨m, ?_⟩
  have hmem : pointsAction R E m * t₁ * (pointsAction R E m)⁻¹ ∈ T :=
    (mem_normalizer_iff.mp (hT.range_le ⟨m, rfl⟩) t₁).mp ht₁
  have hfix : (t₂⁻¹ * (pointsAction R E m * t₁ * (pointsAction R E m)⁻¹)) p₀ = p₀ := by
    have hinv : (pointsAction R E m)⁻¹ p₀ = p₀ := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hm₁.symm
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hm₂,
      Equiv.Perm.inv_eq_iff_eq]
  have := hT.eq_one_of_apply_eq (T.mul_mem (T.inv_mem ht₂) hmem) hfix
  rw [inv_mul_eq_one] at this
  exact this.symm

omit [Finite G] in
theorem exists_two : ∃ t₁ ∈ T, ∃ t₂ ∈ T, t₁ ≠ 1 ∧ t₂ ≠ 1 ∧ t₁ * t₂ ≠ 1 := by
  have : Finite ↥T := Nat.finite_of_card_ne_zero (by rw [hT.card]; omega)
  obtain ⟨t₁, ht₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := T)).mp (fun h => by
    have := hT.card
    rw [h, Subgroup.card_bot] at this
    omega)
  have hle : zpowers (t₁ : Equiv.Perm ↥(pointsIn R E)) ≤ T := zpowers_le.mpr t₁.2
  have hne : zpowers (t₁ : Equiv.Perm ↥(pointsIn R E)) ≠ T := by
    intro h
    have h2 : (t₁ : Equiv.Perm ↥(pointsIn R E)) ^ 2 = 1 := hT.elem.2 _ t₁.2
    have hcard : Nat.card (zpowers (t₁ : Equiv.Perm ↥(pointsIn R E))) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) h2
    rw [h, hT.card] at hcard
    omega
  obtain ⟨t₂, ht₂T, ht₂⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hle hne)
  refine ⟨t₁, t₁.2, t₂, ht₂T, fun h => ht₁1 (Subtype.ext h), fun h => ht₂ (h ▸ one_mem _),
    fun h => ht₂ ?_⟩
  rw [eq_inv_of_mul_eq_one_right h]
  exact inv_mem (mem_zpowers _)

end TranslationData

section Kernel

variable {R E H : Subgroup G} {T : Subgroup (Equiv.Perm ↥(pointsIn R E))}

omit [Finite G] in
theorem mem_normalizer_of_pointsAction_eq_one {k : ↥(normalizer (E : Set G))}
    (hk : pointsAction R E k = 1) :
    ∀ Q ∈ pointsIn R E, (k : G) ∈ normalizer (Q : Set G) := by
  intro Q hQ
  have h := congrArg (fun σ : Equiv.Perm ↥(pointsIn R E) => ((σ ⟨Q, hQ⟩ : ↥(pointsIn R E)) :
    Subgroup G)) hk
  simp only [coe_pointsAction_apply, Equiv.Perm.coe_one, id_eq] at h
  exact (normalizer (Q : Set G)).inv_mem_iff.mp ((rightConjugate_eq_self_iff Q _).mp h)

omit [Finite G] in
theorem pointsAction_eq_one_of_mem_centralizer {c : ↥(normalizer (E : Set G))}
    (hc : (c : G) ∈ centralizer (E : Set G)) : pointsAction R E c = 1 := by
  refine Equiv.ext fun Q => Subtype.ext ?_
  rw [coe_pointsAction_apply, Equiv.Perm.coe_one, id_eq, rightConjugate_eq_self_iff]
  refine (normalizer (Q : Set G)).inv_mem (Subgroup.centralizer_le_normalizer _ ?_)
  exact mem_centralizer_iff.mpr fun q hq => mem_centralizer_iff.mp hc q (Q.2.1 hq)

omit [Finite G] in
theorem conj_mem_centralizer {n c : G} (hn : n ∈ normalizer (E : Set G))
    (hc : c ∈ centralizer (E : Set G)) : n * c * n⁻¹ ∈ centralizer (E : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro e he
  have he' : n⁻¹ * e * n ∈ E := by
    have := (mem_normalizer_iff.mp (inv_mem hn) e).mp he
    simpa using this
  have h := hc _ he'
  calc e * (n * c * n⁻¹) = n * ((n⁻¹ * e * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * e * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * e := by group

abbrev centralizerIn (E : Subgroup G) : Subgroup ↥(normalizer (E : Set G)) :=
  (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G))

omit [Finite G] in
theorem centralizerIn_normal (E : Subgroup G) : (centralizerIn E).Normal :=
  ⟨fun c hc n => by
    simp only [mem_subgroupOf, coe_mul, coe_inv] at hc ⊢
    exact conj_mem_centralizer n.2 hc⟩

theorem commutator_mem_of_mem_translations (hD : PointsData R E H) (hT : TranslationData R E T)
    {y : ↥(normalizer (E : Set G))} (hy : pointsAction R E y ∈ T)
    {k : ↥(normalizer (E : Set G))} (hk : pointsAction R E k = 1) :
    y * k * y⁻¹ * k⁻¹ ∈ centralizerIn E := by
  have := centralizerIn_normal E
  set ρ := pointsAction R E with hρ
  set C := centralizerIn E with hC
  set π := QuotientGroup.mk' C with hπ
  have hπ1 : ∀ x, π x = 1 ↔ x ∈ C := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerN : ∀ x : ↥(normalizer (E : Set G)), ρ x = 1 →
      ∀ Q ∈ pointsIn R E, (x : G) ∈ normalizer (Q : Set G) :=
    fun x hx => mem_normalizer_of_pointsAction_eq_one hx
  by_cases hall : ∀ x : ↥(normalizer (E : Set G)), ρ x = 1 → x ∈ C
  · have hkC := hall k hk
    have h1 : y * k * y⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem k hkC y
    exact C.mul_mem h1 (C.inv_mem hkC)
  push Not at hall
  obtain ⟨k₀, hk₀, hk₀C⟩ := hall
  have hk₀C' : (k₀ : G) ∉ centralizer (E : Set G) := hk₀C
  have hthree : ∀ x : ↥(normalizer (E : Set G)), ρ x = 1 →
      π x = 1 ∨ π x = π k₀ ∨ π x = (π k₀)⁻¹ := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact Or.inl ((hπ1 x).mpr hxC)
    rcases hD.mem_or_mem_of_not_mem x.2 (hkerN x hx) k₀.2 (hkerN k₀ hk₀) hxC hk₀C' with h | h
    · right; left
      have h' : k₀⁻¹ * x ∈ C := h
      have := (hπ1 _).mpr h'
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    · right; right
      have h' : k₀ * x ∈ C := h
      have := (hπ1 _).mpr h'
      rw [map_mul] at this
      exact eq_inv_of_mul_eq_one_right this
  have hk₀1 : π k₀ ≠ 1 := fun h => hk₀C ((hπ1 k₀).mp h)
  have hconj : ∀ x : ↥(normalizer (E : Set G)),
      π x * π k₀ * (π x)⁻¹ = π k₀ ∨ π x * π k₀ * (π x)⁻¹ = (π k₀)⁻¹ := by
    intro x
    have hx : ρ (x * k₀ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, hk₀, mul_one, map_inv, mul_inv_cancel]
    have hthree' := hthree _ hx
    rw [map_mul, map_mul, map_inv] at hthree'
    rcases hthree' with h | h | h
    · exact absurd (conj_eq_one_iff.mp h) hk₀1
    · exact Or.inl h
    · exact Or.inr h
  have hpos_conj : ∀ x m : ↥(normalizer (E : Set G)), Commute (π x) (π k₀) →
      Commute (π (m * x * m⁻¹)) (π k₀) := by
    intro x m hx
    rw [map_mul, map_mul, map_inv]
    have hm : Commute (π x) ((π m)⁻¹ * π k₀ * π m) := by
      rcases hconj m⁻¹ with h | h
      · rw [map_inv, inv_inv] at h
        rw [h]
        exact hx
      · rw [map_inv, inv_inv] at h
        rw [h]
        exact hx.inv_right
    show π m * π x * (π m)⁻¹ * π k₀ = π k₀ * (π m * π x * (π m)⁻¹)
    calc π m * π x * (π m)⁻¹ * π k₀ = π m * (π x * ((π m)⁻¹ * π k₀ * π m)) * (π m)⁻¹ := by group
      _ = π m * (((π m)⁻¹ * π k₀ * π m) * π x) * (π m)⁻¹ := by rw [hm.eq]
      _ = π k₀ * (π m * π x * (π m)⁻¹) := by group
  obtain ⟨t₁, ht₁, t₂, ht₂, ht₁1, ht₂1, ht₁₂⟩ := hT.exists_two
  obtain ⟨y₁, hy₁⟩ := hT.le_range ht₁
  obtain ⟨y₂, hy₂⟩ := hT.le_range ht₂
  have hneg : ∀ x : ↥(normalizer (E : Set G)), ¬ Commute (π x) (π k₀) →
      π x * π k₀ * (π x)⁻¹ = (π k₀)⁻¹ := by
    intro x hx
    rcases hconj x with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.mp h) hx
    · exact h
  obtain ⟨y₀, hy₀T, hy₀1, hy₀⟩ : ∃ y₀ : ↥(normalizer (E : Set G)), ρ y₀ ∈ T ∧ ρ y₀ ≠ 1 ∧
      Commute (π y₀) (π k₀) := by
    by_cases h₁ : Commute (π y₁) (π k₀)
    · exact ⟨y₁, hy₁ ▸ ht₁, hy₁ ▸ ht₁1, h₁⟩
    by_cases h₂ : Commute (π y₂) (π k₀)
    · exact ⟨y₂, hy₂ ▸ ht₂, hy₂ ▸ ht₂1, h₂⟩
    refine ⟨y₁ * y₂, ?_, ?_, ?_⟩
    · rw [map_mul, hy₁, hy₂]
      exact T.mul_mem ht₁ ht₂
    · rw [map_mul, hy₁, hy₂]
      exact ht₁₂
    · have e₁ := hneg y₁ h₁
      have e₂ := hneg y₂ h₂
      rw [map_mul]
      show π y₁ * π y₂ * π k₀ = π k₀ * (π y₁ * π y₂)
      have : π y₁ * π y₂ * π k₀ * (π y₁ * π y₂)⁻¹ = π k₀ := by
        calc π y₁ * π y₂ * π k₀ * (π y₁ * π y₂)⁻¹
            = π y₁ * (π y₂ * π k₀ * (π y₂)⁻¹) * (π y₁)⁻¹ := by group
          _ = π y₁ * (π k₀)⁻¹ * (π y₁)⁻¹ := by rw [e₂]
          _ = (π y₁ * π k₀ * (π y₁)⁻¹)⁻¹ := by group
          _ = π k₀ := by rw [e₁, inv_inv]
      calc π y₁ * π y₂ * π k₀ = π y₁ * π y₂ * π k₀ * (π y₁ * π y₂)⁻¹ * (π y₁ * π y₂) := by
            group
        _ = π k₀ * (π y₁ * π y₂) := by rw [this]
  have hallpos : ∀ x : ↥(normalizer (E : Set G)), ρ x ∈ T → Commute (π x) (π k₀) := by
    intro x hx
    by_cases hx1 : ρ x = 1
    · rcases hthree x hx1 with h | h | h
      · rw [h]; exact Commute.one_left _
      · exact h ▸ Commute.refl _
      · rw [h]; exact (Commute.refl _).inv_left
    obtain ⟨m, hm⟩ := hT.exists_conj_eq hD.R_le hy₀T hx hy₀1 hx1
    have hk : ρ ((m * y₀ * m⁻¹)⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hm, inv_mul_cancel]
    have hxeq : x = (m * y₀ * m⁻¹) * ((m * y₀ * m⁻¹)⁻¹ * x) := by group
    rw [hxeq, map_mul]
    refine Commute.mul_left (hpos_conj y₀ m hy₀) ?_
    rcases hthree _ hk with h | h | h
    · rw [h]; exact Commute.one_left _
    · exact h ▸ Commute.refl _
    · rw [h]; exact (Commute.refl _).inv_left
  have hyk : Commute (π y) (π k) := by
    rcases hthree k hk with h | h | h
    · rw [h]; exact Commute.one_right _
    · rw [h]; exact hallpos y hy
    · rw [h]; exact (hallpos y hy).inv_right
  rw [← hπ1, map_mul, map_mul, map_mul, map_inv, map_inv, hyk.eq]
  group

end Kernel

end CFSG.ComponentClassification.AS81
