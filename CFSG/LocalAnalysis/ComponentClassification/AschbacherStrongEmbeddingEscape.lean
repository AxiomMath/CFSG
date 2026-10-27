module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingProducts

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {X : Type*} [Group X] {H : Subgroup X} {z : X}

theorem conj_of_odd_mul {s t : X} (hs : s * s = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (s * t))) : ∃ g : X, t = g⁻¹ * s * g := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨((s * t) ^ m)⁻¹, ?_⟩
  rw [inv_inv, ← pow_two_mul_eq hs ht m]
  have hone : (s * t) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  have h : (s * t) ^ (2 * m) = (s * t)⁻¹ := by
    rw [pow_succ] at hone
    exact eq_inv_of_mul_eq_one_left hone
  rw [h, mul_inv_rev, inv_eq_of_mul_eq_one_left ht, inv_eq_of_mul_eq_one_left hs,
    mul_assoc, hs, mul_one]

theorem class_conj_in_centralizer [Finite X] (hz : orderOf z = 2)
    (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    {w : X} (hw : ¬ Subgroup.centralizer ({w} : Set X) ≤ H) (hzw : Commute z w)
    {t : X} (ht : t ∈ involutionPointClass z) (htw : Commute t w) :
    ∃ y ∈ Subgroup.centralizer ({w} : Set X), t = y⁻¹ * z * y := by
  have hzcls := distinguished_mem_pointClass z
  let C := Subgroup.centralizer ({w} : Set X)
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hzw.eq
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr htw.eq
  have hjoin : ∀ {s₁ s₂ : X}, s₁ ∈ C → s₂ ∈ C → Subgroup.closure ({s₁, s₂} : Set X) ≤ C :=
    fun h₁ h₂ => (Subgroup.closure_le _).mpr (by
      rintro x (rfl | rfl)
      · exact h₁
      · exact h₂)
  have hzbase : z • (QuotientGroup.mk 1 : X ⧸ H) = QuotientGroup.mk 1 :=
    (smul_eq_iff_eq_base huniq _).mpr rfl
  by_cases htbase : t • (QuotientGroup.mk 1 : X ⧸ H) = QuotientGroup.mk 1
  · obtain ⟨c, hcC, hcH⟩ := Set.not_subset.mp hw
    obtain ⟨x', hx'def⟩ : ∃ x' : X, x' = c⁻¹ * z * c := ⟨_, rfl⟩
    have hx' : x' ∈ involutionPointClass z := hx'def ▸ class_conj_mem hzcls c
    have hx'C : x' ∈ C := hx'def ▸ C.mul_mem (C.mul_mem (C.inv_mem hcC) hzC) hcC
    have hx'base : x' • (QuotientGroup.mk 1 : X ⧸ H) ≠ QuotientGroup.mk 1 := by
      intro h
      apply hcH
      rw [hx'def] at h
      exact (conj_mem_iff huniq c).mp (class_mem_iff_fixes_base.mpr h)
    obtain ⟨g, hg, hgx⟩ := conj_in_join_of_fixes_ne hz huniq h1 ht hx' htbase hx'base
    refine ⟨c * g⁻¹, C.mul_mem hcC (C.inv_mem (hjoin htC hx'C hg)), ?_⟩
    have h : t = g * x' * g⁻¹ := by rw [hgx]; group
    rw [h, hx'def]
    group
  · obtain ⟨g, hg, hgt⟩ := conj_in_join_of_fixes_ne hz huniq h1 hzcls ht hzbase htbase
    exact ⟨g, hjoin hzC htC hg, hgt⟩

theorem triple_mul_smul_eq_iff (hz : orderOf z = 2)
    (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {a b : X}
    (ha : a ∈ involutionPointClass z) (hb : b ∈ involutionPointClass z)
    (hza : Commute z a) (hzb : Commute z b) (hab : Commute a b)
    (hza' : a ≠ z) (hab' : b ≠ a) (ω : X ⧸ H) :
    (z * a * b * z) • ω = ω ↔ z • ω = ω := by
  have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have heq : z * a * b * z = a * b := by
    calc z * a * b * z = a * (z * b) * z := by rw [hza.eq, mul_assoc a z b]
      _ = a * b * (z * z) := by rw [hzb.eq]; group
      _ = a * b := by rw [hzz, mul_one]
  rw [heq, product_smul_eq_iff huniq h1 ha hb hab hab',
    commuting_smul_eq_iff huniq h1 ha (distinguished_mem_pointClass z) hza.symm hza'.symm]

theorem triple_class_smul_eq_iff [Finite X] (hz : orderOf z = 2)
    (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {a b : X}
    (ha : a ∈ involutionPointClass z) (hb : b ∈ involutionPointClass z)
    (hza : Commute z a) (hzb : Commute z b) (hab : Commute a b)
    (hza' : a ≠ z) (hab' : b ≠ a)
    (hw : ¬ Subgroup.centralizer ({z * a * b} : Set X) ≤ H)
    {t : X} (ht : t ∈ involutionPointClass z) (htw : Commute t (z * a * b)) (ω : X ⧸ H) :
    (z * a * b * t) • ω = ω ↔ t • ω = ω := by
  have hzw : Commute z (z * a * b) :=
    ((Commute.refl z).mul_right hza).mul_right hzb
  obtain ⟨y, hy, rfl⟩ := class_conj_in_centralizer hz huniq h1 hw hzw ht htw
  have hyw : Commute y (z * a * b) := Subgroup.mem_centralizer_singleton_iff.mp hy
  have heq : z * a * b * (y⁻¹ * z * y) = y⁻¹ * (z * a * b * z) * y := by
    have h : z * a * b * y⁻¹ = y⁻¹ * (z * a * b) := by
      have := hyw.inv_left.eq
      exact this.symm
    calc z * a * b * (y⁻¹ * z * y) = (z * a * b * y⁻¹) * z * y := by group
      _ = y⁻¹ * (z * a * b) * z * y := by rw [h]
      _ = y⁻¹ * (z * a * b * z) * y := by group
  rw [heq, conj_smul_eq_iff, triple_mul_smul_eq_iff hz huniq h1 ha hb hza hzb hab hza' hab',
    ← conj_smul_eq_iff]

theorem rotation_mul_conj {s t : X} (hs : s * s = 1) (ht : t * t = 1) (n : ℕ) :
    (Even n → ∃ g : X, (s * t) ^ n * s = g⁻¹ * s * g) ∧
      (Odd n → ∃ g : X, (s * t) ^ n * s = g⁻¹ * t * g) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨((s * t) ^ j)⁻¹, ?_⟩
    rw [← two_mul, pow_two_mul_eq hs ht j, inv_inv]
  · rintro ⟨j, rfl⟩
    refine ⟨s * ((s * t) ^ j)⁻¹, ?_⟩
    rw [pow_two_add_one_mul_eq hs ht j, mul_inv_rev, inv_inv, hsinv]
    group

theorem smul_eq_of_escaping_triple [Finite X] (hz : orderOf z = 2)
    (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {a b : X}
    (ha : a ∈ involutionPointClass z) (hb : b ∈ involutionPointClass z)
    (hza : Commute z a) (hzb : Commute z b) (hab : Commute a b)
    (hza' : a ≠ z) (hab' : b ≠ a)
    (hw : ¬ Subgroup.centralizer ({z * a * b} : Set X) ≤ H)
    (hwcls : z * a * b ∉ involutionPointClass z) (ω : X ⧸ H) :
    (z * a * b) • ω = ω := by
  have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have haa := class_mul_self hz ha
  have hbb := class_mul_self hz hb
  have hzab : Commute z (a * b) := hza.mul_right hzb
  have hab2 : (a * b) * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc b a b, ← hab.eq, mul_assoc a b b, hbb, mul_one, haa]
  have hww : z * a * b * (z * a * b) = 1 := by
    calc z * a * b * (z * a * b) = z * ((a * b) * z) * (a * b) := by simp only [mul_assoc]
      _ = z * (z * (a * b)) * (a * b) := by rw [← hzab.eq]
      _ = (z * z) * ((a * b) * (a * b)) := by simp only [mul_assoc]
      _ = 1 := by rw [hzz, hab2, one_mul]
  set w := z * a * b with hwdef
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective ω
  have hs : k * z * k⁻¹ ∈ involutionPointClass z := by
    simpa only [inv_inv] using class_conj_mem (distinguished_mem_pointClass z) k⁻¹
  have hsfix : ∀ ω' : X ⧸ H, (k * z * k⁻¹) • ω' = ω' ↔ ω' = QuotientGroup.mk k := by
    intro ω'
    have h := conj_smul_eq_iff_eq huniq k⁻¹ ω'
    rw [inv_inv, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h
    exact h
  have hss := class_mul_self hz hs
  have hsk : (k * z * k⁻¹) • (QuotientGroup.mk k : X ⧸ H) = QuotientGroup.mk k :=
    (hsfix _).mpr rfl
  by_cases hcomm : Commute (k * z * k⁻¹) w
  · have h : (k * z * k⁻¹) • (w • (QuotientGroup.mk k : X ⧸ H)) = w • QuotientGroup.mk k := by
      rw [← mul_smul, hcomm.eq, mul_smul, hsk]
    exact (hsfix _).mp h
  · have heven : Even (orderOf ((k * z * k⁻¹) * w)) := by
      apply Nat.not_odd_iff_even.mp
      intro hodd
      obtain ⟨g, hg⟩ := conj_of_odd_mul hss hww hodd
      exact hwcls (hg ▸ class_conj_mem hs g)
    set r := (k * z * k⁻¹) * w with hrdef
    set j := orderOf r / 2 with hjdef
    let c := r ^ j
    have hc : orderOf c = 2 :=
      orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos r)) heven.two_dvd
    have hcinv : c⁻¹ = c := inv_eq_self_of_orderOf_eq_two hc
    have hc1 : c ≠ 1 := by
      intro h; rw [h, orderOf_one] at hc; exact absurd hc (by decide)
    have hsc : Commute (k * z * k⁻¹) c := by
      change (k * z * k⁻¹) * c = c * (k * z * k⁻¹)
      have h := involution_mul_pow hss hww j
      change (k * z * k⁻¹) * c = c⁻¹ * (k * z * k⁻¹) at h
      rw [h, hcinv]
    have hws : w * (k * z * k⁻¹) = r⁻¹ := by
      rw [hrdef, mul_inv_rev, inv_eq_of_mul_eq_one_left hww, inv_eq_of_mul_eq_one_left hss]
    have hcw' : (w * (k * z * k⁻¹)) ^ j = c := by
      rw [hws, inv_pow]
      exact hcinv
    have hwc : Commute w c := by
      change w * c = c * w
      have h := involution_mul_pow hww hss j
      rw [hcw'] at h
      rw [h, hcinv]
    obtain ⟨n, hn⟩ := Nat.even_or_odd' j
    rcases hn with hn | hn
    · obtain ⟨g, hg⟩ := (rotation_mul_conj hss hww j).1 ⟨n, by omega⟩
      have hcs : c * (k * z * k⁻¹) ∈ involutionPointClass z := by
        change r ^ j * (k * z * k⁻¹) ∈ _
        rw [hrdef, hg]
        exact class_conj_mem hs g
      have hcsne : c * (k * z * k⁻¹) ≠ k * z * k⁻¹ := fun h => hc1 (mul_eq_right.mp h)
      have hcomm' : Commute (k * z * k⁻¹) (c * (k * z * k⁻¹)) :=
        hsc.mul_right (Commute.refl _)
      have hceq : (k * z * k⁻¹) * (c * (k * z * k⁻¹)) = c := by
        rw [← mul_assoc, hsc.eq, mul_assoc, hss, mul_one]
      have hcfix : ∀ ω' : X ⧸ H, c • ω' = ω' ↔ ω' = QuotientGroup.mk k := by
        intro ω'
        rw [← hceq, product_smul_eq_iff huniq h1 hs hcs hcomm' hcsne, hsfix]
      have hck : c • (QuotientGroup.mk k : X ⧸ H) = QuotientGroup.mk k := (hcfix _).mpr rfl
      have h : c • (w • (QuotientGroup.mk k : X ⧸ H)) = w • QuotientGroup.mk k := by
        rw [← mul_smul, ← hwc.eq, mul_smul, hck]
      exact (hcfix _).mp h
    · obtain ⟨g, hg⟩ := (rotation_mul_conj hww hss j).2 ⟨n, hn⟩
      have hcw : c * w ∈ involutionPointClass z := by
        rw [← hcw', hg]
        exact class_conj_mem hs g
      have hwcw : Commute (c * w) w := (hwc.symm.mul_left (Commute.refl w))
      have hceq : w * (c * w) = c := by rw [← mul_assoc, hwc.eq, mul_assoc, hww, mul_one]
      obtain ⟨γ, hγ⟩ := class_fixes_unique huniq hcw
      have hcfix : ∀ ω' : X ⧸ H, c • ω' = ω' ↔ ω' = γ := by
        intro ω'
        rw [← hceq]
        have h := triple_class_smul_eq_iff hz huniq h1 ha hb hza hzb hab hza' hab' hw hcw
          hwcw ω'
        rw [hγ] at h
        exact h
      have hcγ : c • γ = γ := (hcfix γ).mpr rfl
      have hsγ : (k * z * k⁻¹) • γ = γ := by
        have h : c • ((k * z * k⁻¹) • γ) = (k * z * k⁻¹) • γ := by
          rw [← mul_smul, ← hsc.eq, mul_smul, hcγ]
        exact (hcfix _).mp h
      have hγk : γ = QuotientGroup.mk k := (hsfix γ).mp hsγ
      have hcwk : (c * w) • (QuotientGroup.mk k : X ⧸ H) = QuotientGroup.mk k :=
        (hγ _).mpr hγk.symm
      have h : (c * w) • (w • (QuotientGroup.mk k : X ⧸ H)) = w • QuotientGroup.mk k := by
        rw [← mul_smul, hwcw.eq, mul_smul, hcwk]
      rw [hγ, ← hγk] at h
      rw [hγk] at h
      exact h

end CFSG.ComponentClassification.AschbacherStrongEmbedding
