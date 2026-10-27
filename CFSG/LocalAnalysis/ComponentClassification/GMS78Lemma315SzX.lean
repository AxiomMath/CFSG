module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzR
public import CFSG.GH74.BNPair.L15Maschke

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T R X : Subgroup G} {a : ℕ} {y d : G}

structure IsX (L T R X : Subgroup G) (d : G) : Prop where
  gmsV_le : gmsV L T ≤ X
  le_R : X ≤ R
  mem_normalizer : d ∈ normalizer (X : Set G)
  sup_eq : T ⊔ X = R
  inf_eq : T ⊓ X = gmsV L T

namespace SzR

variable (hS : SzR G L T R a y d)
include hS

theorem d_mem_gmsN₁ :
    d ∈ gmsN₁ L T := by
  refine GMS78.mem_gmsN₁.mpr ⟨hS.mem_normalizer_gmsV,
    mem_normalizer_of_conj_mem_of_finite fun b hb => ?_,
    fun v hv => hS.conj_mul_inv_mem_gmsA hv⟩
  rw [hS.conj_eq b (mem_sup_left (mem_inf.mp hb).1)]
  exact (mem_normalizer_iff.mp hS.torus.mem_normalizer_gmsA b).mp hb

theorem exists_isX
    (h34 : NoStronglyClosedAbelian G) : ∃ X, IsX L T R X d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : Nat.Coprime 2 (Nat.card (zpowers d)) := by
    rw [Nat.card_zpowers]
    exact Nat.coprime_two_left.mpr hS.odd
  have hconj : ∀ {H : Subgroup G}, d ∈ normalizer (H : Set G) →
      ∀ g ∈ zpowers d, ∀ x ∈ H, g * x * g⁻¹ ∈ H := by
    intro H hdH g hg x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (mem_normalizer_iff.mp (zpow_mem hdH k) x).mp hx
  have hdT : d ∈ normalizer (T : Set G) := by
    rw [hS.eq_gmsW]
    exact hS.mem_normalizer_gmsW
  obtain ⟨X, hVX, hXR, hdX, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 2) (Q := R) (Φ := gmsV L T)
      (D := zpowers d) (T := T) hS.gmsV_le_R (fun x hx y hy => hS.commutator_mem_gmsV h34 hx hy)
      (fun x hx => hS.sq_mem_gmsV h34 hx) hD (hconj hS.mem_normalizer)
      (hconj hS.mem_normalizer_gmsV) (hS.gmsV_le.trans (le_of_eq hS.eq_gmsW.symm)) hS.T_le
      (hconj hdT)
  refine ⟨X, hVX, hXR, mem_normalizer_iff.mpr fun x => ⟨fun hx => hdX d (mem_zpowers d) x hx,
    fun hx => ?_⟩, hsup, hinf⟩
  have := hdX d⁻¹ (inv_mem (mem_zpowers d)) _ hx
  simpa [mul_assoc] using this

theorem rightConjugate_mul_eq {z v : G}
    (hv : v ∈ gmsV L T) :
    rightConjugate (T ⊓ centralizer (L : Set G)) (z * v)⁻¹ =
      rightConjugate (T ⊓ centralizer (L : Set G)) z⁻¹ := by
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hvN : v⁻¹ ∈ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
      congrArg Subtype.val (hVel.1.is_comm.comm ⟨t, mem_sup_right ht⟩ ⟨v⁻¹, inv_mem hv⟩))
  rw [mul_inv_rev, ← rightConjugate_mul, (rightConjugate_eq_self_iff _ _).mpr hvN]

theorem exists_mem_isX_not_mem
    (hX : IsX L T R X d) {S : Set (Subgroup G)} (hSfin : S.Finite)
    (hScard : S.ncard < 2 ^ (2 * a + 1)) :
    ∃ z ∈ X, rightConjugate (T ⊓ centralizer (L : Set G)) z⁻¹ ∉ S := by
  obtain ⟨Q, hQ, hQS⟩ : ∃ Q ∈ gmsDelta L T, Q ∉ S := by
    by_contra hcon
    push Not at hcon
    have h1 := Set.ncard_le_ncard hcon hSfin
    rw [← Nat.card_coe_set_eq, hS.lemma313.card_eq] at h1
    omega
  obtain ⟨r, hr, hrQ⟩ := hS.isR.exists_conj_eq hS.facts hS.sec3 hS.trans hQ
  have hXT : X ≤ normalizer (T : Set G) := hX.le_R.trans hS.le_normalizer_T
  have hr' : r ∈ X ⊔ T := by rw [sup_comm, hX.sup_eq]; exact hr
  obtain ⟨z, hz, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hXT hr'
  refine ⟨z, hz, ?_⟩
  have htN : t⁻¹ ∈ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    inv_mem (le_normalizer_of_conj_mem (fun _ ht' _ hp => hS.sec3.conj_mem_T₀ ht' hp) ht)
  rw [mul_inv_rev, ← rightConjugate_mul, (rightConjugate_eq_self_iff _ _).mpr htN] at hrQ
  rwa [hrQ]

theorem sq_mul_inv_sq_mem
    (h34 : NoStronglyClosedAbelian G) (hX : IsX L T R X d) {x x' : G} (hx : x ∈ X)
    (hxV : x ∉ gmsV L T) (hx' : x' ∈ X) (hx'V : x' ∉ gmsV L T) :
    x ^ 2 * (x' ^ 2)⁻¹ ∈ gmsA L T := by
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hnotW : ∀ z ∈ X, z ∉ gmsV L T → z ∉ gmsW L T := fun z hz hzV hzW => hzV (by
    rw [← hX.inf_eq, hS.eq_gmsW]
    exact mem_inf.mpr ⟨hzW, hz⟩)
  have hxR := hX.le_R hx
  have hx'R := hX.le_R hx'
  obtain ⟨k, hk⟩ := hS.isR.exists_pow_conj_mem hS.lemma313 hS.facts hS.sec3 hS.foundation
    hS.inf_centralizer hS.torus hS.mem_normalizer hS.mem_normalizer_gmsW hS.conj_eq hxR
    (hnotW x hx hxV) hx'R (hnotW x' hx' hx'V)
  set c := (d ^ k)⁻¹ * x * d ^ k with hc
  have hcX : c ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem hX.mem_normalizer k)) x).mp hx
    simpa [hc] using this
  have hv : x'⁻¹ * c ∈ gmsV L T := by
    rw [← hX.inf_eq]
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem hx') hcX⟩
    rw [hS.eq_gmsW]
    exact hk
  have h1 : c ^ 2 * (x ^ 2)⁻¹ ∈ gmsA L T := by
    have e : c ^ 2 * (x ^ 2)⁻¹ = (d ^ k)⁻¹ * x ^ 2 * ((d ^ k)⁻¹)⁻¹ * (x ^ 2)⁻¹ := by
      rw [hc, sq, sq]
      group
    rw [e]
    exact (GMS78.mem_gmsN₁.mp (inv_mem (pow_mem hS.d_mem_gmsN₁ k))).2.2 _
      (hS.sq_mem_gmsV h34 hxR)
  have h2 : c ^ 2 * (x' ^ 2)⁻¹ ∈ gmsA L T := by
    set v := x'⁻¹ * c with hvdef
    have hcv : c = x' * v := by rw [hvdef]; group
    have ha : x'⁻¹ * v * x'⁻¹⁻¹ * v⁻¹ ∈ gmsA L T :=
      conj_mul_inv_mem (hS.isR.le_gmsTrans (inv_mem hx'R)) hv
    have hv2 : v * v = 1 := by rw [← sq]; exact hVel.2 v hv
    have e : c ^ 2 * (x' ^ 2)⁻¹ =
        x' ^ 2 * (x'⁻¹ * v * x'⁻¹⁻¹ * v⁻¹) * (v * v) * (x' ^ 2)⁻¹ := by
      rw [hcv, sq, sq]
      group
    rw [e, hv2, mul_one]
    have hN : x' ^ 2 ∈ normalizer (gmsA L T : Set G) :=
      Subgroup.centralizer_le_normalizer _ (pow_mem ((hS.isR.le_gmsTrans hx'R) |> fun h =>
        (mem_inf.mp h).2) 2)
    exact (mem_normalizer_iff.mp hN _).mp ha
  have e : x ^ 2 * (x' ^ 2)⁻¹ = (c ^ 2 * (x ^ 2)⁻¹)⁻¹ * (c ^ 2 * (x' ^ 2)⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem h1) h2

theorem le_normalizer_gmsA_R : R ≤ normalizer (gmsA L T : Set G) := fun _ hr =>
  Subgroup.centralizer_le_normalizer _ (mem_inf.mp (hS.isR.le_gmsTrans hr)).2

theorem sq_mem_gmsA_of_isX
    (h34 : NoStronglyClosedAbelian G) (hX : IsX L T R X d) {x : G} (hx : x ∈ X) :
    x ^ 2 ∈ gmsA L T := by
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  by_cases hxV : x ∈ gmsV L T
  · rw [hVel.2 x hxV]
    exact one_mem _
  have hq : 8 ≤ 2 ^ (2 * a + 1) :=
    (show 8 = 2 ^ 3 by norm_num) ▸
      Nat.pow_le_pow_right (by norm_num) (by have := hS.one_le; omega)
  set Q₀ := T ⊓ centralizer (L : Set G) with hQ₀
  have hφ : ∀ z w : G, w ∈ gmsV L T → rightConjugate Q₀ (z * w)⁻¹ = rightConjugate Q₀ z⁻¹ :=
    fun z w hw => hS.rightConjugate_mul_eq hw
  have hφV : ∀ w ∈ gmsV L T, rightConjugate Q₀ w⁻¹ = Q₀ := fun w hw => by
    simpa [rightConjugate_one] using hφ 1 w hw
  have hgood : ∀ z ∈ X, rightConjugate Q₀ z⁻¹ ≠ Q₀ → rightConjugate Q₀ z⁻¹ ≠ rightConjugate Q₀ x →
      z ∉ gmsV L T ∧ x * z ∉ gmsV L T := by
    intro z _ h1 h2
    refine ⟨fun hzV => h1 (hφV z hzV), fun hxz => h2 ?_⟩
    have := hφ x⁻¹ (x * z) hxz
    rwa [show x⁻¹ * (x * z) = z by group, inv_inv] at this
  have hcard2 : ({Q₀, rightConjugate Q₀ x} : Set (Subgroup G)).ncard < 2 ^ (2 * a + 1) := by
    have := (Set.ncard_insert_le Q₀ {rightConjugate Q₀ x}).trans (by rw [Set.ncard_singleton])
    omega
  obtain ⟨y₁, hy₁, hy₁S⟩ := hS.exists_mem_isX_not_mem hX (Set.toFinite _) hcard2
  rw [← hQ₀] at hy₁S
  obtain ⟨hy₁V, hxy₁V⟩ := hgood y₁ hy₁ (fun h => hy₁S (by simp [h]))
    (fun h => hy₁S (by simp [h]))
  have hcard4 : ({Q₀, rightConjugate Q₀ x, rightConjugate Q₀ y₁, rightConjugate Q₀ (x * y₁)} :
      Set (Subgroup G)).ncard < 2 ^ (2 * a + 1) := by
    have h1 := Set.ncard_insert_le Q₀
      {rightConjugate Q₀ x, rightConjugate Q₀ y₁, rightConjugate Q₀ (x * y₁)}
    have h2 := Set.ncard_insert_le (rightConjugate Q₀ x)
      {rightConjugate Q₀ y₁, rightConjugate Q₀ (x * y₁)}
    have h3 := Set.ncard_insert_le (rightConjugate Q₀ y₁) {rightConjugate Q₀ (x * y₁)}
    rw [Set.ncard_singleton] at h3
    omega
  obtain ⟨y₂, hy₂, hy₂S⟩ := hS.exists_mem_isX_not_mem hX (Set.toFinite _) hcard4
  rw [← hQ₀] at hy₂S
  obtain ⟨hy₂V, hxy₂V⟩ := hgood y₂ hy₂ (fun h => hy₂S (by simp [h]))
    (fun h => hy₂S (by simp [h]))
  have hy₁₂V : y₁ * y₂ ∉ gmsV L T := by
    intro h
    apply hy₂S
    have := hφ y₁⁻¹ (y₁ * y₂) h
    rw [show y₁⁻¹ * (y₁ * y₂) = y₂ by group, inv_inv] at this
    simp [this]
  have hxy₁₂V : x * (y₁ * y₂) ∉ gmsV L T := by
    intro h
    apply hy₂S
    have := hφ (x * y₁)⁻¹ (x * (y₁ * y₂)) h
    rw [show (x * y₁)⁻¹ * (x * (y₁ * y₂)) = y₂ by group, inv_inv] at this
    simp [this]
  have hN : (x ^ 2)⁻¹ ∈ normalizer (gmsA L T : Set G) :=
    hS.le_normalizer_gmsA_R (inv_mem (pow_mem (hX.le_R hx) 2))
  have hc : ∀ z ∈ X, z ∉ gmsV L T → x * z ∉ gmsV L T →
      x⁻¹ * z * x * z⁻¹ * x ^ 2 ∈ gmsA L T := by
    intro z hz hzV hxzV
    have h1 := hS.sq_mul_inv_sq_mem h34 hX (mul_mem hx hz) hxzV hx hxV
    have h2 := hS.sq_mul_inv_sq_mem h34 hX hz hzV hx hxV
    rw [sq (x * z)] at h1
    have e : x⁻¹ * z * x * z⁻¹ * x ^ 2 = (x ^ 2)⁻¹ *
        (x * z * (x * z) * (x ^ 2)⁻¹ * (z ^ 2 * (x ^ 2)⁻¹)⁻¹) * ((x ^ 2)⁻¹)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp hN _).mp (mul_mem h1 (inv_mem h2))
  have hP₁ := hc y₁ hy₁ hy₁V hxy₁V
  have hP₂ := hc y₂ hy₂ hy₂V hxy₂V
  have hP₁₂ := hc (y₁ * y₂) (mul_mem hy₁ hy₂) hy₁₂V hxy₁₂V
  have hc₂V : x⁻¹ * y₂ * x * y₂⁻¹ ∈ gmsV L T := by
    have := hS.commutator_mem_gmsV h34 (inv_mem (hX.le_R hx)) (hX.le_R hy₂)
    simpa using this
  have hb : y₁ * (x⁻¹ * y₂ * x * y₂⁻¹) * y₁⁻¹ * (x⁻¹ * y₂ * x * y₂⁻¹)⁻¹ ∈ gmsA L T :=
    conj_mul_inv_mem (hS.isR.le_gmsTrans (hX.le_R hy₁)) hc₂V
  have e : x ^ 2 = (y₁ * (x⁻¹ * y₂ * x * y₂⁻¹) * y₁⁻¹ * (x⁻¹ * y₂ * x * y₂⁻¹)⁻¹) *
      (x⁻¹ * y₂ * x * y₂⁻¹ * x ^ 2) * (x⁻¹ * (y₁ * y₂) * x * (y₁ * y₂)⁻¹ * x ^ 2)⁻¹ *
      (x⁻¹ * y₁ * x * y₁⁻¹ * x ^ 2) := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hb hP₂) (inv_mem hP₁₂)) hP₁

theorem conj_mul_inv_mem_gmsA_of_isX
    (h34 : NoStronglyClosedAbelian G) (hX : IsX L T R X d) {t : G} (ht : t ∈ T ⊓ L) {x : G}
    (hx : x ∈ X) : t * x * t⁻¹ * x⁻¹ ∈ gmsA L T := by
  obtain ⟨-, hVel, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have htT : t ∈ T := (mem_inf.mp ht).1
  have htW : t ∈ gmsW L T := mem_sup_left ht
  have hxR := hX.le_R hx
  by_cases hxV : x ∈ gmsV L T
  · have htx : t * x = x * t := (mem_centralizer_iff.mp (hVC hxV) t htW)
    rw [htx]
    have : x * t * t⁻¹ * x⁻¹ = 1 := by group
    rw [this]
    exact one_mem _
  set b := x⁻¹ * t * x * t⁻¹ with hbdef
  have hbV : b ∈ gmsV L T := by
    have := hS.conj_mul_inv_mem_of_mem_T htT (inv_mem hxR)
    simpa [hbdef] using this
  have hx2 : x ^ 2 ∈ gmsA L T := hS.sq_mem_gmsA_of_isX h34 hX hx
  have htx2 : t * x ^ 2 * t⁻¹ = x ^ 2 := by
    rw [mem_centralizer_iff.mp (mem_inf.mp hx2).2 t ht]
    group
  have hb2 : b * b = 1 := by rw [← sq]; exact hVel.2 b hbV
  have hxb : x * b = b * x := by
    have e1 : (x * b) * (x * b) = x * x := by
      have : (x * b) * (x * b) = t * x ^ 2 * t⁻¹ := by rw [hbdef, sq]; group
      rw [this, htx2, sq]
    have e2 : b * x * b = x := by
      have := congrArg (fun g => x⁻¹ * g) e1
      simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact this
    calc x * b = b * b * x * b := by rw [hb2, one_mul]
      _ = b * (b * x * b) := by group
      _ = b * x := by rw [e2]
  have hxC : x ∉ centralizer (gmsV L T : Set G) := fun hxC => hxV (by
    rw [← hX.inf_eq, ← hS.inf_centralizer_R]
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxR, hxC⟩, hx⟩)
  have hbA : b ∈ gmsA L T :=
    mem_gmsA_of_commute hS.lemma313 hS.facts hS.sec3 hS.foundation (hS.isR.le_gmsTrans hxR) hxC
      hbV hxb
  have e : t * x * t⁻¹ * x⁻¹ = x * b * x⁻¹ := by rw [hbdef]; group
  rw [e, hxb, mul_inv_cancel_right]
  exact hbA

theorem inv_conj_mul_inv_mem_gmsA
    (h34 : NoStronglyClosedAbelian G) (hX : IsX L T R X d) {t : G} (ht : t ∈ T) {x : G}
    (hx : x ∈ X) : x⁻¹ * t * x * t⁻¹ ∈ gmsA L T := by
  obtain ⟨t₁, ht₁, s, hs, rfl⟩ := hS.exists_mul_of_mem_T ht
  have h1 : x⁻¹ * t₁ * x * t₁⁻¹ ∈ gmsA L T := by
    have := inv_mem (hS.conj_mul_inv_mem_gmsA_of_isX h34 hX ht₁ (inv_mem hx))
    simpa [mul_assoc] using this
  have h2 : x⁻¹ * s * x⁻¹⁻¹ * s⁻¹ ∈ gmsA L T :=
    conj_mul_inv_mem (hS.isR.le_gmsTrans (inv_mem (hX.le_R hx))) (mem_sup_right hs)
  have hN : t₁ ∈ normalizer (gmsA L T : Set G) := hS.sec3.le_normalizer_gmsA (mem_inf.mp ht₁).1
  have e : x⁻¹ * (t₁ * s) * x * (t₁ * s)⁻¹ =
      (x⁻¹ * t₁ * x * t₁⁻¹) * (t₁ * (x⁻¹ * s * x⁻¹⁻¹ * s⁻¹) * t₁⁻¹) := by group
  rw [e]
  exact mul_mem h1 ((mem_normalizer_iff.mp hN _).mp h2)

theorem sq_mem_gmsA_of_mem_R
    (h34 : NoStronglyClosedAbelian G) (hX : IsX L T R X d) {r : G} (hr : r ∈ R) :
    r ^ 2 ∈ gmsA L T := by
  have hr' : r ∈ X ⊔ T := by rw [sup_comm, hX.sup_eq]; exact hr
  obtain ⟨x, hx, t, ht, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hX.le_R.trans hS.le_normalizer_T) hr'
  have e : (x * t) ^ 2 = x ^ 2 * (x⁻¹ * t * x * t⁻¹) * t ^ 2 := by rw [sq, sq, sq]; group
  rw [e]
  exact mul_mem (mul_mem (hS.sq_mem_gmsA_of_isX h34 hX hx)
    (hS.inv_conj_mul_inv_mem_gmsA h34 hX ht hx)) (hS.sq_mem_gmsA_of_mem_T ht)

theorem commutator_mem_gmsA_of_isX
    (h34 : NoStronglyClosedAbelian G) (hX : IsX L T R X d) {r r' : G} (hr : r ∈ R)
    (hr' : r' ∈ R) : r * r' * r⁻¹ * r'⁻¹ ∈ gmsA L T :=
  commutator_mem_of_sq_mem hS.le_normalizer_gmsA_R hr' (hS.sq_mem_gmsA_of_mem_R h34 hX hr)
    (hS.sq_mem_gmsA_of_mem_R h34 hX hr') (hS.sq_mem_gmsA_of_mem_R h34 hX (mul_mem hr hr'))

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
