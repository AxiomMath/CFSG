module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR8
public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaTwin
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
open scoped commutatorElement MatrixGroups Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_conj_of_odd_coset {N : Subgroup G} (hodd : Odd (Nat.card N)) {x y : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hxy : x⁻¹ * y ∈ N) :
    ∃ h ∈ N ⊔ Subgroup.zpowers x, h * x * h⁻¹ = y := by
  classical
  set H : Subgroup G := N ⊔ Subgroup.zpowers x with hH
  have hNH : N ≤ H := le_sup_left
  have hxH : x ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hyH : y ∈ H := by
    have : y = x * (x⁻¹ * y) := by group
    rw [this]
    exact H.mul_mem hxH (hNH hxy)
  have hdec : ∀ h ∈ H, ∃ n ∈ N, ∃ w ∈ Subgroup.zpowers x, h = n * w := by
    intro h hh
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left N (Subgroup.zpowers x)
      (Subgroup.zpowers_le.mpr hxN)
    have : h ∈ ((N ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hh
    rw [hset] at this
    obtain ⟨n, hn, w, hw, rfl⟩ := this
    exact ⟨n, hn, w, hw, rfl⟩
  let xH : ↥H := ⟨x, hxH⟩
  let yH : ↥H := ⟨y, hyH⟩
  have hxH2 : IsPGroup 2 (Subgroup.zpowers xH) := by
    obtain ⟨n, hn⟩ := hx2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, show orderOf xH = orderOf x from (Subgroup.orderOf_coe xH).symm, ← hn,
      Nat.card_zpowers]
  have hyH2 : IsPGroup 2 (Subgroup.zpowers yH) := by
    obtain ⟨n, hn⟩ := hy2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, show orderOf yH = orderOf y from (Subgroup.orderOf_coe yH).symm, ← hn,
      Nat.card_zpowers]
  obtain ⟨P, hP⟩ := hxH2.exists_le_sylow
  obtain ⟨P', hP'⟩ := hyH2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H P P'
  have hPeq : ∀ p ∈ (P : Subgroup ↥H), p ∈ Subgroup.zpowers xH := by
    intro p hp
    obtain ⟨n, hn, w, hw, hpw⟩ := hdec p p.2
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hwH : (⟨x ^ i, Subgroup.zpow_mem H hxH i⟩ : ↥H) ∈ Subgroup.zpowers xH :=
      Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
    have hnP : (⟨n, hNH hn⟩ : ↥H) ∈ (P : Subgroup ↥H) := by
      have h1 : p * (⟨x ^ i, Subgroup.zpow_mem H hxH i⟩ : ↥H)⁻¹ ∈ (P : Subgroup ↥H) :=
        P.mul_mem hp (P.inv_mem (hP hwH))
      have h2 : p * (⟨x ^ i, Subgroup.zpow_mem H hxH i⟩ : ↥H)⁻¹ = ⟨n, hNH hn⟩ := by
        apply Subtype.ext
        simp [hpw]
      rwa [h2] at h1
    have hn2 : IsPGroup 2 (Subgroup.zpowers n) := by
      have := P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hnP)
      obtain ⟨m, hm⟩ := this.exists_card_eq
      refine IsPGroup.of_card (n := m) ?_
      rw [Nat.card_zpowers, show orderOf n = orderOf (⟨n, hNH hn⟩ : ↥H) from
        Subgroup.orderOf_coe (⟨n, hNH hn⟩ : ↥H), ← Nat.card_zpowers, hm]
    have hn1 : n = 1 := eq_one_of_isPGroup_of_mem_odd hodd hn hn2
    have : p = ⟨x ^ i, Subgroup.zpow_mem H hxH i⟩ := by
      apply Subtype.ext
      simp [hpw, hn1]
    rw [this]
    exact hwH
  have hyP' : yH ∈ (P' : Subgroup ↥H) := hP' (Subgroup.mem_zpowers yH)
  rw [← hg] at hyP'
  have hyP'' : yH ∈ MulAut.conj g • (P : Subgroup ↥H) := hyP'
  obtain ⟨s, hsP, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hyP''
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hPeq s hsP)
  have hsG : ((s : ↥H) : G) = x ^ j := by
    rw [← hj]
    simp [xH]
  have hyG : y = (g : G) * x ^ j * (g : G)⁻¹ := by
    have := congrArg Subtype.val hs
    simpa [MulAut.conj_apply, hsG] using this.symm
  obtain ⟨n₀, hn₀, w₀, hw₀, hgw⟩ := hdec g g.2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw₀
  have hxjN : x ^ j ∈ Subgroup.normalizer (N : Set G) := Subgroup.zpow_mem _ hxN j
  have hy2' : y = n₀ * x ^ j * n₀⁻¹ := by
    rw [hyG, hgw]
    group
  have hN1 : (x ^ j)⁻¹ * y ∈ N := by
    have h1 : (x ^ j)⁻¹ * n₀ * ((x ^ j)⁻¹)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxjN) n₀).mp hn₀
    have h2 : (x ^ j)⁻¹ * y = ((x ^ j)⁻¹ * n₀ * ((x ^ j)⁻¹)⁻¹) * n₀⁻¹ := by
      rw [hy2']
      group
    rw [h2]
    exact N.mul_mem h1 (N.inv_mem hn₀)
  have hN2 : x⁻¹ * x ^ j ∈ N := by
    have : x⁻¹ * x ^ j = (x⁻¹ * y) * ((x ^ j)⁻¹ * y)⁻¹ := by group
    rw [this]
    exact N.mul_mem hxy (N.inv_mem hN1)
  have hmemx : x⁻¹ * x ^ j ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) j)
  have h1 : x⁻¹ * x ^ j = 1 :=
    eq_one_of_isPGroup_of_mem_odd hodd hN2 (hx2.to_le (Subgroup.zpowers_le.mpr hmemx))
  have hxj : x ^ j = x := by
    have : x ^ j = x * (x⁻¹ * x ^ j) := by group
    rw [this, h1, mul_one]
  refine ⟨(g : G), ?_, ?_⟩
  · exact g.2
  · rw [hyG, hxj]

omit [Finite G] in
theorem isPGroup_zpowers_of_sq_sq {x : G} (h : (x * x) * (x * x) = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have h4 : x ^ 2 ^ 2 = 1 := by simpa [pow_succ, mul_assoc] using h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h4)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

omit [Finite G] in
theorem mem_normalizer_oddCoreOf_of_mem_normalizer' {K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer (oddCoreOf K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => mem_normalizer_oddCoreOf_of_mem_normalizer hn hh, fun hh => ?_⟩
  have := mem_normalizer_oddCoreOf_of_mem_normalizer
    ((Subgroup.normalizer (K : Set G)).inv_mem hn) hh
  simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_chart_of_classical {K : Subgroup G} {z : G} (hK : IsClassicalMember p f K z) :
    ∃ φ : ↥K →* SL(2, GaloisField p f), Function.Surjective φ ∧
      ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K := by
  obtain ⟨e⟩ := hK.nonempty_equiv
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem exists_conj_in_member (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) {k₁ k₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (h₁ : k₁ * k₁ = z) (h₂ : k₂ * k₂ = z) : ∃ g ∈ K, g * k₁ * g⁻¹ = k₂ := by
  obtain ⟨φ, hφs, hφk⟩ := exists_chart_of_classical hK
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hodd
  have hzK : z ∈ K := hKz.mem
  let zK : ↥K := ⟨z, hzK⟩
  let a₁ : ↥K := ⟨k₁, hk₁⟩
  let a₂ : ↥K := ⟨k₂, hk₂⟩
  have hza : zK * zK = 1 := Subtype.ext hKz.sq
  have hφz1 : φ zK ≠ 1 := by
    intro h
    have hmem := (hφk zK).mp h
    have hz1 : z = 1 := by
      refine eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
        (mem_oddCoreOf_iff.mpr ⟨hzK, hmem⟩) (isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one)
    exact hKz.ne_one hz1
  have hφz : φ zK = -1 := by
    have hinv : (φ zK)⁻¹ = φ zK := by
      rw [← map_inv]
      congr 1
      exact inv_eq_of_mul_eq_one_right hza
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self _ h2 _ hinv with
      h | h
    · exact absurd h hφz1
    · exact h
  have hsq₁ : φ a₁ * φ a₁ = -1 := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext h₁
  have hsq₂ : φ a₂ * φ a₂ = -1 := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext h₂
  obtain ⟨g', hg'⟩ := sl2_exists_conj_of_sq_eq_neg_one hodd hsq₁ hsq₂
  obtain ⟨g, rfl⟩ := hφs g'
  set x₀ : G := (g : G) * k₁ * (g : G)⁻¹ with hx₀
  have hx₀K : x₀ ∈ K := K.mul_mem (K.mul_mem g.2 hk₁) (K.inv_mem g.2)
  have hx₀sq : x₀ * x₀ = z := by
    have : x₀ * x₀ = (g : G) * (k₁ * k₁) * (g : G)⁻¹ := by rw [hx₀]; group
    rw [this, h₁]
    exact hKz.conj_eq (conjSub_eq_self_of_mem g.2)
  have hx₀2 : IsPGroup 2 (Subgroup.zpowers x₀) :=
    isPGroup_zpowers_of_sq_sq (by rw [hx₀sq]; exact hKz.sq)
  have hk₂2 : IsPGroup 2 (Subgroup.zpowers k₂) :=
    isPGroup_zpowers_of_sq_sq (by rw [h₂]; exact hKz.sq)
  have hcoset : x₀⁻¹ * k₂ ∈ oddCoreOf K := by
    have hker : φ ((g * a₁ * g⁻¹)⁻¹ * a₂) = 1 := by
      have : φ (g * a₁ * g⁻¹) = φ a₂ := by simpa [map_mul, map_inv] using hg'
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have hmem : x₀⁻¹ * k₂ ∈ K := K.mul_mem (K.inv_mem hx₀K) hk₂
    refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
    have e : (⟨x₀⁻¹ * k₂, hmem⟩ : ↥K) = (g * a₁ * g⁻¹)⁻¹ * a₂ := by
      apply Subtype.ext
      simp [hx₀, a₁, a₂]
    rw [e]
    exact (hφk _).mp hker
  obtain ⟨h, hh, hconj⟩ := exists_conj_of_odd_coset (oddCoreOf_odd_natCard K) hx₀2 hk₂2
    (mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hx₀K)) hcoset
  have hhK : h ∈ K := by
    exact (sup_le (oddCoreOf_le_self K) (Subgroup.zpowers_le.mpr hx₀K)) hh
  refine ⟨h * (g : G), K.mul_mem hhK g.2, ?_⟩
  rw [← hconj, hx₀]
  group

omit [Finite G] in
theorem conjClass_symm {K J : Subgroup G} (h : J ∈ CoreAssembly.conjClass K) :
    K ∈ CoreAssembly.conjClass J := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J h
  exact ⟨g⁻¹, by
    show conjSub g⁻¹ (conjSub g K) = K
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]⟩

omit [Finite G] in
theorem conjClass_trans {K J L : Subgroup G} (h : J ∈ CoreAssembly.conjClass K)
    (h' : L ∈ CoreAssembly.conjClass J) : L ∈ CoreAssembly.conjClass K := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J h
  obtain ⟨g', rfl⟩ := CoreAssembly.single_class (conjSub g K) L h'
  exact ⟨g' * g, conjSub_mul g' g K⟩

theorem twin_facts_general (hq : 5 ≤ p ^ f) (hp2 : p ≠ 2) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K₁ K₂ : Subgroup G} {z : G}
    (h₁ : K₁ ∈ CoreAssembly.conjClass K₀) (h₂ : K₂ ∈ CoreAssembly.conjClass K₀)
    (hz₁ : IsUniqueInvolution K₁ z) (hz₂ : IsUniqueInvolution K₂ z) (hne : K₁ ≠ K₂) :
    K₂ ≤ Subgroup.normalizer (K₁ : Set G) ∧ K₁ ≤ Subgroup.normalizer (K₂ : Set G) ∧
      ⁅K₁, K₂⁆ ≤ oddCoreOf K₁ ⊓ oddCoreOf K₂ := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K₀ K₁ h₁
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K₀ K₂ h₂
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj a)
  have hUb := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj b)
  exact twins_of_conjSub hq h₀ ((hUa.eq hz₁).trans (hUb.eq hz₂).symm) hne

end CFSG.ClassicalInvolution.Asc77.AscFusion
