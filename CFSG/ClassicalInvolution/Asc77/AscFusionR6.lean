module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR5
public import CFSG.ClassicalInvolution.Asc77.AscL62Aut
public import CFSG.ClassicalInvolution.Asc77.AscFusionR4

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem centSylow_member (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K R V : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) (hR : IsSylow2In R K) (hV2 : IsPGroup 2 ↥V)
    (hVK : ∀ y ∈ V, conjSub y K = K) (hcomm : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r) :
    ∀ k ∈ K, ∀ v ∈ V, ⁅v, k⁆ ∈ oddCoreOf K := by
  intro k hk v hv
  obtain ⟨e⟩ := hK.nonempty_equiv
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr (hVK v hv)
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨v, hvN⟩ with hα
  have hαN : (classicalInvolutionOddCore ↥K).map (α : ↥K →* ↥K) =
      classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (α : ↥K ≃* ↥K)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, orderOf v = 2 ^ n := AscL62.orderOf_eq_two_pow_of_isPGroup hV2 hv
  have hαn : α ^ 2 ^ n = 1 := by
    rw [hα, ← map_pow]
    have : (⟨v, hvN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hn, pow_orderOf_eq_one]
    rw [this, map_one]
  let φ : ↥K →* SL(2, GaloisField p f) :=
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K →* SL(2, GaloisField p f)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 SL(2, GaloisField p f) :=
    Sylow.mapSurjective (f := φ) hφs (AscL62.sylowOfIsSylow2In'' hR)
  have hfix : ∀ x ∈ P, ∃ r : ↥K, e (QuotientGroup.mk r) = x ∧ e (QuotientGroup.mk (α r)) = x := by
    intro x hx
    have hx' : x ∈ ((AscL62.sylowOfIsSylow2In'' hR : Subgroup ↥K)).map φ := by
      have := Sylow.coe_mapSurjective (f := φ) hφs (AscL62.sylowOfIsSylow2In'' hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hvr : v * (r : G) * v⁻¹ = r := by
      rw [← hcomm r hrR v hv]
      group
    have hαr : α r = r := by
      apply Subtype.ext
      rw [hα]
      simpa using hvr
    exact ⟨r, rfl, by rw [hαr]; rfl⟩
  have h1 := AscL62.mulAut_trivial_quotient_of_fixes_sylow hp hq _ e α hαN n hαn P hfix ⟨k, hk⟩
  have h2 : (α ⟨k, hk⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈ classicalInvolutionOddCore ↥K := by
    rw [← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
    exact h1
  have h3 : ((α ⟨k, hk⟩ : ↥K) : G) = v * k * v⁻¹ := by
    rw [hα]
    simp
  have hmem : ⁅v, k⁆ ∈ K := by
    rw [commutatorElement_def]
    have := (α ⟨k, hk⟩).2
    rw [h3] at this
    exact K.mul_mem this (K.inv_mem hk)
  refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
  convert h2 using 1
  apply Subtype.ext
  simp [h3, commutatorElement_def]


theorem exists_kappa (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K : Subgroup G} {z v : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hKz : IsUniqueInvolution K z)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v ∉ Subgroup.normalizer (K : Set G))
    (hn : v * v ∈ Subgroup.normalizer (K : Set G))
    (hnt : ¬ ∀ k ∈ K, ⁅v * v, k⁆ ∈ oddCoreOf K) :
    ∃ κ ∈ K, κ * κ = z ∧ (v * v)⁻¹ * κ * (v * v) = κ⁻¹ ∧
      κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ := by
  classical
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hv4]
    norm_num
  have hvK' : conjSub v⁻¹ K ≠ K := fun h =>
    hvK (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  obtain ⟨R, hR2, hvR, -, hRK, -, hcomm, hinv⟩ :=
    exists_twin_sylow hp2 hq h₀ hK hKz hv2 hvz hvK' hn
  have hK₀mem : IsClassicalMember p f K z :=
    isClassicalMember_of_mem_conjClass hp2 hq h₀ hK hKz
  set Qs : Subgroup G := R ⊓ K with hQs
  have hQsK : Qs ≤ K := inf_le_right
  have hQs2 : IsPGroup 2 Qs := hR2.to_le inf_le_left
  have hQuat : IsQuatSub Qs := isQuatSub_of_isSylow2In hp2 hK₀mem hRK
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have hQcard : 2 ≤ Nat.card Qs := by
    obtain ⟨k₂, hk₂, hcard⟩ := hQuat.natCard_eq
    rw [hcard]
    calc 2 ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k₂ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzQ : z ∈ Qs := AscL62.mem_of_uniqueInvolution_of_pGroup hKz hQsK hQs2 hQcard
  set n : G := v * v with hnd
  have hnR : n ∈ R := R.mul_mem hvR hvR
  have hn2 : n * n = 1 := by
    have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
    calc n * n = v ^ 4 := by rw [hnd]; simp [pow_succ, mul_assoc]
      _ = 1 := this
  have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have hconjQ : ∀ x : G, x ∈ Qs → n⁻¹ * x * n ∈ Qs := by
    intro x hx
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hnR) hx.1) hnR, ?_⟩
    exact (mem_conj_iff_of_mem_normalizer hn x).mpr hx.2
  let τ : ↥Qs ≃* ↥Qs :=
    { toFun := fun x => ⟨n⁻¹ * x * n, hconjQ x x.2⟩
      invFun := fun x => ⟨n * x * n⁻¹, by
        have h1 := hconjQ x x.2
        rw [hni] at h1
        simpa [hni] using h1⟩
      left_inv := fun x => by
        apply Subtype.ext
        show n * (n⁻¹ * (x : G) * n) * n⁻¹ = x
        group
      right_inv := fun x => by
        apply Subtype.ext
        show n⁻¹ * (n * (x : G) * n⁻¹) * n = x
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show n⁻¹ * ((x : G) * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n)
        group }
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    show n⁻¹ * (n⁻¹ * (x : G) * n) * n = x
    rw [hni]
    calc n * (n * (x : G) * n) * n = (n * n) * x * (n * n) := by group
      _ = x := by rw [hn2]; group
  have hτ1 : ∃ x, τ x ≠ x := by
    by_contra hcon
    push Not at hcon
    have hcen : ∀ r ∈ Qs, ∀ v' ∈ Subgroup.zpowers n, r * v' = v' * r := by
      intro r hr v' hv'
      have hr1 : n⁻¹ * r * n = r := congrArg Subtype.val (hcon ⟨r, hr⟩)
      have hrn : r * n = n * r := by
        calc r * n = n * (n⁻¹ * r * n) := by group
          _ = n * r := by rw [hr1]
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
      exact (Commute.zpow_right (show Commute r n from hrn) m).eq
    have hV2 : IsPGroup 2 ↥(Subgroup.zpowers n) :=
      hR2.to_le (Subgroup.zpowers_le.mpr hnR)
    have hVK : ∀ y ∈ Subgroup.zpowers n, conjSub y K = K := by
      intro y hy
      exact conjSub_eq_of_mem_normalizer (Subgroup.zpowers_le.mpr hn hy)
    have := centSylow_member hp2 hq hK₀mem (R := Qs) (V := Subgroup.zpowers n) hRK hV2 hVK hcen
    exact hnt (fun k hk => this k hk n (Subgroup.mem_zpowers n))
  have hgen : ∀ H : Subgroup ↥Qs, (∀ x : ↥Qs, orderOf x = 4 → x ∈ H) → H = ⊤ := by
    intro H hH
    have : NeZero (2 ^ k₁) := ⟨by positivity⟩
    exact quaternion_generated_by_order_four eQ H hH
  have hzu : ∀ x : ↥Qs, x * x = 1 → x = 1 ∨ x = ⟨z, hzQ⟩ := by
    intro x hx
    have hxG : (x : G) * (x : G) = 1 := congrArg Subtype.val hx
    rcases hKz.unique (x : G) (hQsK x.2) hxG with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h
  have hz2 : (⟨z, hzQ⟩ : ↥Qs) * ⟨z, hzQ⟩ = 1 := Subtype.ext hKz.sq
  obtain ⟨κ', hκ'4, hκ'⟩ := exists_inverted_order_four ⟨z, hzQ⟩ hz2 (fun x => hQs2 x) hzu hgen τ hτ2
    hτ1
  set κ : G := (κ' : G) with hκ
  have hκK : κ ∈ K := hQsK κ'.2
  have hκ4 : orderOf κ = 4 := by rw [hκ, Subgroup.orderOf_coe]; exact hκ'4
  refine ⟨κ, hκK, ?_, ?_, ?_⟩
  ·
    have h1 : (κ * κ) * (κ * κ) = 1 := by
      have : κ ^ 4 = 1 := by rw [← hκ4]; exact pow_orderOf_eq_one κ
      calc (κ * κ) * (κ * κ) = κ ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hKz.unique (κ * κ) (K.mul_mem hκK hκK) h1 with h | h
    · exfalso
      have : orderOf κ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hκ4] at this
      omega
    · exact h
  · have := congrArg Subtype.val hκ'
    simpa [τ, hκ, hni] using this
  · have hκ'' : v⁻¹ * κ * v ∈ R ⊓ conjSub v⁻¹ K := hinv κ ⟨κ'.2.1, hκK⟩
    exact hcomm κ ⟨κ'.2.1, hκK⟩ _ hκ''

end CFSG.ClassicalInvolution.Asc77.AscFusion
