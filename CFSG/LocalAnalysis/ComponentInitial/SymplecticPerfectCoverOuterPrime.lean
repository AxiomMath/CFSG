module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Subgroup SymplecticFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBSymplecticTwo (kernel_generation)

variable {r : ℕ} {K : Type} [Field K]

theorem conjAut_mem_inner_of_isSquare [NeZero r] {A : gsp r K}
    (h : IsSquare (multiplier r K A : K)) :
    conjAut r K A ∈ inner (StatedProj (StatedSp r K)) := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact (multiplier r K A).ne_zero hc
  set u : Kˣ := Units.mk0 c hc0 with hu
  set s : GL (Fin r ⊕ Fin r) K := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) u⁻¹ with hs
  have hscent : s ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u⁻¹, rfl⟩
  have hBmat : (((A : GL (Fin r ⊕ Fin r) K) * s : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((u⁻¹ : Kˣ) : K) • ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [Units.val_mul, hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal]
  have hcu : ((u⁻¹ : Kˣ) : K) * c = 1 := by
    rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hc0]
  have hB : (A : GL (Fin r ⊕ Fin r) K) * s ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff]
    change ((((A : GL (Fin r ⊕ Fin r) K) * s : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))ᵀ * formJ r K *
        (((A : GL (Fin r ⊕ Fin r) K) * s : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = formJ r K
    rw [hBmat, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      multiplier_spec A, smul_smul, hc]
    calc (((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) * (c * c)) • formJ r K
        = ((((u⁻¹ : Kˣ) : K) * c) * (((u⁻¹ : Kˣ) : K) * c)) • formJ r K := by ring_nf
      _ = formJ r K := by rw [hcu, one_mul, one_smul]
  have hconj : conjAut r K A = conjAut r K ⟨(A : GL (Fin r ⊕ Fin r) K) * s,
      statedSp_le_gsp hB⟩ := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [conjAut_proj, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_conjSp, coe_conjSp]
    change (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ =
      (A : GL (Fin r ⊕ Fin r) K) * s * g * ((A : GL (Fin r ⊕ Fin r) K) * s)⁻¹
    rw [mul_assoc (A : GL (Fin r ⊕ Fin r) K) s,
      ← Subgroup.mem_center_iff.mp hscent (g : GL (Fin r ⊕ Fin r) K)]
    group
  rw [hconj]
  exact ⟨proj r K ⟨_, hB⟩, (conjAut_statedSp ⟨_, hB⟩).symm⟩

theorem sq_mem_inner_of_mem_spLinearAutGroup [NeZero r]
    {d : MulAut (StatedProj (StatedSp r K))} (hd : d ∈ spLinearAutGroup r K) :
    d ^ 2 ∈ inner (StatedProj (StatedSp r K)) := by
  obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hd
  rw [← map_pow]
  exact conjAut_mem_inner_of_isSquare ⟨(multiplier r K A : K), by
    rw [map_pow, Units.val_pow_eq_pow_val, sq]⟩

theorem relIndex_inner_spLinearAutGroup_dvd [NeZero r] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) :
    (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣
      Nat.gcd 2 (p ^ f - 1) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  by_cases hp2 : p = 2
  · subst hp2
    have hsq : ∀ a : K, IsSquare a :=
      FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    rw [Subgroup.relIndex_eq_one.mpr fun d hd => by
      obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hd
      exact conjAut_mem_inner_of_isSquare (hsq _)]
    exact one_dvd _
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  rw [hgcd, Subgroup.relIndex_dvd_two_iff]
  by_cases hex : ∃ A₀ : gsp r K, ¬IsSquare (multiplier r K A₀ : K)
  · obtain ⟨A₀, hA₀⟩ := hex
    refine ⟨conjAut r K A₀, conjAut_mem_spLinearAutGroup A₀, fun b hb => ?_⟩
    obtain ⟨B, rfl⟩ := mem_spLinearAutGroup_iff.mp hb
    by_cases hB : IsSquare (multiplier r K B : K)
    · exact Or.inr (conjAut_mem_inner_of_isSquare hB)
    · left
      rw [← map_mul]
      apply conjAut_mem_inner_of_isSquare
      rw [map_mul, Units.val_mul, ← quadraticChar_one_iff_isSquare
        (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)), map_mul,
        quadraticChar_neg_one_iff_not_isSquare.mpr hB,
        quadraticChar_neg_one_iff_not_isSquare.mpr hA₀]
      norm_num
  · simp only [not_exists, not_not] at hex
    refine ⟨1, one_mem _, fun b hb => Or.inr ?_⟩
    obtain ⟨B, rfl⟩ := mem_spLinearAutGroup_iff.mp hb
    exact conjAut_mem_inner_of_isSquare (hex B)

theorem exists_fieldAut_inv_mul_mem {x : MulAut (StatedProj (StatedSp r K))}
    (hx : x ∈ spSemilinearAutGroup r K) :
    ∃ σ : K ≃+* K, (fieldAut r K σ)⁻¹ * x ∈ spLinearAutGroup r K := by
  obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hx
  refine ⟨σ, ?_⟩
  have h : (fieldAut r K σ)⁻¹ * (conjAut r K A * fieldAut r K σ) =
      fieldAut r K σ⁻¹ * conjAut r K A * (fieldAut r K σ⁻¹)⁻¹ := by
    rw [map_inv, inv_inv]
    group
  rw [h, fieldAut_mul_conjAut_mul_inv]
  exact conjAut_mem_spLinearAutGroup _

theorem relIndex_spLinearAutGroup_dvd [NeZero r] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) :
    (spLinearAutGroup r K).relIndex (spSemilinearAutGroup r K) ∣ f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  obtain ⟨-, -, hnorm, -⟩ :=
    standard_outer_quotient (K := K) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  set D' := (spLinearAutGroup r K).subgroupOf (spSemilinearAutGroup r K)
  let ρ : (K ≃+* K) →* spSemilinearAutGroup r K ⧸ D' :=
    (QuotientGroup.mk' D').comp ((fieldAut r K).codRestrict _ fieldAut_mem_spSemilinearAutGroup)
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨σ, hσ⟩ := exists_fieldAut_inv_mul_mem x.2
    refine ⟨σ, ?_⟩
    change (QuotientGroup.mk _ : spSemilinearAutGroup r K ⧸ D') = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hσ
  rw [Subgroup.relIndex, Subgroup.index, ← hcard]
  exact Subgroup.card_dvd_of_surjective hρ

theorem index_spSemilinearAutGroup_dvd_two [Finite K] (hr : 2 ≤ r) :
    (spSemilinearAutGroup r K).index ∣ 2 := by
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · obtain ⟨-, -, -, hindex⟩ := kernel_generation (K := K)
    have hne : (spSemilinearAutGroup 2 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain h | h : (spSemilinearAutGroup 2 K).index = 1 ∨
        (spSemilinearAutGroup 2 K).index = 2 := by omega
    · rw [h]
      exact one_dvd 2
    · rw [h]
  · rw [(automorphism_generation (K := K) hr3).1, Subgroup.index_top]
    exact one_dvd 2

theorem sq_mem_spSemilinearAutGroup [Finite K] (hr : 2 ≤ r)
    (x : MulAut (StatedProj (StatedSp r K))) : x ^ 2 ∈ spSemilinearAutGroup r K := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (index_spSemilinearAutGroup_dvd_two (K := K) hr)
    with h | h
  · rw [Subgroup.index_eq_one.mp h]
    exact Subgroup.mem_top _
  · exact Subgroup.sq_mem_of_index_two h x

theorem isCyclic_of_le_of_forall_odd {Y : Type*} [Group Y] {D E V : Subgroup Y}
    [(D.subgroupOf E).Normal] [IsCyclic (E ⧸ D.subgroupOf E)] (hD : ∀ d ∈ D, d ^ 2 = 1)
    (hVE : V ≤ E) (hV : ∀ v ∈ V, Odd (orderOf v)) : IsCyclic V := by
  refine isCyclic_of_injective
    ((QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion hVE)) ?_
  rw [injective_iff_map_eq_one]
  intro v hv
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hv
  have hdvd : orderOf (v : Y) ∣ 2 := orderOf_dvd_of_pow_eq_one (hD _ hv)
  have hodd := hV v v.2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Subtype.ext (orderOf_eq_one_iff.mp h)
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem outer_isCyclic_of_isPGroup {p f ℓ : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hr : 2 ≤ r) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {V : Subgroup (Outer (StatedProj (StatedSp r K)))} (hV : IsPGroup ℓ V) : IsCyclic V := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : NeZero r := ⟨by omega⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set π := QuotientGroup.mk' (inner (StatedProj (StatedSp r K))) with hπ
  set Eb := (spSemilinearAutGroup r K).map π with hEb
  set Db := (spLinearAutGroup r K).map π with hDb
  obtain ⟨-, -, hnormD, -⟩ := standard_outer_quotient (K := K) (by omega : 1 ≤ r)
  have hDE : ∀ x ∈ spSemilinearAutGroup r K, ∀ d ∈ spLinearAutGroup r K,
      x * d * x⁻¹ ∈ spLinearAutGroup r K := fun x hx d hd => by
    have h := hnormD.conj_mem ⟨d, spLinearAutGroup_le_spSemilinearAutGroup hd⟩
      (by rwa [Subgroup.mem_subgroupOf]) ⟨x, hx⟩
    rwa [Subgroup.mem_subgroupOf] at h
  have : (Db.subgroupOf Eb).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d, hd, hdn⟩ := hn
    obtain ⟨x, hx, hxg⟩ := g.2
    refine ⟨x * d * x⁻¹, hDE x hx d hd, ?_⟩
    rw [map_mul, map_mul, map_inv, hdn, hxg, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]⟩
  obtain ⟨φ, -, -, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ, hφ⟩
  have : IsCyclic (Eb ⧸ Db.subgroupOf Eb) := by
    let ρ : (K ≃+* K) →* Eb ⧸ Db.subgroupOf Eb :=
      (QuotientGroup.mk' (Db.subgroupOf Eb)).comp ((π.comp (fieldAut r K)).codRestrict Eb
        fun σ => Subgroup.mem_map_of_mem π (fieldAut_mem_spSemilinearAutGroup σ))
    refine isCyclic_of_surjective ρ fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, hx, hxg⟩ := g.2
    obtain ⟨σ, hσ⟩ := exists_fieldAut_inv_mul_mem hx
    refine ⟨σ, ?_⟩
    change (QuotientGroup.mk _ : Eb ⧸ Db.subgroupOf Eb) = QuotientGroup.mk g
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨(fieldAut r K σ)⁻¹ * x, hσ, ?_⟩
    rw [map_mul, map_inv, hxg, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hD2 : ∀ d ∈ Db, d ^ 2 = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact sq_mem_inner_of_mem_spLinearAutGroup hd
  have hodd : ∀ v ∈ V, Odd (orderOf v) := fun v hv => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hV ⟨v, hv⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
  have hVE : V ≤ Eb := fun v hv => by
    obtain ⟨x, rfl⟩ := (show Function.Surjective π from QuotientGroup.mk'_surjective _) v
    obtain ⟨m, hm⟩ := hodd _ hv
    have h2 : π x ^ 2 ∈ Eb := ⟨x ^ 2, sq_mem_spSemilinearAutGroup hr x, by rw [map_pow]⟩
    have hv' : π x = (π x ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf (π x) + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hv']
    exact Eb.pow_mem h2 _
  exact isCyclic_of_le_of_forall_odd hD2 hVE hodd

theorem outer_card_dvd {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hr : 2 ≤ r) :
    Nat.card (Outer (StatedProj (StatedSp r K))) ∣ 2 * f * Nat.gcd 2 (p ^ f - 1) ∧
      (3 ≤ r → Nat.card (Outer (StatedProj (StatedSp r K))) ∣ f * Nat.gcd 2 (p ^ f - 1)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hID, -⟩ := standard_outer_quotient (K := K) (by omega : 1 ≤ r)
  have hID' : inner (StatedProj (StatedSp r K)) ≤ spLinearAutGroup r K := hID
  have hidx : Nat.card (Outer (StatedProj (StatedSp r K))) =
      (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) *
        ((spLinearAutGroup r K).relIndex (spSemilinearAutGroup r K) *
          (spSemilinearAutGroup r K).index) := by
    rw [relIndex_mul_index spLinearAutGroup_le_spSemilinearAutGroup, relIndex_mul_index hID']
    rfl
  have ha := relIndex_inner_spLinearAutGroup_dvd (r := r) hp hf hK
  have hb := relIndex_spLinearAutGroup_dvd (r := r) hp hf hK
  refine ⟨?_, fun hr3 => ?_⟩
  · rw [hidx]
    have h := Nat.mul_dvd_mul ha
      (Nat.mul_dvd_mul hb (index_spSemilinearAutGroup_dvd_two (K := K) hr))
    rwa [show Nat.gcd 2 (p ^ f - 1) * (f * 2) = 2 * f * Nat.gcd 2 (p ^ f - 1) by ring] at h
  · rw [hidx, Subgroup.index_eq_one.mpr (automorphism_generation (K := K) hr3).1, mul_one,
      mul_comm f]
    exact Nat.mul_dvd_mul ha hb

theorem outer_isCyclic_of_even {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hr : 3 ≤ r) (heven : Even (p ^ f)) :
    IsCyclic (Outer (StatedProj (StatedSp r K))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : NeZero r := ⟨by omega⟩
  have hDI : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) = 1 := by
    have h := relIndex_inner_spLinearAutGroup_dvd (r := r) hp hf hK
    have hgcd : Nat.gcd 2 (p ^ f - 1) = 1 := by
      have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
      obtain ⟨k, hk⟩ := heven
      exact Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
    rw [hgcd] at h
    exact Nat.dvd_one.mp h
  have hDle := Subgroup.relIndex_eq_one.mp hDI
  obtain ⟨φ, -, -, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ, hφ⟩
  refine isCyclic_of_surjective
    ((QuotientGroup.mk' (inner (StatedProj (StatedSp r K)))).comp (fieldAut r K)) fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ spSemilinearAutGroup r K := by
    rw [(automorphism_generation (K := K) hr).1]
    exact Subgroup.mem_top x
  obtain ⟨σ, hσ⟩ := exists_fieldAut_inv_mul_mem hx
  exact ⟨σ, QuotientGroup.eq.mpr (hDle hσ)⟩

theorem perfect_symplectic_central_quotient_outer_prime_control {p f r : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hr : 2 ≤ r) {K : Type} [Field K] (hK : Nat.card K = p ^ f)
    (J : Type*) [Group J] [Group.IsPerfect J]
    (hJ : Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSp r K))) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ S : Sylow ℓ (Outer J), IsCyclic S) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.pRank ℓ (Outer J) ≤ 1) ∧
    Nat.card (Outer J) ∣ 2 * f * Nat.gcd 2 (p ^ f - 1) ∧
    (3 ≤ r → Nat.card (Outer J) ∣ f * Nat.gcd 2 (p ^ f - 1)) ∧
    (3 ≤ r → Even (p ^ f) → IsCyclic (Outer J)) := by
  obtain ⟨e⟩ := hJ
  obtain ⟨⟨E, -⟩, -⟩ := outer_isomorphism e
  set ι : Outer J →* Outer (StatedProj (StatedSp r K)) :=
    E.toMonoidHom.comp (outerCenterQuotientHom J) with hιdef
  have hι : Function.Injective ι := E.injective.comp (perfect_central_quotient_Schreier J).1
  have hcyc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ V : Subgroup (Outer J), IsPGroup ℓ V →
      IsCyclic V := by
    intro ℓ hℓ hℓ2 V hV
    have := outer_isCyclic_of_isPGroup hp hf hK hr hℓ hℓ2 (hV.map ι)
    exact isCyclic_of_surjective (V.equivMapOfInjective ι hι).symm (MulEquiv.surjective _)
  have hcard := outer_card_dvd hp hf hK hr
  refine ⟨fun ℓ hℓ hℓ2 S => hcyc ℓ hℓ hℓ2 S S.isPGroup', fun ℓ hℓ hℓ2 => ?_,
    (Subgroup.card_dvd_of_injective ι hι).trans hcard.1,
    fun hr3 => (Subgroup.card_dvd_of_injective ι hι).trans (hcard.2 hr3), fun hr3 heven => ?_⟩
  ·
    apply csSup_le'
    rintro d ⟨A, hA, hAcard⟩
    have := hcyc ℓ hℓ hℓ2 A (IsPGroup.of_card hAcard)
    have hexp : Monoid.exponent A ∣ ℓ := IsElementaryAbelian.exponent_dvd_p ℓ A
    rw [IsCyclic.exponent_eq_card, hAcard] at hexp
    exact (Nat.pow_dvd_pow_iff_le_right hℓ.one_lt).mp (by rwa [pow_one])
  · have := outer_isCyclic_of_even hp hf hK hr3 heven
    exact isCyclic_of_injective ι hι

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
