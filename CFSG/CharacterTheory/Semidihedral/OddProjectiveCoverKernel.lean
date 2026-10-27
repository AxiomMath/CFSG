module

public import CFSG.CharacterTheory.Semidihedral.MatrixTorus
public import CFSG.CharacterTheory.Semidihedral.SquareInvariantAlternating
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public noncomputable section

namespace CFSG.Semidihedral.OddProjectiveCoverKernel

open Matrix CFSG.Open
open CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.ShultStronglyClosedTI
open scoped commutatorElement IsMulCommutative MatrixGroups

universe u v w

variable (K : Type u) [Field K]

abbrev S := NativeScalarProjective K 2

@[expose] def rootHom : Multiplicative K →* S K :=
  (scalarQuotient K 2).comp (linearCoverRoot (K := K)).toMonoidHom

@[expose] def U : Subgroup (S K) := (rootHom K).range

theorem rootHom_apply (t : K) :
    rootHom K (Multiplicative.ofAdd t) = scalarQuotient K 2 (linearCoverRoot t) := rfl

theorem root_scalar_iff (t : K) :
    linearCoverRoot t ∈ nativeScalarKernel K 2 ↔ t = 0 := by
  rw [nativeScalarKernel_eq_center]
  constructor
  · intro ht
    obtain ⟨a, _, ha⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ht
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) ha
    simpa using h.symm
  · rintro rfl
    rw [AddChar.map_zero_eq_one]
    exact Subgroup.one_mem _

theorem rootHom_injective : Function.Injective (rootHom K) := by
  apply (rootHom K).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro t ht
  have hq : scalarQuotient K 2 (linearCoverRoot t.toAdd) = 1 := ht
  have hs : linearCoverRoot t.toAdd ∈ nativeScalarKernel K 2 :=
    (QuotientGroup.eq_one_iff _).mp hq
  exact Subgroup.mem_bot.mpr (congrArg Multiplicative.ofAdd
    ((root_scalar_iff K t.toAdd).mp hs))

@[expose] def rootEquiv : Multiplicative K ≃* U K :=
  MulEquiv.ofBijective (rootHom K).rangeRestrict
    ⟨fun _ _ h => rootHom_injective K (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

theorem U_card : Nat.card (U K) = Nat.card K :=
  (Nat.card_congr (rootEquiv K).toEquiv).symm

theorem scalar_membership (g : SpecialLinearGroup (Fin 2) K) :
    g ∈ nativeScalarKernel K 2 ↔ g = 1 ∨ g = minusIdentity K := by
  rw [nativeScalarKernel_eq_center]
  exact mem_center_iff_eq_one_or_minusIdentity K g

theorem S_card [Finite K] (hK : ringChar K ≠ 2) :
    Nat.card (S K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
  have h := (nativeScalarKernel K 2).card_eq_card_quotient_mul_card_subgroup
  rw [nativeScalarKernel_two_card K hK, CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup] at h
  exact Nat.eq_div_of_mul_eq_right (by decide) (by simpa [mul_comm] using h.symm)

theorem U_elementary {p : ℕ} [CharP K p] :
    IsElemAbelian p (U K) := by
  refine ⟨⟨⟨fun a b => (rootEquiv K).symm.injective ?_⟩⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_comm _ _
  · rintro g ⟨t, rfl⟩
    rw [← map_pow]
    have ht : t ^ p = 1 := by
      apply Multiplicative.ext
      change p • t.toAdd = 0
      rw [nsmul_eq_mul, CharP.cast_eq_zero K p, zero_mul]
    rw [ht, map_one]

theorem diagonal_conj_root (a : Kˣ) (t : K) :
    scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero) *
      rootHom K (Multiplicative.ofAdd t) *
      (scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero))⁻¹ =
        rootHom K (Multiplicative.ofAdd ((a : K) ^ 2 * t)) := by
  rw [rootHom_apply, rootHom_apply, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (scalarQuotient K 2) (linearCoverDiagonal_conj_root (a : K) a.ne_zero t)

theorem defining_not_dvd_sq_sub_one {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) : ¬p ∣ (p ^ f) ^ 2 - 1 := by
  intro h
  have hp : p.Prime := Fact.out
  have hdiv : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by decide)
  have hone : p ∣ 1 := by
    have hsub := Nat.dvd_sub hdiv h
    have hpos : 0 < (p ^ f) ^ 2 := pow_pos (pow_pos hp.pos f) 2
    simpa [show (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 by omega] using hsub
  exact hp.not_dvd_one hone

@[expose] def rootSylow [Finite K] {p f : ℕ} [Fact p.Prime]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) :
    Sylow p (S K) := by
  have hpgroup : IsPGroup p (U K) := IsPGroup.of_card (n := f) (by rw [U_card, hcard])
  have hindex : (U K).index * 2 = Nat.card K ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K))
    have h := (U K).index_mul_card
    have hs := (nativeScalarKernel K 2).card_eq_card_quotient_mul_card_subgroup
    rw [nativeScalarKernel_two_card K hchar, CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup] at hs
    rw [U_card] at h
    calc
      Nat.card K * ((U K).index * 2) = ((U K).index * Nat.card K) * 2 := by ac_rfl
      _ = Nat.card (S K) * 2 := by rw [h]
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := hs.symm
  have hno : ¬p ∣ (U K).index := by
    intro h
    apply defining_not_dvd_sq_sub_one (p := p) (f := f) hf
    rw [← hcard, ← hindex]
    exact dvd_mul_of_dvd_left h 2
  exact hpgroup.toSylow hno

theorem rootSylow_coe [Finite K] {p f : ℕ} [Fact p.Prime]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) :
    (rootSylow K hchar hf hcard : Subgroup (S K)) = U K := rfl

theorem diagonal_normalizes (a : Kˣ) :
    scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero) ∈
      Subgroup.normalizer (U K : Set (S K)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd ((a : K) ^ 2 * t.toAdd),
      (diagonal_conj_root K a t.toAdd).symm⟩
  · intro hg
    obtain ⟨t, ht⟩ := hg
    refine ⟨Multiplicative.ofAdd (((a⁻¹ : Kˣ) : K) ^ 2 * t.toAdd), ?_⟩
    have hconj := diagonal_conj_root K a
      (((a⁻¹ : Kˣ) : K) ^ 2 * t.toAdd)
    have hparam : (a : K) ^ 2 * (((a⁻¹ : Kˣ) : K) ^ 2 * t.toAdd) = t.toAdd := by
      simp [pow_two, mul_assoc]
    rw [hparam] at hconj
    change _ = rootHom K t at hconj
    rw [ht] at hconj
    exact mul_left_cancel (mul_right_cancel hconj)

@[expose] def diagonalHom : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun a := SpecialLinearGroup.diag2 (a : K) a.ne_zero
  map_one' := by
    apply Subtype.ext
    rw [SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change _ = _ * _
    rw [SpecialLinearGroup.diag2_coe', SpecialLinearGroup.diag2_coe',
      SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, _root_.mul_inv_rev, mul_comm]

theorem diagonalHom_injective : Function.Injective (diagonalHom K) := by
  intro a b h
  apply Units.ext
  have hm := congrArg (fun X : SpecialLinearGroup (Fin 2) K => X.val 0 0) h
  simpa [diagonalHom, SpecialLinearGroup.diag2_coe'] using hm

@[expose] def splitTorus : Subgroup (SpecialLinearGroup (Fin 2) K) := (diagonalHom K).range

theorem splitTorus_cyclic [Finite K] : IsCyclic (splitTorus K) :=
  isCyclic_of_surjective (diagonalHom K).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem splitTorus_card : Nat.card (splitTorus K) = Nat.card K - 1 := by
  change Nat.card (diagonalHom K).range = Nat.card K - 1
  rw [← Nat.card_congr ((diagonalHom K).ofInjective (diagonalHom_injective K)).toEquiv,
    Nat.card_units]

theorem scalar_le_splitTorus : nativeScalarKernel K 2 ≤ splitTorus K := by
  intro g hg
  rcases (scalar_membership K g).mp hg with rfl | rfl
  · exact Subgroup.one_mem _
  · refine ⟨-1, ?_⟩
    change SpecialLinearGroup.diag2 ((-1 : Kˣ) : K) (-1 : Kˣ).ne_zero = minusIdentity K
    apply Subtype.ext
    rw [SpecialLinearGroup.diag2_coe', minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem scalar_le_nonsplitTorus (a : Kˣ) :
    nativeScalarKernel K 2 ≤ MatrixTorus.Torus K a := by
  intro g hg
  rcases (scalar_membership K g).mp hg with rfl | rfl
  · exact Subgroup.one_mem _
  · have h : OddFieldSL2.minusIdentity K ∈ MatrixTorus.Torus K a :=
      (MatrixTorus.z K a).property
    simpa only [minusIdentity_eq_neg_one, OddFieldSL2.minusIdentity] using h

theorem projective_torus_card (hchar : ringChar K ≠ 2)
    (T : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hT : nativeScalarKernel K 2 ≤ T) :
    Nat.card (T.map (scalarQuotient K 2)) * 2 = Nat.card T := by
  let r := (scalarQuotient K 2).subgroupMap T
  have hker : r.ker = (nativeScalarKernel K 2).subgroupOf T := by
    ext x
    constructor
    · intro hx
      have hq : scalarQuotient K 2 x.val = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff x.val).mp hq
    · intro hx
      change r x = 1
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff x.val).mpr hx
  have hkcard : Nat.card r.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv,
      nativeScalarKernel_two_card K hchar]
  have h := Subgroup.card_ker_mul_card_of_surjective
    ((scalarQuotient K 2).subgroupMap_surjective T)
  rw [hkcard, mul_comm] at h
  exact h

theorem projective_torus_cyclic
    (T : Subgroup (SpecialLinearGroup (Fin 2) K)) (hT : IsCyclic T) :
    IsCyclic (T.map (scalarQuotient K 2)) := by
  let : IsCyclic T := hT
  exact isCyclic_of_surjective ((scalarQuotient K 2).subgroupMap T)
    ((scalarQuotient K 2).subgroupMap_surjective T)

theorem sylow_cyclic_of_full_torus {G : Type v} [Group G] [Finite G]
    {r : ℕ} [Fact r.Prime] (T : Subgroup G) (hcyclic : IsCyclic T)
    (hpart : (Nat.card T).factorization r = (Nat.card G).factorization r)
    (R : Sylow r G) : IsCyclic (R : Subgroup G) := by
  let : IsCyclic T := hcyclic
  let Q : Sylow r T := default
  let A : Subgroup G := (Q : Subgroup T).map T.subtype
  have hcard : Nat.card A = r ^ (Nat.card G).factorization r := by
    rw [Subgroup.card_map_of_injective T.subtype_injective,
      Sylow.card_eq_multiplicity, hpart]
  let P : Sylow r G := Sylow.ofCard A hcard
  have hAcyclic : IsCyclic A :=
    isCyclic_of_surjective (T.subtype.subgroupMap (Q : Subgroup T))
      (T.subtype.subgroupMap_surjective (Q : Subgroup T))
  have hPcyclic : IsCyclic (P : Subgroup G) := hAcyclic
  let : IsCyclic (P : Subgroup G) := hPcyclic
  exact isCyclic_of_injective (Sylow.equiv R P).toMonoidHom (Sylow.equiv R P).injective

theorem not_dvd_add_one_of_dvd_sub_one {q r : ℕ} (hq : 1 ≤ q)
    (hr : r.Prime) (hrtwo : r ≠ 2) (hdiv : r ∣ q - 1) : ¬r ∣ q + 1 := by
  intro h
  have htwo : r ∣ 2 := by
    have hd := Nat.dvd_sub h hdiv
    simpa [show q + 1 - (q - 1) = 2 by omega] using hd
  exact hrtwo ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp htwo)

theorem not_dvd_field_order {p f r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : r ≠ p) : ¬r ∣ p ^ f := by
  intro h
  exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))

theorem nativeSL_odd_sylow_cyclic [Finite K] {p f r : ℕ}
    (hp : p.Prime) (hchar : ringChar K ≠ 2)
    (hcard : Nat.card K = p ^ f) (hr : r.Prime) (hrtwo : r ≠ 2) (hrp : r ≠ p)
    (R : Sylow r (SpecialLinearGroup (Fin 2) K)) :
    IsCyclic (R : Subgroup (SpecialLinearGroup (Fin 2) K)) := by
  let : Fact r.Prime := ⟨hr⟩
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hm0 : Nat.card K - 1 ≠ 0 := by omega
  have ha0 : Nat.card K + 1 ≠ 0 := by omega
  have hrf : ¬r ∣ Nat.card K := hcard ▸ not_dvd_field_order hp hr hrp
  have hfactor : Nat.card (SpecialLinearGroup (Fin 2) K) =
      Nat.card K * ((Nat.card K - 1) * (Nat.card K + 1)) := by
    rw [CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup]
    congr 1
    have hm : Nat.card K - 1 + 1 = Nat.card K := Nat.sub_add_cancel (by omega)
    have hsq : Nat.card K ^ 2 - 1 + 1 = Nat.card K ^ 2 :=
      Nat.sub_add_cancel (by nlinarith)
    nlinarith
  by_cases hm : r ∣ Nat.card K - 1
  · have ha : ¬r ∣ Nat.card K + 1 := not_dvd_add_one_of_dvd_sub_one (by omega) hr hrtwo hm
    apply sylow_cyclic_of_full_torus (splitTorus K) (splitTorus_cyclic K) _ R
    rw [splitTorus_card, hfactor,
      Nat.factorization_mul hq0 (mul_ne_zero hm0 ha0), Nat.factorization_mul hm0 ha0]
    simp [Nat.factorization_eq_zero_of_not_dvd hrf,
      Nat.factorization_eq_zero_of_not_dvd ha]
  · obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare hchar
    have hd0 : d ≠ 0 := fun h => hd (by rw [h]; exact ⟨0, by simp⟩)
    let a : Kˣ := -Units.mk0 d hd0
    have ha : ¬IsSquare (-(a : K)) := by simpa [a] using hd
    apply sylow_cyclic_of_full_torus (MatrixTorus.Torus K a)
      (MatrixTorus.nonsplit_torus_cyclic K a ha) _ R
    rw [MatrixTorus.nonsplit_torus_card K a ha, hfactor,
      Nat.factorization_mul hq0 (mul_ne_zero hm0 ha0), Nat.factorization_mul hm0 ha0]
    simp [Nat.factorization_eq_zero_of_not_dvd hrf,
      Nat.factorization_eq_zero_of_not_dvd hm]

theorem S_odd_sylow_cyclic [Finite K] {p f r : ℕ}
    (hp : p.Prime) (hchar : ringChar K ≠ 2)
    (hcard : Nat.card K = p ^ f) (hr : r.Prime) (hrtwo : r ≠ 2) (hrp : r ≠ p)
    (R : Sylow r (S K)) : IsCyclic (R : Subgroup (S K)) := by
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (scalarQuotient_surjective K 2) r R
  have hmap : (P : Subgroup (SpecialLinearGroup (Fin 2) K)).map (scalarQuotient K 2) =
      (R : Subgroup (S K)) := by
    rw [← Sylow.coe_mapSurjective (scalarQuotient_surjective K 2), hP]
  let : IsCyclic (P : Subgroup (SpecialLinearGroup (Fin 2) K)) :=
    nativeSL_odd_sylow_cyclic K hp hchar hcard hr hrtwo hrp P
  rw [← hmap]
  exact isCyclic_of_surjective ((scalarQuotient K 2).subgroupMap (P : Subgroup _))
    ((scalarQuotient K 2).subgroupMap_surjective (P : Subgroup _))

theorem odd_projective_linear_two_Sylow_data {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) :
    (nativeScalarKernel K 2 : Set (SpecialLinearGroup (Fin 2) K)) =
        {1, minusIdentity K} ∧
      Nat.card (S K) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      IsElemAbelian p (U K) ∧ Nat.card (U K) = p ^ f ∧
      (∃ P : Sylow p (S K), (P : Subgroup (S K)) = U K) ∧
      (∀ a : Kˣ,
        scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero) ∈
          Subgroup.normalizer (U K : Set (S K)) ∧
        ∀ t : K,
          scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero) *
              rootHom K (Multiplicative.ofAdd t) *
              (scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero))⁻¹ =
            rootHom K (Multiplicative.ofAdd ((a : K) ^ 2 * t))) ∧
      (∀ r : ℕ, r.Prime → Odd r → r ≠ p →
        ∀ R : Sylow r (S K), IsCyclic (R : Subgroup (S K))) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero f hp.ne_zero)
  let : Fintype K := Fintype.ofFinite K
  let : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine ⟨?_, ?_, U_elementary K, (U_card K).trans hcard,
    ⟨rootSylow K hchar hf hcard, rfl⟩,
    fun a => ⟨diagonal_normalizes K a, diagonal_conj_root K a⟩, ?_⟩
  · ext g
    exact (scalar_membership K g).trans (by simp)
  · rw [S_card K hchar, hcard]
  · intro r hr hrodd hrp R
    have hr2 : r ≠ 2 := by
      intro h
      subst r
      norm_num at hrodd
    exact S_odd_sylow_cyclic K hp hchar hcard hr hr2 hrp R

theorem odd_kernel_isPGroup_of_cyclic_sylows {E : Type v} {J : Type w} [Group E] [Finite E]
    [Group.IsPerfect E] [Group J] {p : ℕ} (hp : p.Prime)
    (pi : E →* J) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card pi.ker))
    (hcyclic : ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
      ∀ Q : Sylow r J, IsCyclic (Q : Subgroup J)) : IsPGroup p pi.ker := by
  let : Fact p.Prime := ⟨hp⟩
  have hnot : ∀ (r : ℕ), r.Prime → r ≠ p → ¬r ∣ Nat.card pi.ker := by
    intro r hr hrp hdiv
    by_cases hr2 : r = 2
    · subst r
      exact hodd.not_two_dvd_nat hdiv
    · let : Fact r.Prime := ⟨hr⟩
      let C : Sylow r pi.ker := default
      let Q : Sylow r J := default
      have hC : (C : Subgroup pi.ker) = ⊥ :=
        central_cover_cyclic_sylow_kernel_eq_bot pi hpi hcentral C Q
          (hcyclic r hr hr2 hrp Q)
      have hcardC : Nat.card (C : Subgroup pi.ker) = 1 := by rw [hC, Subgroup.card_bot]
      rw [Sylow.card_eq_multiplicity] at hcardC
      have hzero : (Nat.card pi.ker).factorization r = 0 :=
        (Nat.pow_eq_one.mp hcardC).resolve_left hr.ne_one
      have hpos := hr.factorization_pos_of_dvd (Nat.card_pos (α := pi.ker)).ne' hdiv
      omega
  have hfactor : (Nat.card pi.ker).factorization =
      Finsupp.single p ((Nat.card pi.ker).factorization p) := by
    ext r
    by_cases hrp : r = p
    · subst r
      simp
    · rw [Finsupp.single_eq_of_ne hrp]
      by_cases hr : r.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (hnot r hr hrp)
      · exact Nat.factorization_eq_zero_of_not_prime _ hr
  exact IsPGroup.of_card (Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne' hfactor)

@[expose] def preimageSylow [Finite K] {p f : ℕ} [Fact p.Prime]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    {E : Type v} [Group E] (pi : E →* S K) (hpi : Function.Surjective pi)
    (hpker : IsPGroup p pi.ker) : Sylow p E :=
  (rootSylow K hchar hf hcard).comapOfKerIsPGroup pi hpker
    (by rw [pi.range_eq_top_of_surjective hpi]; exact le_top)

theorem preimageSylow_coe [Finite K] {p f : ℕ} [Fact p.Prime]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    {E : Type v} [Group E] (pi : E →* S K) (hpi : Function.Surjective pi)
    (hpker : IsPGroup p pi.ker) :
    (preimageSylow K hchar hf hcard pi hpi hpker : Subgroup E) = (U K).comap pi := rfl

theorem root_preimage_commutator_mem_kernel {E : Type v} [Group E]
    (pi : E →* S K) {x y : E} (hx : pi x ∈ U K) (hy : pi y ∈ U K) :
    ⁅x, y⁆ ∈ pi.ker := by
  change pi ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]

theorem preimage_derived_eq_kernel [Finite K] {p f : ℕ} [Fact p.Prime]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hpker : IsPGroup p pi.ker) :
    (commutator ((U K).comap pi)).map ((U K).comap pi).subtype = pi.ker := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact root_preimage_commutator_mem_kernel K pi x.property y.property
  · exact central_pSubgroup_le_sylow_derived
      (preimageSylow K hchar hf hcard pi hpi hpker) pi.ker hcentral hpker

theorem root_preimage_commutator_central {E : Type v} [Group E]
    (pi : E →* S K) (hcentral : pi.ker ≤ Subgroup.center E)
    {x y : E} (hx : pi x ∈ U K) (hy : pi y ∈ U K) :
    ⁅x, y⁆ ∈ Subgroup.center E :=
  hcentral (root_preimage_commutator_mem_kernel K pi hx hy)

theorem root_preimage_pow_central {p : ℕ} [CharP K p]
    {E : Type v} [Group E] (pi : E →* S K)
    (hcentral : pi.ker ≤ Subgroup.center E) {x : E} (hx : pi x ∈ U K) :
    x ^ p ∈ Subgroup.center E := by
  apply hcentral
  change pi (x ^ p) = 1
  rw [map_pow]
  exact (U_elementary K).2 (pi x) hx

theorem root_preimage_commutator_pow {p : ℕ} [CharP K p]
    {E : Type v} [Group E] (pi : E →* S K)
    (hcentral : pi.ker ≤ Subgroup.center E) {x y : E}
    (hx : pi x ∈ U K) (hy : pi y ∈ U K) : ⁅x, y⁆ ^ p = 1 := by
  have hc := root_preimage_commutator_central K pi hcentral hx hy
  have hp := root_preimage_pow_central K pi hcentral hx
  rw [← CFSG.LocalAnalysis.ComponentInitial.commutatorElement_pow_left_of_mem_center hc]
  have hxp : Commute (x ^ p) y := (Subgroup.mem_center_iff.mp hp y).symm
  exact hxp.commutator_eq

theorem kernel_elementary [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hpker : IsPGroup p pi.ker) :
    CFSG.IsElementaryAbelian p pi.ker := by
  let P : Subgroup E := (U K).comap pi
  have heq : (commutator P).map P.subtype = pi.ker :=
    preimage_derived_eq_kernel K hchar hf hcard pi hpi hcentral hpker
  have hc (z : P) (hz : z ∈ Subgroup.closure (commutatorSet P)) :
      (z : E) ∈ Subgroup.center E := by
    apply hcentral
    rw [← heq]
    exact Subgroup.mem_map.mpr ⟨z, (commutator_eq_closure P).symm ▸ hz, rfl⟩
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
        ((Subgroup.mem_center_iff.mp (hcentral a.property) b.val).symm)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro c
  apply Subtype.ext
  have hcm : (c : E) ∈ (commutator P).map P.subtype := heq.symm ▸ c.property
  obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hcm
  change (d : E) = (c : E) at hdc
  change (c : E) ^ p = 1
  rw [← hdc]
  rw [commutator_eq_closure] at hd
  exact Subgroup.closure_induction (k := commutatorSet P) (x := d)
    (p := fun (z : P) _ => (z : E) ^ p = 1)
    (fun z hz => by
      obtain ⟨x, y, rfl⟩ := hz
      exact root_preimage_commutator_pow K pi hcentral x.property y.property)
    (by simp)
    (fun x y hx _ ihx ihy => by
      have hxy : Commute (x : E) (y : E) :=
        (Subgroup.mem_center_iff.mp (hc x hx) y.val).symm
      change ((x : E) * (y : E)) ^ p = 1
      rw [hxy.mul_pow, ihx, ihy, one_mul])
    (fun x _ ihx => by
      change ((x : E)⁻¹) ^ p = 1
      rw [inv_pow, ihx, inv_one]) hd

@[expose] def rootLift {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (t : K) : E :=
  (hpi (rootHom K (Multiplicative.ofAdd t))).choose

theorem rootLift_image {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (t : K) :
    pi (rootLift K pi hpi t) = rootHom K (Multiplicative.ofAdd t) :=
  (hpi (rootHom K (Multiplicative.ofAdd t))).choose_spec

@[expose] def coverCommutator {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (x y : K) : pi.ker :=
  ⟨⁅rootLift K pi hpi x, rootLift K pi hpi y⁆,
    root_preimage_commutator_mem_kernel K pi
      (by rw [rootLift_image]; exact ⟨Multiplicative.ofAdd x, rfl⟩)
      (by rw [rootLift_image]; exact ⟨Multiplicative.ofAdd y, rfl⟩)⟩

theorem coverCommutator_eq_of_lifts {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E)
    {x y : K} {a b : E}
    (ha : pi a = rootHom K (Multiplicative.ofAdd x))
    (hb : pi b = rootHom K (Multiplicative.ofAdd y)) :
    (coverCommutator K pi hpi x y : E) = ⁅a, b⁆ :=
  linearCover_commutator_lift_independent pi hcentral
    ((rootLift_image K pi hpi x).trans ha.symm)
    ((rootLift_image K pi hpi y).trans hb.symm)

theorem coverCommutator_add_left {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E)
    (x x' y : K) :
    coverCommutator K pi hpi (x + x') y =
      coverCommutator K pi hpi x y * coverCommutator K pi hpi x' y := by
  apply Subtype.ext
  have h := coverCommutator_eq_of_lifts K pi hpi hcentral
    (x := x + x') (y := y)
    (a := rootLift K pi hpi x * rootLift K pi hpi x')
    (b := rootLift K pi hpi y)
    (by rw [map_mul, rootLift_image, rootLift_image, ← map_mul]; rfl)
    (rootLift_image K pi hpi y)
  rw [h]
  exact CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_left_of_mem_center
    (hcentral (coverCommutator K pi hpi x' y).property)

theorem coverCommutator_add_right {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E)
    (x y y' : K) :
    coverCommutator K pi hpi x (y + y') =
      coverCommutator K pi hpi x y * coverCommutator K pi hpi x y' := by
  apply Subtype.ext
  have h := coverCommutator_eq_of_lifts K pi hpi hcentral
    (x := x) (y := y + y')
    (a := rootLift K pi hpi x)
    (b := rootLift K pi hpi y * rootLift K pi hpi y')
    (rootLift_image K pi hpi x)
    (by rw [map_mul, rootLift_image, rootLift_image, ← map_mul]; rfl)
  rw [h]
  exact CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_right_of_mem_center'
    (hcentral (coverCommutator K pi hpi x y').property)

theorem coverCommutator_self {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (x : K) : coverCommutator K pi hpi x x = 1 :=
  Subtype.ext (commutatorElement_self _)

theorem coverCommutator_zero_left {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E) (y : K) :
    coverCommutator K pi hpi 0 y = 1 := by
  apply Subtype.ext
  have h := coverCommutator_eq_of_lifts K pi hpi hcentral
    (a := 1) (b := rootLift K pi hpi y)
    (by rw [map_one]; exact (map_one (rootHom K)).symm)
    (rootLift_image K pi hpi y)
  exact h.trans (commutatorElement_one_left _)

theorem coverCommutator_zero_right {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E) (x : K) :
    coverCommutator K pi hpi x 0 = 1 := by
  apply Subtype.ext
  have h := coverCommutator_eq_of_lifts K pi hpi hcentral
    (a := rootLift K pi hpi x) (b := 1)
    (rootLift_image K pi hpi x)
    (by rw [map_one]; exact (map_one (rootHom K)).symm)
  exact h.trans (commutatorElement_one_right _)

theorem coverCommutator_square_invariant {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E)
    (a : Kˣ) (x y : K) :
    coverCommutator K pi hpi ((a : K) ^ 2 * x) ((a : K) ^ 2 * y) =
      coverCommutator K pi hpi x y := by
  obtain ⟨e, he⟩ := hpi (scalarQuotient K 2 (SpecialLinearGroup.diag2 (a : K) a.ne_zero))
  have hx : pi ((MulAut.conj e) (rootLift K pi hpi x)) =
      rootHom K (Multiplicative.ofAdd ((a : K) ^ 2 * x)) := by
    simpa only [MulAut.conj_apply, map_mul, map_inv, he, rootLift_image] using
      diagonal_conj_root K a x
  have hy : pi ((MulAut.conj e) (rootLift K pi hpi y)) =
      rootHom K (Multiplicative.ofAdd ((a : K) ^ 2 * y)) := by
    simpa only [MulAut.conj_apply, map_mul, map_inv, he, rootLift_image] using
      diagonal_conj_root K a y
  apply Subtype.ext
  rw [coverCommutator_eq_of_lifts K pi hpi hcentral hx hy, ← map_commutatorElement]
  have hc := hcentral (coverCommutator K pi hpi x y).property
  change e * (coverCommutator K pi hpi x y : E) * e⁻¹ =
    (coverCommutator K pi hpi x y : E)
  rw [Subgroup.mem_center_iff.mp hc e, mul_inv_cancel_right]

@[expose] def coverCommutatorBiadditive {E : Type v} [Group E] (pi : E →* S K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center E)
    [IsMulCommutative pi.ker] : K →+ K →+ Additive pi.ker where
  toFun x :=
    { toFun y := Additive.ofMul (coverCommutator K pi hpi x y)
      map_zero' := congrArg Additive.ofMul (coverCommutator_zero_right K pi hpi hcentral x)
      map_add' y y' := congrArg Additive.ofMul
        (coverCommutator_add_right K pi hpi hcentral x y y') }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul (coverCommutator_zero_left K pi hpi hcentral y)
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul (coverCommutator_add_left K pi hpi hcentral x x' y)

@[expose] def coverCommutatorBilinear {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    {E : Type v} [Group E] (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) [CFSG.IsElementaryAbelian p pi.ker] :
    K →ₗ[ZMod p] K →ₗ[ZMod p] Additive pi.ker :=
  SquareInvariantAlternating.bilinearOfBiadditive p
    (coverCommutatorBiadditive K pi hpi hcentral)

theorem coverCommutatorBilinear_apply {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    {E : Type v} [Group E] (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) [CFSG.IsElementaryAbelian p pi.ker]
    (x y : K) :
    coverCommutatorBilinear K (p := p) pi hpi hcentral x y =
      Additive.ofMul (coverCommutator K pi hpi x y) := rfl

theorem coverCommutatorBilinear_isAlt {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    {E : Type v} [Group E] (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) [CFSG.IsElementaryAbelian p pi.ker] :
    (coverCommutatorBilinear K (p := p) pi hpi hcentral).IsAlt :=
  fun x => congrArg Additive.ofMul (coverCommutator_self K pi hpi x)

theorem coverCommutatorBilinear_square_invariant {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    {E : Type v} [Group E] (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) [CFSG.IsElementaryAbelian p pi.ker]
    (a : Kˣ) (x y : K) :
    coverCommutatorBilinear K (p := p) pi hpi hcentral ((a : K) ^ 2 * x) ((a : K) ^ 2 * y) =
      coverCommutatorBilinear K (p := p) pi hpi hcentral x y :=
  congrArg Additive.ofMul (coverCommutator_square_invariant K pi hpi hcentral a x y)

theorem coverCommutator_eq_one_of_not_nine [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hpodd : Odd p) (hchar : ringChar K ≠ 2)
    (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) (hnine : p ^ f ≠ 9)
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hpker : IsPGroup p pi.ker) :
    ∀ x y : K, coverCommutator K pi hpi x y = 1 := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : CFSG.IsElementaryAbelian p pi.ker :=
    kernel_elementary K hchar hf hcard pi hpi hcentral hpker
  let b := coverCommutatorBilinear K (p := p) pi hpi hcentral
  have hzero : b = 0 := SquareInvariantAlternating.square_invariant_alternating_eq_zero
    p f hpodd hf K hcard (Additive pi.ker) b
    (coverCommutatorBilinear_isAlt K (p := p) pi hpi hcentral)
    (coverCommutatorBilinear_square_invariant K (p := p) pi hpi hcentral) hnine
  intro x y
  have hvalue : Additive.ofMul (coverCommutator K pi hpi x y) = 0 :=
    congrArg (fun B : K →ₗ[ZMod p] K →ₗ[ZMod p] Additive pi.ker => B x y) hzero
  exact congrArg Additive.toMul hvalue

theorem kernel_eq_bot_of_not_nine [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hpodd : Odd p) (hchar : ringChar K ≠ 2)
    (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) (hnine : p ^ f ≠ 9)
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hpker : IsPGroup p pi.ker) : pi.ker = ⊥ := by
  let P : Subgroup E := (U K).comap pi
  have hcomm : IsMulCommutative P := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := a.property
    obtain ⟨y, hy⟩ := b.property
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hb := coverCommutator_eq_of_lifts K pi hpi hcentral
      (x := x.toAdd) (y := y.toAdd) hx.symm hy.symm
    exact hb.symm.trans (congrArg (fun c : pi.ker => (c : E))
      (coverCommutator_eq_one_of_not_nine K hpodd hchar hf hcard hnine
        pi hpi hcentral hpker x.toAdd y.toAdd))
  let : IsMulCommutative P := hcomm
  have heq := preimage_derived_eq_kernel K hchar hf hcard pi hpi hcentral hpker
  change (commutator P).map P.subtype = pi.ker at heq
  rw [commutator_eq_bot, Subgroup.map_bot] at heq
  exact heq.symm

theorem prime_power_nine {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hnine : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hdiv : p ∣ 9 := hnine ▸ dvd_pow_self p (by omega)
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    (hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by norm_num; exact hdiv))
  refine ⟨hp3, ?_⟩
  subst p
  exact Nat.pow_right_injective (by decide : 2 ≤ 3) (by simpa using hnine)

theorem kernel_bound_of_nine [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hchar : ringChar K ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    (hnine : p ^ f = 9) {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hpker : IsPGroup p pi.ker) :
    IsCyclic pi.ker ∧ Nat.card pi.ker ≤ 3 := by
  obtain ⟨hp3, hf2⟩ := prime_power_nine Fact.out hf hnine
  let C : Sylow p pi.ker := default
  let Q := rootSylow K hchar hf hcard
  have helem : IsElemAbelian p (Q : Subgroup (S K)) := U_elementary K
  have hQcard : Nat.card (Q : Subgroup (S K)) = p ^ 2 := by
    change Nat.card (U K) = p ^ 2
    rw [U_card, hcard, hf2]
  have hbound := central_cover_elementary_rank_two_sylow_kernel_bound pi hpi hcentral
    C Q helem hQcard
  have htop : IsPGroup p (⊤ : Subgroup pi.ker) := by
    intro x
    obtain ⟨n, hn⟩ := hpker x.val
    exact ⟨n, Subtype.ext hn⟩
  have hC : (C : Subgroup pi.ker) = ⊤ := top_unique (htop.le_sylow_of_normal C)
  rw [hC] at hbound
  let : IsCyclic (⊤ : Subgroup pi.ker) := hbound.1
  refine ⟨isCyclic_of_surjective (Subgroup.topEquiv (G := pi.ker)).toMonoidHom
    (Subgroup.topEquiv (G := pi.ker)).surjective, ?_⟩
  rw [← Nat.card_congr (Subgroup.topEquiv (G := pi.ker)).toEquiv]
  simpa only [hp3] using hbound.2

theorem odd_projective_cover_kernel_isPGroup {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card pi.ker)) :
    IsPGroup p pi.ker := by
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero f hp.ne_zero)
  have hdata := odd_projective_linear_two_Sylow_data K hp hpodd hf hcard
  apply odd_kernel_isPGroup_of_cyclic_sylows hp pi hpi hcentral hodd
  intro r hr hr2 hrp Q
  exact hdata.2.2.2.2.2.2 r hr (hr.odd_of_ne_two hr2) hrp Q

theorem odd_projective_linear_two_perfect_odd_cover_kernel {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (pi : E →* S K) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card pi.ker)) :
    (p ^ f ≠ 9 → pi.ker = ⊥) ∧
      (p ^ f = 9 → IsCyclic pi.ker ∧ Nat.card pi.ker ≤ 3) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero f hp.ne_zero)
  let : Fintype K := Fintype.ofFinite K
  let : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hpker := odd_projective_cover_kernel_isPGroup K hp hpodd hf hcard pi hpi hcentral hodd
  exact ⟨fun hnine => kernel_eq_bot_of_not_nine K hpodd hchar hf hcard hnine
      pi hpi hcentral hpker,
    fun hnine => kernel_bound_of_nine K hchar hf hcard hnine pi hpi hcentral hpker⟩

end CFSG.Semidihedral.OddProjectiveCoverKernel
