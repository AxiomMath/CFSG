module

public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizerOrdinary
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.AlgebraicGroups.E6RationalTwistedFaithful

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SecondGraphFull

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial (exists_frobenius_pow_eq ringAut_pow_apply_of_sq
  finite_field_automorphism_fixed_field_cardinality)

theorem card_eq_two_pow_two_mul {f : ℕ} {K : Type} (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card K = 2 ^ (2 * f) := by
  rw [hK, ← pow_mul, mul_comm]

section Fields

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_lift_ringEquiv (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (φ : k ≃+* k) :
    ∃ δ : K ≃+* K, ∀ c, δ (algebraMap k K c) = algebraMap k K (φ c) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨s, -, hφ, -⟩ := exists_frobenius_pow_eq hf hk φ
  obtain ⟨σ₂, hσ₂, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two
    (by omega : 1 ≤ 2 * f) (card_eq_two_pow_two_mul hK)
  exact ⟨σ₂ ^ s, fun c => by rw [ringAut_pow_apply_of_sq hσ₂, hφ, map_pow]⟩

theorem exists_restrict_ringEquiv (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (δ : K ≃+* K) :
    ∃ δk : k ≃+* k, ∀ c, algebraMap k K (δk c) = δ (algebraMap k K c) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨s, -, hδ, -⟩ := exists_frobenius_pow_eq (by omega) (card_eq_two_pow_two_mul hK) δ
  obtain ⟨σ₂, hσ₂, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hk
  exact ⟨σ₂ ^ s, fun c => by rw [ringAut_pow_apply_of_sq hσ₂, hδ, map_pow]⟩

theorem eq_one_or_eq_of_forall_algebraMap (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (δ : K ≃+* K)
    (hδ : ∀ c, δ (algebraMap k K c) = algebraMap k K c) : δ = 1 ∨ δ = σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨s, hs, hδs, -⟩ := exists_frobenius_pow_eq (by omega) (card_eq_two_pow_two_mul hK) δ
  obtain ⟨σ₂, hσ₂, hord, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hk
  have h1 : σ₂ ^ s = 1 := RingEquiv.ext fun c => (algebraMap k K).injective (by
    rw [ringAut_pow_apply_of_sq hσ₂, map_pow, ← hδs, hδ]
    rfl)
  obtain ⟨m, rfl⟩ : f ∣ s := hord ▸ orderOf_dvd_of_pow_eq_one h1
  have hm : m = 0 ∨ m = 1 := by
    rcases m with _ | _ | m
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      nlinarith
  rcases hm with hm | hm
  · refine Or.inl (RingEquiv.ext fun c => ?_)
    rw [hδs, hm, mul_zero, pow_zero, pow_one]
    rfl
  · refine Or.inr (RingEquiv.ext fun c => ?_)
    rw [hδs, hσ, hm, mul_one]

end Fields

section Twisted

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K] [Finite K]

theorem diagramMap_inv_conj_mem_twistedFixedGroup
    {L : Type} [Field L] {σ : L →+* L}
    {y : ModGL TwistTag.E6.tag L} (hy : y ∈ twistedFixedGroup TwistTag.E6 L σ) :
    (diagramMap TwistTag.E6 L)⁻¹ * y * diagramMap TwistTag.E6 L ∈
      twistedFixedGroup TwistTag.E6 L σ := by
  refine ⟨diagramMap_inv_conj_mem hy.1, ?_⟩
  have hP : twistHom TwistTag.E6 L σ (diagramMap TwistTag.E6 L) = diagramMap TwistTag.E6 L := by
    rw [twistHom_apply, units_map_entrywiseHom_diagramMap, mul_inv_cancel_right]
  have hy' : twistHom TwistTag.E6 L σ y = y := hy.2
  change twistHom TwistTag.E6 L σ ((diagramMap TwistTag.E6 L)⁻¹ * y * diagramMap TwistTag.E6 L) =
    (diagramMap TwistTag.E6 L)⁻¹ * y * diagramMap TwistTag.E6 L
  rw [map_mul, map_mul, map_inv, hP, hy']

theorem exists_conj_mul_of_mem_centralizer_graphFixedRootGroup
    (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (htC : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hβ : MulAut.conj (⟨_, htC⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) *
        fieldActor σ σ * β =
      β * (MulAut.conj (⟨_, htC⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) *
        fieldActor σ σ)) :
    ∃ x ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)),
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 * x =
        x * pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∧
      ∃ δ : K ≃+* K, ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (β h : ModGL TwistTag.E6.tag K) =
          x * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) * x⁻¹ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : ringChar k = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card hf hk
  obtain ⟨-, -, -, -, -, hcoeΔ, hcoeδ, hNF, -, hPσ, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, δ, hβnf⟩ := hNF β
  obtain ⟨x, hx⟩ : ∃ x : ModGL TwistTag.E6.tag K, x = (g : ModGL TwistTag.E6.tag K) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ModGL TwistTag.E6.tag K,
      T = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K := ⟨_, rfl⟩
  have hβx : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (β h : ModGL TwistTag.E6.tag K) = x * fieldActor σ δ h * x⁻¹ := fun h => by
    rw [hβnf, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hcoeΔ, hx, mul_inv_rev]
    simp only [mul_assoc]
  have hξ : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ((MulAut.conj (⟨_, htC⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) *
        fieldActor (t := TwistTag.E6) σ σ) h : ModGL TwistTag.E6.tag K) = T * h * T⁻¹ :=
      fun h => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hPσ, hT, mul_inv_rev]
    simp only [mul_assoc]
  have hδT : Units.map (entrywiseHom δ.toRingHom) T = T := by
    rw [hT]
    exact units_map_entrywiseHom_secondGraphRep δ.toRingHom
  have hFξ : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (fieldActor σ δ ((MulAut.conj (⟨_, htC⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) *
        fieldActor (t := TwistTag.E6) σ σ) h) : ModGL TwistTag.E6.tag K) =
          T * fieldActor σ δ h * T⁻¹ := fun h => by
    rw [hcoeδ, hξ, map_mul, map_mul, map_inv, hδT, hcoeδ]
  have hzC := conj_commute_of_commute hβx hξ hFξ hβ
  set L := AlgebraicClosure K
  obtain ⟨Fr, hFr⟩ := exists_frobenius_of_ringChar k L hk2
  have hFr' : ∀ c, Fr c = c ^ 2 ^ f := fun c => by rw [hFr, hk]
  have hL2 : ringChar L = 2 := by
    have : CharP k 2 := ringChar.of_eq hk2
    have : CharP L 2 := charP_of_injective_algebraMap (algebraMap k L).injective 2
    exact ringChar.eq L 2
  obtain ⟨hHR, -, hRC, -⟩ :=
    CFSG.LieType.AlgebraicGroups.E6_rational_twisted_fixed_group_faithful_action
      Nat.prime_two hf K hK σ.toRingHom hσ L Fr hFr'
  have hcomp : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hFr', ← map_pow, ← hσ]
      rfl
  have hgR : baseChangeGL (algebraMap K L) (g : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 L Fr := hHR ⟨g, g.2, rfl⟩
  have hDR : baseChangeGL (algebraMap K L)
      (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∈
        twistedFixedGroup TwistTag.E6 L Fr := by
    refine ⟨?_, ?_⟩
    · rw [baseChangeGL_rootDiagUnit]
      exact (exceptional_Lang_adjoint_diagonal_lift _ L _).1
    · change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L)
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))) = _
      rw [twistHom_baseChangeGL (algebraMap K L) hcomp, twistHom_rootDiagUnit (compatDiag_perm u)]
      rfl
  have hxR : baseChangeGL (algebraMap K L) x ∈ twistedFixedGroup TwistTag.E6 L Fr := by
    rw [hx, map_mul]
    exact mul_mem hgR hDR
  have htR : pinnedX TwistTag.E6.tag L e6HighestRoot 1 ∈ twistedFixedGroup TwistTag.E6 L Fr := by
    rw [← baseChangeGL_pinnedX_one (algebraMap K L)]
    exact hHR ⟨_, htC, rfl⟩
  have hTL : baseChangeGL (algebraMap K L) T =
      pinnedX TwistTag.E6.tag L e6HighestRoot 1 * diagramMap TwistTag.E6 L := by
    rw [hT, baseChangeGL_secondGraphRep]
  have hzR : baseChangeGL (algebraMap K L) ((T * x)⁻¹ * (x * T)) ∈
      twistedFixedGroup TwistTag.E6 L Fr := by
    rw [show (T * x)⁻¹ * (x * T) = x⁻¹ * (T⁻¹ * x * T) by group, map_mul, map_mul, map_mul,
      map_inv, map_inv, hTL]
    refine mul_mem (inv_mem hxR) ?_
    rw [show (pinnedX TwistTag.E6.tag L e6HighestRoot 1 * diagramMap TwistTag.E6 L)⁻¹ *
        baseChangeGL (algebraMap K L) x *
          (pinnedX TwistTag.E6.tag L e6HighestRoot 1 * diagramMap TwistTag.E6 L) =
        (diagramMap TwistTag.E6 L)⁻¹ * ((pinnedX TwistTag.E6.tag L e6HighestRoot 1)⁻¹ *
          baseChangeGL (algebraMap K L) x * pinnedX TwistTag.E6.tag L e6HighestRoot 1) *
            diagramMap TwistTag.E6 L by group]
    exact diagramMap_inv_conj_mem_twistedFixedGroup
      (mul_mem (mul_mem (inv_mem htR) hxR) htR)
  have hzH : baseChangeGL (algebraMap K L) ((T * x)⁻¹ * (x * T)) ∈ Subgroup.centralizer
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)) :
        Set (ModGL TwistTag.E6.tag L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hzC ⟨w, hw⟩]
  have hz1 : baseChangeGL (algebraMap K L) ((T * x)⁻¹ * (x * T)) = 1 := by
    have h := Subgroup.mem_inf.2 ⟨hzR, hzH⟩
    rwa [hRC, Subgroup.mem_bot] at h
  have hxT : x * T = T * x :=
    (inv_mul_eq_one.1 (baseChangeGL_injective (algebraMap K L) (hz1.trans (map_one _).symm))).symm
  have hζK : pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
      (diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ = x := by
    calc _ = T * x * T⁻¹ := by rw [hT]; group
      _ = x := by rw [← hxT, mul_inv_cancel_right]
  have hζ : pinnedX TwistTag.E6.tag L e6HighestRoot 1 *
      (diagramMap TwistTag.E6 L * baseChangeGL (algebraMap K L) x *
        (diagramMap TwistTag.E6 L)⁻¹) * (pinnedX TwistTag.E6.tag L e6HighestRoot 1)⁻¹ =
          baseChangeGL (algebraMap K L) x := by
    have h := congrArg (baseChangeGL (algebraMap K L)) hζK
    rwa [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, baseChangeGL_pinnedX_one,
      baseChangeGL_diagramMap] at h
  have hxL : baseChangeGL (algebraMap K L) x ∈ adjointGroup TwistTag.E6.tag L := hxR.1
  have hPxL := E6SecondGraphFixed.diagramMap_conj_eq_of_conj hL2 hxL hζ
  have hFrx : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) x) =
      baseChangeGL (algebraMap K L) x := by
    have h1 : twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L) x) =
        baseChangeGL (algebraMap K L) x := hxR.2
    rw [twistHom_apply] at h1
    exact mul_left_cancel (mul_right_cancel (h1.trans hPxL.symm))
  obtain ⟨⟨y, hy, hyx⟩, -⟩ := mem_map_of_conj_fixed hk2 Fr hFr hxL hFrx hζ
  have hxJ : x ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
      (baseChangeGL (algebraMap k K)) := by
    refine ⟨y, hy, baseChangeGL_injective (algebraMap K L) ?_⟩
    rw [baseChangeGL_baseChangeGL, ← IsScalarTower.algebraMap_eq, hyx]
  have hPx : diagramMap TwistTag.E6 K * x = x * diagramMap TwistTag.E6 K := by
    obtain ⟨y', hy', hy'x⟩ := hxJ
    rw [← hy'x]
    exact (mem_twistedFixedGroup_id_iff.1 (baseChangeGL_mem_twistedFixedGroup _ hy')).2
  have htx : x * pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 * x * diagramMap TwistTag.E6 K := by
    calc x * pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K = x * T := by
          rw [hT, mul_assoc]
      _ = T * x := hxT
      _ = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * (diagramMap TwistTag.E6 K * x) := by
          rw [hT, mul_assoc]
      _ = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * x * diagramMap TwistTag.E6 K := by
          rw [hPx, ← mul_assoc]
  exact ⟨x, hxJ, (mul_right_cancel htx).symm, δ, fun h => by rw [hβx, hcoeδ]⟩

theorem secondGraphFullCentralizer_graphFixedRootGroup_of_ringEquiv
    (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    SecondGraphFullCentralizer (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
      (diagramMap TwistTag.E6 K) (pinnedX TwistTag.E6.tag K e6HighestRoot 1)
      (embeddedFieldAut (algebraMap k K)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card hf hk
  have hfixι : ∀ c : k, σ.toRingHom (algebraMap k K c) = algebraMap k K c := fun c => by
    change σ (algebraMap k K c) = _
    rw [hσ, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hJC := map_baseChangeGL_le_graphFixedRootGroup hfixι
  have htΓ : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
      twistedFixedGroup TwistTag.E6 k (RingHom.id k) :=
    E6SecondGraphFixed.pinnedX_e6HighestRoot_mem_twistedFixedGroup hk2
  have htJ : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) :=
    ⟨_, htΓ, baseChangeGL_pinnedX_one _⟩
  obtain ⟨-, -, -, -, -, -, hcoeδ, -, -, hPσ, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  have hηJ : ∀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (g : ModGL TwistTag.E6.tag K) ∈
        (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) →
      fieldActor σ σ g = g := fun g hg => Subtype.ext (by
    obtain ⟨y, hy, hyg⟩ := hg
    rw [hPσ, ← hyg, (mem_twistedFixedGroup_id_iff.1 (baseChangeGL_mem_twistedFixedGroup _ hy)).2,
      mul_inv_cancel_right])
  have hactδ : ∀ (δ : K ≃+* K) (δk : k ≃+* k),
      (∀ c, algebraMap k K (δk c) = δ (algebraMap k K c)) →
      ∀ g : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)),
        ((embeddedFieldAut (algebraMap k K) δk g : _) : ModGL TwistTag.E6.tag K) =
          Units.map (entrywiseHom δ.toRingHom) (g : ModGL TwistTag.E6.tag K) := by
    intro δ δk hδk g
    obtain ⟨y, hy, hyg⟩ := g.2
    rw [coe_embeddedFieldAut (algebraMap k K) δk ⟨y, hy⟩ g hyg.symm, ← hyg]
    change baseChangeGL (algebraMap k K) (baseChangeGL δk.toRingHom y) =
      baseChangeGL δ.toRingHom (baseChangeGL (algebraMap k K) y)
    rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
    exact congrArg (fun ψ : k →+* K => baseChangeGL ψ y) (RingHom.ext hδk)
  have hdec' : ∀ β ∈ Subgroup.centralizer {MulAut.conj (⟨_, hJC htJ⟩ :
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom) * fieldActor σ σ},
      ∃ x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)),
        x * ⟨_, htJ⟩ = ⟨_, htJ⟩ * x ∧ ∃ δ : K ≃+* K,
          (∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, (β h : ModGL TwistTag.E6.tag K) =
            x * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) *
              (x : ModGL TwistTag.E6.tag K)⁻¹) ∧
          ∃ δk : k ≃+* k, (∀ c, algebraMap k K (δk c) = δ (algebraMap k K c)) ∧
            ∀ g, (β ⟨g, hJC g.2⟩ : ModGL TwistTag.E6.tag K) =
              ((MulAut.conj x * embeddedFieldAut (algebraMap k K) δk) g : _) := by
    intro β hβ
    have hβ' := Subgroup.mem_centralizer_singleton_iff.1 hβ
    obtain ⟨x, hxJ, htx, δ, hβx⟩ :=
      exists_conj_mul_of_mem_centralizer_graphFixedRootGroup hf hk hK σ hσ (hJC htJ) β hβ'.symm
    obtain ⟨δk, hδk⟩ := exists_restrict_ringEquiv hf hk hK δ
    refine ⟨⟨x, hxJ⟩, Subtype.ext htx.symm, δ, hβx, δk, hδk, fun g => ?_⟩
    rw [hβx, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hactδ δ δk hδk]
  refine secondGraphFullCentralizer_of htJ hJC (fieldActor σ σ) hPσ hηJ _ rfl
    (fun β hβ => ?_) (fun β hβ hfix => ?_) (fun φ => ?_)
    (fun x x' φ φ' h => eq_of_conj_mul_embeddedFieldAut_eq hf hk (algebraMap k K) h)
    (fun φ => embeddedFieldAut_pinnedX hk2 (algebraMap k K) φ htJ)
  · obtain ⟨x, hxt, -, -, δk, -, hx⟩ := hdec' β hβ
    exact ⟨x, hxt, δk, hx⟩
  ·
    obtain ⟨x, -, δ, hβx, δk, hδk, hx⟩ := hdec' β hβ
    have hid : MulAut.conj x * embeddedFieldAut (algebraMap k K) δk =
        MulAut.conj 1 * embeddedFieldAut (algebraMap k K) (RingEquiv.refl k) := by
      rw [map_one, embeddedFieldAut_refl, one_mul]
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [← hx g, hfix ⟨g, hJC g.2⟩ g.2]
      rfl
    obtain ⟨rfl, rfl⟩ := eq_of_conj_mul_embeddedFieldAut_eq hf hk (algebraMap k K) hid
    have hδfix : ∀ c : k, δ (algebraMap k K c) = algebraMap k K c := fun c => by
      rw [← hδk]
      rfl
    have hβδ : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (β h : ModGL TwistTag.E6.tag K) =
          Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) := fun h => by
      rw [hβx, Subgroup.coe_one, one_mul, inv_one, mul_one]
    rcases eq_one_or_eq_of_forall_algebraMap hf hk hK σ hσ δ hδfix with h1 | h1
    · have hβ1 : β = 1 := MulEquiv.ext fun h => Subtype.ext (by
        rw [hβδ, h1]
        exact Units.ext (entrywise_id _))
      rw [hβ1]
      exact one_mem _
    · have hβη : β = fieldActor σ σ := MulEquiv.ext fun h => Subtype.ext (by
        rw [hβδ, h1, hcoeδ])
      rw [hβη]
      exact Subgroup.mem_zpowers _
  ·
    obtain ⟨δ, hδ⟩ := exists_lift_ringEquiv hf hk hK φ
    have hδt := units_map_entrywiseHom_pinnedX_one (K := K) δ.toRingHom
    have hδP := units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (K := K) δ.toRingHom
    refine ⟨fieldActor σ δ, Subgroup.mem_centralizer_singleton_iff.2
      (MulEquiv.ext fun h => Subtype.ext ?_), fun g => ?_⟩
    · change (fieldActor σ δ (MulAut.conj (⟨_, hJC htJ⟩ :
          graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (fieldActor σ σ h)) :
            ModGL TwistTag.E6.tag K) =
        (MulAut.conj (⟨_, hJC htJ⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
          (fieldActor σ σ (fieldActor σ δ h)) : ModGL TwistTag.E6.tag K)
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hPσ, hcoeδ, map_mul,
        map_inv, hδt, hδP]
    · rw [hcoeδ, hactδ δ φ fun c => (hδ c).symm]

end Twisted

theorem secondGraphFullCentralizer_graphFixedRootGroup
    {f : ℕ} (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    SecondGraphFullCentralizer (graphFixedRootGroup TwistTag.E6 K σ)
      ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
      (diagramMap TwistTag.E6 K) (pinnedX TwistTag.E6.tag K e6HighestRoot 1)
      (embeddedFieldAut (algebraMap k K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩, rfl⟩
  exact secondGraphFullCentralizer_graphFixedRootGroup_of_ringEquiv hf hk hK σE hσ

end CFSG.LieType.Chevalley.E6SecondGraphFull
