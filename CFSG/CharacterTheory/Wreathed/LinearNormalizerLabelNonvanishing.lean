module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CompatibleFamily

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
theorem mem_sylow_of_centralizes {p : ℕ} [Fact p.Prime] (S : Sylow p G) {x : G}
    (hpx : IsPGroup p (Subgroup.zpowers x))
    (hx : x ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    x ∈ (S : Subgroup G) := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx).trans (Subgroup.centralizer_le_normalizer _)
  have hsup := S.is_maximal' (IsPGroup.to_sup_of_normal_left' S.isPGroup' hpx hle) le_sup_left
  rw [← hsup]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem card_class_eq_card_centralizer_inter {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k]
    [CharP k p] (S : Subgroup G) (hS : IsPGroup p S) (X : ConjClasses G) :
    (∑ g : G, if ConjClasses.mk g = X then (1 : k) else 0) =
      ∑ g : G, if g ∈ Subgroup.centralizer (S : Set G) ∧ ConjClasses.mk g = X then (1 : k)
        else 0 := by
  let : MulAction S G := MulAction.compHom G (MulAut.conj.comp S.subtype)
  have haction : ∀ (s : S) (g : G), s • g = (s : G) * g * (s : G)⁻¹ := fun _ _ => rfl
  have hfixed : ∀ g : G, g ∈ MulAction.fixedPoints S G ↔ g ∈ Subgroup.centralizer (S : Set G) := by
    intro g
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro hfix s hs
      have h := hfix ⟨s, hs⟩
      rw [haction] at h
      calc s * g = s * g * s⁻¹ * s := by group
        _ = g * s := by rw [h]
    · intro hcomm s
      rw [haction, hcomm s s.property]
      group
  have hsum := p_group_invariant_sum_fixedPoints p hS
    (fun g : G => if ConjClasses.mk g = X then (1 : k) else 0) (by
      intro s g
      change (if ConjClasses.mk ((s : G) * g * (s : G)⁻¹) = X then (1 : k) else 0) = _
      rw [conjugacyClass_mk_conjugation])
  rw [hsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : g ∈ Subgroup.centralizer (S : Set G)
  · simp only [(hfixed g).mpr hg, hg, true_and, ite_true]
  · have hg' : g ∉ MulAction.fixedPoints S G := fun h => hg ((hfixed g).mp h)
    simp only [hg', hg, false_and, ite_false]

theorem linear_normalizer_label_sylow_center_nonvanishing
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (S : Sylow p G)
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lam : Subgroup.normalizer ((S : Subgroup G) : Set G) →* ℂˣ)
    (hlamS : ∀ x : Subgroup.normalizer ((S : Subgroup G) : Set G), (x : G) ∈ (S : Subgroup G) →
      lam x = 1)
    (lambdaLabel : normalizerBasis.index)
    (hlabel : ∀ x, (normalizerBasis.representation lambdaLabel).character x = lam x)
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal p (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    coefficientBlockDefect basis ideal p B S ∧
    (∀ u ∈ (S : Subgroup G), u ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
      centralCharacterResidueHom basis ideal B
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk u)) =
        (Nat.card (ConjClasses.mk u).carrier : ComplexAlgebraicIntegers ⧸ ideal) ∧
      (Nat.card (ConjClasses.mk u).carrier : ComplexAlgebraicIntegers ⧸ ideal) ≠ 0) ∧
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ∀ u ∈ (S : Subgroup G), u ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
        (basis.representation χ).character u ≠ 0) := by
  have hSp : IsPGroup p (S : Subgroup G) := S.isPGroup'
  have hlocal := (CFSG.Wreathed.linear_character_block_has_sylow_defect normalizerBasis ideal p
    lam lambdaLabel hlabel (S.subtype Subgroup.le_normalizer)).1
  change coefficientBlockDefect normalizerBasis ideal p lambdaLabel
    ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))) at hlocal
  have hdefect : coefficientBlockDefect basis ideal p B S :=
    defect_normalizer_brauer_image_defect basis ideal p _ hSp normalizerBasis hlocal hB
  have hvalue : ∀ u ∈ (S : Subgroup G), u ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
      centralCharacterResidueHom basis ideal B
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk u)) =
        (Nat.card (ConjClasses.mk u).carrier : ComplexAlgebraicIntegers ⧸ ideal) := by
    intro u hu _
    set X := ConjClasses.mk u with hX
    have hpu : IsPGroup p (Subgroup.zpowers u) :=
      hSp.to_le (Subgroup.zpowers_le.mpr hu)
    have hinS : ∀ x : G, ConjClasses.mk x = X →
        x ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
        x ∈ (S : Subgroup G) := by
      intro x hxX hxC
      obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hxX.symm)
      have hpx : IsPGroup p (Subgroup.zpowers x) := by
        rw [← hg, show g * u * g⁻¹ = (MulAut.conj g).toMonoidHom u from rfl,
          ← MonoidHom.map_zpowers]
        exact hpu.map _
      exact mem_sylow_of_centralizes S hpx hxC
    rw [← hB]
    change centralCharacterResidueHom normalizerBasis ideal lambdaLabel
      (centralNormalizerCoefficientProjection _ (S : Subgroup G) _
        (Subgroup.centralizer_le_normalizer _) le_rfl (centralConjugacyClassSum _ X)) = _
    rw [centralCharacterResidueHom_linear normalizerBasis ideal lam lambdaLabel hlabel]
    unfold linearWeightedResidue
    have hterm : ∀ x : Subgroup.normalizer ((S : Subgroup G) : Set G),
        localizedComplexIntegerResidue ideal
            ⟨(centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal)
              (S : Subgroup G) _ (Subgroup.centralizer_le_normalizer _) le_rfl
                (centralConjugacyClassSum _ X)).val.coeff (id x),
              centralCoefficientSubring_coefficients _ _ _⟩ *
          localizedComplexIntegerResidue ideal ⟨lam x, linear_value_mem ideal lam x⟩ =
        if (x : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧ ConjClasses.mk (x : G) = X
          then 1 else 0 := by
      intro x
      dsimp only [id]
      set v := centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal)
        (S : Subgroup G) (Subgroup.normalizer ((S : Subgroup G) : Set G))
        (Subgroup.centralizer_le_normalizer _) le_rfl (centralConjugacyClassSum _ X) with hv
      have hcoeff : v.val.coeff x =
          if (x : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
            ConjClasses.mk (x : G) = X then 1 else 0 := by
        rw [hv, centralNormalizerCoefficientProjection_coeff]
        change (if (x : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) then
          (conjugacyClassSum (ring := ℂ) X).coeff (x : G) else 0) = _
        rw [conjugacyClassSum_coeff]
        by_cases hC : (x : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)
        · rw [ite_eq_left hC]
          by_cases hX' : ConjClasses.mk (x : G) = X
          · rw [ite_eq_left hX', ite_eq_left ⟨hC, hX'⟩]
          · rw [ite_eq_right hX', ite_eq_right fun h => hX' h.2]
        · rw [ite_eq_right hC, ite_eq_right fun h => hC h.1]
      have hres : localizedComplexIntegerResidue ideal
          ⟨v.val.coeff x, centralCoefficientSubring_coefficients _ v x⟩ =
            if (x : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
              ConjClasses.mk (x : G) = X then 1 else 0 := by
        split_ifs with hboth
        · have h1 : (⟨v.val.coeff x, centralCoefficientSubring_coefficients _ v x⟩ :
              localizedComplexIntegerRing ideal) = 1 := Subtype.ext (by
            change v.val.coeff x = ((1 : localizedComplexIntegerRing ideal) : ℂ)
            rw [hcoeff, ite_eq_left hboth, OneMemClass.coe_one])
          rw [h1, map_one]
        · have h0 : (⟨v.val.coeff x, centralCoefficientSubring_coefficients _ v x⟩ :
              localizedComplexIntegerRing ideal) = 0 := Subtype.ext (by
            change v.val.coeff x = ((0 : localizedComplexIntegerRing ideal) : ℂ)
            rw [hcoeff, ite_eq_right hboth, ZeroMemClass.coe_zero])
          rw [h0, map_zero]
      rw [hres]
      split_ifs with hboth
      · have hlam1 : lam x = 1 := hlamS x (hinS x hboth.2 hboth.1)
        have h2 : (⟨lam x, linear_value_mem ideal lam x⟩ : localizedComplexIntegerRing ideal) = 1 :=
          Subtype.ext (show ((lam x : ℂˣ) : ℂ) = ((1 : localizedComplexIntegerRing ideal) : ℂ) by
            rw [hlam1, Units.val_one, OneMemClass.coe_one])
        rw [h2, map_one, one_mul]
      · rw [zero_mul]
    rw [Finset.sum_congr rfl fun x _ => hterm x]
    have hreindex : (∑ x : Subgroup.normalizer ((S : Subgroup G) : Set G),
        if (x : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧ ConjClasses.mk (x : G) = X
          then (1 : ComplexAlgebraicIntegers ⧸ ideal) else 0) =
        ∑ g : G, if g ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧ ConjClasses.mk g = X
          then (1 : ComplexAlgebraicIntegers ⧸ ideal) else 0 :=
      Fintype.sum_of_injective (Subgroup.normalizer ((S : Subgroup G) : Set G)).subtype
        (Subgroup.subtype_injective _) _ _ (by
          intro g hg
          rw [ite_eq_right]
          rintro ⟨hgC, -⟩
          exact hg ⟨⟨g, Subgroup.centralizer_le_normalizer _ hgC⟩, rfl⟩) (fun _ => rfl)
    rw [hreindex]
    rw [← card_class_eq_card_centralizer_inter (S : Subgroup G) hSp X, Finset.sum_boole]
    congr 1
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext g
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hnonzero : ∀ u ∈ (S : Subgroup G), u ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
      (Nat.card (ConjClasses.mk u).carrier : ComplexAlgebraicIntegers ⧸ ideal) ≠ 0 := by
    intro u _ huC
    rw [ne_eq, CharP.cast_eq_zero_iff _ p, CFSG.LyonsUnitaryFour.card_conjClass_eq_index]
    have hle : (S : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp huC s hs)
    intro hdvd
    exact S.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hle))
  refine ⟨hdefect, fun u hu huC => ⟨hvalue u hu huC, hnonzero u hu huC⟩, ?_⟩
  intro χ hχ u hu huC hzero
  apply hnonzero u hu huC
  rw [← hvalue u hu huC]
  have hsame := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal B χ).mp
    ((coefficientBlock_mem_iff _ _ _ _).mp hχ)
  rw [hsame]
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ _) = 0
  have hlocal : localCentralCharacterHom basis ideal χ
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk u)) = 0 := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe]
    change centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk u)) χ = 0
    rw [centralCharacterScalar_conjugacyClassSum_mk, hzero, mul_zero, zero_div]
  rw [hlocal, map_zero]

end CFSG.Wreathed
