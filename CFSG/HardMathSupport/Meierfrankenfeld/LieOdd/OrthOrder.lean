module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthModel

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped Pointwise

theorem card_outer_le_of_reindex {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound p Q₀) {Qc : QuadraticForm K (Fin d → K)}
    (hQc : Qc = reindexQuadraticForm e Q₀) (hQ : Qc ≠ 0) :
    Nat.card (Outer (matrixProjectiveDerived Qc)) ≤ 8 * f * (matrixProjectiveImage Qc).index := by
  subst hQc
  have ha := relIndex_inner_dvd (reindexQuadraticForm e Q₀)
  have hb := relIndex_isometryRange_dvd (reindexQuadraticForm e Q₀) (exists_nonzero_value _ hQ)
  have hc := (relIndex_linearRange_dvd (reindexQuadraticForm e Q₀)).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection (reindexQuadraticForm e Q₀)).range).trans
      (card_ringAut_and_isCyclic hp K hK).1.dvd)
  rw [card_abelianization_matrixIsometries_reindex] at ha
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
  rw [hsq] at hb
  have hA := hab.2.1 hp2
  have hApos : 0 < Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)) := by
    have : Finite (TauCeti.QuadraticMap.orthogonalGroup Q₀) := inferInstance
    exact Nat.card_pos
  have h1 := (Nat.le_of_dvd hApos ha).trans hA
  have h2 := (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) hb).trans
    (Nat.gcd_le_right _ (by norm_num))
  have h3 := Nat.le_of_dvd (by omega) hc
  rw [card_outer_eq]
  calc _ ≤ 4 * 2 * f * (matrixProjectiveImage (reindexQuadraticForm e Q₀)).index :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3)
    _ = 8 * f * (matrixProjectiveImage (reindexQuadraticForm e Q₀)).index := by ring

theorem card_outer_le_of_orthogonal (T : Type) [Group T] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ) (hp2 : p ≠ 2)
    (h : StatedClassicalModel T t n p f) : Nat.card (Outer T) ≤ 24 * f := by
  rcases ht with rfl | rfl | rfl
  ·
    have h0 := h
    obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h0
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl) n p f
      h K hK (quadOdd n K) (coe_quadOdd n K) e
    have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
      rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n p f
        h) K hK e).1]
      exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
        (.inl rfl) n p f h) K hK).2
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadOdd n K))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinateOddWitnessEquiv K e)).toEquiv
    have hb := card_outer_le_of_reindex hp hp2 hf hK (oddIndexEquiv n) (quadOdd n K) hab
      (Qc := coordinateQuadOdd n K) rfl (coordinate_model_intrinsic_odd h K hK e).1
    rw [hE, Subgroup.index_top, ← hout] at hb
    omega
  ·
    have h0 := h
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h0
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
      (.inr (.inl rfl)) n p f h K hK (quadPlus n K) (coe_quadPlus n K) e
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
      (.inr (.inl rfl)) n p f h) K hK e).1
    have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinatePlusWitnessEquiv K e)).toEquiv
    have hb := card_outer_le_of_reindex hp hp2 hf hK (plusIndexEquiv n) (quadPlus n K) hab
      (Qc := coordinateQuadPlus n K) rfl (coordinate_model_intrinsic_plus h K hK e).1
    rw [← hout] at hb
    have hidx : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
      rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
      · have hst : (projectivePointFamilyAut (coordinateQuadPlus n K)).index =
            (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
              (projectivePointFamily (coordinateQuadPlus n K))).ncard :=
          MulAction.index_stabilizer _ _
        rw [← hEA, hst]
        exact (horbit.2.2.2.2.2 h4).2
      · rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
        norm_num
    calc Nat.card (Outer T) ≤ 8 * f * (matrixProjectiveImage (coordinateQuadPlus n K)).index := hb
      _ ≤ 8 * f * 3 := Nat.mul_le_mul_left _ hidx
      _ = 24 * f := by ring
  ·
    have h0 := h
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
    have hn1 : 1 ≤ n := by omega
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
      (.inr (.inr rfl)) n p f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
    have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
      rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
        (.inr (.inr rfl)) n p f h) hn1 K hK b c hirr e).1]
      exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
        .POmegaMinus (.inr rfl) n p f h) hn1 K hK b c hirr).2
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinateMinusWitnessEquiv K hn1 b c e)).toEquiv
    have hb := card_outer_le_of_reindex hp hp2 hf hK (minusIndexEquiv n hn1) (quadMinus n K b c)
      hab (Qc := coordinateQuadMinus n K hn1 b c) rfl
      (coordinate_model_intrinsic_minus h K hK b c hirr e).1
    rw [hE, Subgroup.index_top, ← hout] at hb
    omega

theorem card_le_card_outer_mul_card_inf {S : Type} [Group S] [Finite S]
    (B : Subgroup (MulAut S)) :
    Nat.card B ≤ Nat.card (Outer S) * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range) := by
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  have : Finite (Outer S) := Quotient.finite _
  have : (MulAut.conj : S →* MulAut S).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  have h1 := Subgroup.relIndex_mul_card (H := (MulAut.conj : S →* MulAut S).range) (K := B)
  have h3 := Subgroup.relIndex_dvd_index_of_normal (MulAut.conj : S →* MulAut S).range B
  have h4 : (MulAut.conj : S →* MulAut S).range.index = Nat.card (Outer S) := rfl
  rw [← h1, inf_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos (h4 ▸ h3))

theorem card_statedProj_statedOmega_le {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nat.card (StatedProj (StatedOmega Q₀)) ≤
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h1 : Nat.card (StatedProj (StatedOmega Q₀)) ≤ Nat.card (StatedOmega Q₀) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card (StatedOmega Q₀) =
      Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [statedOmega_eq_comap hQ]
    exact Nat.card_congr ((toLinEquiv ι K).toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have h3 := Subgroup.card_le_of_le (H := ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (K := TauCeti.QuadraticMap.orthogonalGroup Q)
    (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂))
  omega

theorem prod_pow_two_mul_sub_one_le {q : ℤ} (hq : 1 ≤ q) (m : ℕ) :
    0 ≤ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ∧
      ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ q ^ (m * (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have hpow : 1 ≤ q ^ (2 * (m + 1)) := one_le_pow₀ hq
    refine ⟨mul_nonneg ih.1 (by linarith), ?_⟩
    calc (∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)) * (q ^ (2 * (m + 1)) - 1)
        ≤ q ^ (m * (m + 1)) * q ^ (2 * (m + 1)) :=
          mul_le_mul ih.2 (by linarith) (by linarith) (pow_nonneg (by linarith) _)
      _ = q ^ ((m + 1) * (m + 1 + 1)) := by
          rw [← pow_add]
          congr 1
          ring

theorem card_orthogonalGroup_quadOdd_le {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (r : ℕ) : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd r K)) ≤
      2 * Nat.card K ^ (r * (2 * r + 1)) := by
  have hq : (1 : ℤ) ≤ Nat.card K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hO := CFSG.ClassicalInvolution.card_orthogonalGroup_quadOdd_of_two_ne_zero h2 r
  obtain ⟨-, hP⟩ := prod_pow_two_mul_sub_one_le hq r
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd r K)) : ℤ) ≤
      2 * (Nat.card K : ℤ) ^ (r * (2 * r + 1)) := by
    rw [hO]
    calc 2 * (Nat.card K : ℤ) ^ (r ^ 2) * ∏ i ∈ Finset.Icc 1 r, ((Nat.card K : ℤ) ^ (2 * i) - 1)
        ≤ 2 * (Nat.card K : ℤ) ^ (r ^ 2) * (Nat.card K : ℤ) ^ (r * (r + 1)) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 2 * (Nat.card K : ℤ) ^ (r * (2 * r + 1)) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          ring
  exact_mod_cast h

theorem card_orthogonalGroup_quadPlus_le {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (m : ℕ) : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) ≤
      2 * Nat.card K ^ ((m + 1) * (2 * m + 1)) := by
  have hq : (1 : ℤ) ≤ Nat.card K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hO := CFSG.ClassicalInvolution.card_orthogonalGroup_quadPlus_of_two_ne_zero h2 m
  obtain ⟨hP0, hP⟩ := prod_pow_two_mul_sub_one_le hq m
  have hpow : 1 ≤ (Nat.card K : ℤ) ^ (m + 1) := one_le_pow₀ hq
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) : ℤ) ≤
      2 * (Nat.card K : ℤ) ^ ((m + 1) * (2 * m + 1)) := by
    rw [hO]
    calc 2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1)
        ≤ 2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * (Nat.card K : ℤ) ^ (m + 1) *
            (Nat.card K : ℤ) ^ (m * (m + 1)) := by
          apply mul_le_mul _ hP hP0 (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * (Nat.card K : ℤ) ^ ((m + 1) * (2 * m + 1)) := by
          rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
          congr 2
          ring
  exact_mod_cast h

theorem card_orthogonalGroup_quadMinus_le {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) ≤
      4 * Nat.card K ^ ((m + 1) * (2 * m + 1)) := by
  have hq : (1 : ℤ) ≤ Nat.card K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hO := CFSG.ClassicalInvolution.card_orthogonalGroup_quadMinus_of_two_ne_zero h2 hirr m
  obtain ⟨hP0, hP⟩ := prod_pow_two_mul_sub_one_le hq m
  have hpow : 1 ≤ (Nat.card K : ℤ) ^ (m + 1) := one_le_pow₀ hq
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) : ℤ) ≤
      4 * (Nat.card K : ℤ) ^ ((m + 1) * (2 * m + 1)) := by
    rw [hO]
    calc 2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1)
        ≤ 2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * (2 * (Nat.card K : ℤ) ^ (m + 1)) *
            (Nat.card K : ℤ) ^ (m * (m + 1)) := by
          apply mul_le_mul _ hP hP0 (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * (Nat.card K : ℤ) ^ ((m + 1) * (2 * m + 1)) := by
          rw [show 2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * (2 * (Nat.card K : ℤ) ^ (m + 1)) *
              (Nat.card K : ℤ) ^ (m * (m + 1)) = 4 * ((Nat.card K : ℤ) ^ (m * (m + 1)) *
              (Nat.card K : ℤ) ^ (m + 1) * (Nat.card K : ℤ) ^ (m * (m + 1))) by ring,
            ← pow_add, ← pow_add]
          congr 2
          ring
  exact_mod_cast h

theorem card_sup_le_of_card_outer {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hcenter : Subgroup.center ↥L = ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : CFSG.Quasithin.IsElemAbelian2 E)
    {S : Type} [Group S] (θ : ↥L ≃* S) {k : ℕ} (hk : Nat.card (Outer S) ≤ k) :
    Nat.card ↥(L ⊔ E) ≤ k * Nat.card S := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite S := Finite.of_equiv _ θ.toEquiv
  let e : ↥L ⧸ Subgroup.center ↥L ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans θ)
  have h := FFToolkit.card_sup_le_of_outer hW hperf hirr hE hEel e (k := k) (fun B _ _ =>
    (card_le_card_outer_mul_card_inf B).trans (Nat.mul_le_mul_right _ hk))
  rwa [Nat.card_congr θ.toEquiv] at h

theorem card_sup_le_of_pomegaOdd {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hcenter : Subgroup.center ↥L = ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : CFSG.Quasithin.IsElemAbelian2 E)
    {K : Type} [Field K] [Finite K] {p e r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hr : 3 ≤ r) (hn : n = 2 * r + 1)
    (θ : ↥L ≃* StatedProj (StatedOmega (StatedQuadOdd r K))) :
    Nat.card ↥(L ⊔ E) ≤ 96 * p ^ (e * (n * (n - 1) / 2)) * e := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd r K))) .POmegaOdd r p e :=
    ⟨⟨hp, he, hr, hp2⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hout := card_outer_le_of_orthogonal _ .POmegaOdd (.inl rfl) r p e hp2 hM
  have hsup := card_sup_le_of_card_outer hW hperf hirr hcenter hE hEel θ hout
  have hS := (card_statedProj_statedOmega_le (coe_quadOdd r K)).trans
    (card_orthogonalGroup_quadOdd_le h2 r)
  have hexp : n * (n - 1) / 2 = r * (2 * r + 1) := by
    subst hn
    rw [show 2 * r + 1 - 1 = 2 * r by omega, show (2 * r + 1) * (2 * r) = 2 * (r * (2 * r + 1))
      by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hexp, pow_mul, ← hK]
  calc Nat.card ↥(L ⊔ E) ≤ 24 * e * Nat.card (StatedProj (StatedOmega (StatedQuadOdd r K))) := hsup
    _ ≤ 24 * e * (2 * Nat.card K ^ (r * (2 * r + 1))) := Nat.mul_le_mul_left _ hS
    _ ≤ 96 * Nat.card K ^ (r * (2 * r + 1)) * e := by nlinarith [Nat.zero_le (Nat.card K ^ (r * (2 * r + 1)))]

theorem card_sup_le_of_pomegaPlus {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hcenter : Subgroup.center ↥L = ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : CFSG.Quasithin.IsElemAbelian2 E)
    {K : Type} [Field K] [Finite K] {p e r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hr : 4 ≤ r) (hn : n = 2 * r)
    (θ : ↥L ≃* StatedProj (StatedOmega (StatedQuadPlus r K))) :
    Nat.card ↥(L ⊔ E) ≤ 96 * p ^ (e * (n * (n - 1) / 2)) * e := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus r K))) .POmegaPlus r p e :=
    ⟨⟨hp, he, hr⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hout := card_outer_le_of_orthogonal _ .POmegaPlus (.inr (.inl rfl)) r p e hp2 hM
  have hsup := card_sup_le_of_card_outer hW hperf hirr hcenter hE hEel θ hout
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hS := (card_statedProj_statedOmega_le (coe_quadPlus (m + 1) K)).trans
    (card_orthogonalGroup_quadPlus_le h2 m)
  have hexp : n * (n - 1) / 2 = (m + 1) * (2 * m + 1) := by
    subst hn
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hexp, pow_mul, ← hK]
  calc Nat.card ↥(L ⊔ E) ≤ 24 * e * Nat.card (StatedProj (StatedOmega (StatedQuadPlus (m + 1) K))) :=
        hsup
    _ ≤ 24 * e * (2 * Nat.card K ^ ((m + 1) * (2 * m + 1))) := Nat.mul_le_mul_left _ hS
    _ ≤ 96 * Nat.card K ^ ((m + 1) * (2 * m + 1)) * e := by
        nlinarith [Nat.zero_le (Nat.card K ^ ((m + 1) * (2 * m + 1)))]

theorem card_sup_le_of_pomegaMinus {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hcenter : Subgroup.center ↥L = ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : CFSG.Quasithin.IsElemAbelian2 E)
    {K : Type} [Field K] [Finite K] {p e r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hr : 4 ≤ r) (hn : n = 2 * r) {b c : K}
    (hirr' : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus r K b c))) :
    Nat.card ↥(L ⊔ E) ≤ 96 * p ^ (e * (n * (n - 1) / 2)) * e := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus r K b c)))
      .POmegaMinus r p e :=
    ⟨⟨hp, he, hr⟩, K, inferInstance, inferInstance, hK, b, c, hirr', ⟨MulEquiv.refl _⟩⟩
  have hout := card_outer_le_of_orthogonal _ .POmegaMinus (.inr (.inr rfl)) r p e hp2 hM
  have hsup := card_sup_le_of_card_outer hW hperf hirr hcenter hE hEel θ hout
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hS := (card_statedProj_statedOmega_le (coe_quadMinus (m + 1) K b c)).trans
    (card_orthogonalGroup_quadMinus_le h2 hirr' m)
  have hexp : n * (n - 1) / 2 = (m + 1) * (2 * m + 1) := by
    subst hn
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hexp, pow_mul, ← hK]
  calc Nat.card ↥(L ⊔ E) ≤
        24 * e * Nat.card (StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c))) := hsup
    _ ≤ 24 * e * (4 * Nat.card K ^ ((m + 1) * (2 * m + 1))) := Nat.mul_le_mul_left _ hS
    _ = 96 * Nat.card K ^ ((m + 1) * (2 * m + 1)) * e := by ring

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
