module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesExclusions
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.EvenBN.TwoF4.L3 (false_of_not_mem_semilinear conj_mem_semilinearAutGroup)

section FieldInvolution

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_card_SL_three {k : Type} [Field k] [Fintype k] [DecidableEq k]
    (h2 : 2 ≤ Fintype.card k) (h4 : Fintype.card k ≤ 4) :
    ¬ 17 ∣ Nat.card (SpecialLinearGroup (Fin 3) k) := by
  rw [Matrix.card_SL_field, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  interval_cases (Fintype.card k) <;> decide

theorem false_of_fieldAut_fixes_seventeen (hK : Nat.card K = 16) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 4) {x : projectiveSL 3 K} (hx : orderOf x = 17)
    (hfix : fieldAut 3 K σ x = x) : False := by
  classical
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 4)
    (by norm_num) (by rw [hK]; norm_num)
  let := Fintype.ofFinite K
  obtain ⟨g', rfl⟩ := proj_surjective 3 K x
  have h17 : proj 3 K (g' ^ 17) = 1 := by rw [map_pow, ← hx, pow_orderOf_eq_one]
  obtain ⟨c, hc3, hcg⟩ := mem_scalars.1 (proj_eq_one_iff.1 h17)
  set s := scalarElement c hc3 with hs
  have hsC : s ∈ center (SpecialLinearGroup (Fin 3) K) :=
    scalars_le_center 3 K (scalarElement_mem_scalars c hc3)
  set g := g' * s with hg
  have hpg : proj 3 K g = proj 3 K g' := by
    rw [hg, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hc3), mul_one]
  have hg17 : g ^ 17 = 1 := by
    have hcomm : Commute g' s := (mem_center_iff.1 hsC) g'
    rw [hg, hcomm.mul_pow]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hcg, Matrix.SpecialLinearGroup.coe_pow, hs,
      coe_scalarElement, ← map_pow, ← map_mul, Matrix.SpecialLinearGroup.coe_one]
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ',
      show c ^ 18 = (c ^ 3) ^ 6 by rw [← pow_mul], hc3, one_pow, Units.val_one]
    simp
  have hσg : Matrix.SpecialLinearGroup.map σ.toRingHom g = g := by
    have h1 : proj 3 K (Matrix.SpecialLinearGroup.map σ.toRingHom g) = proj 3 K g := by
      rw [← fieldAut_proj, hpg, hfix]
    obtain ⟨μ, hμ3, hμ⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h1.symm)
    set z := g⁻¹ * Matrix.SpecialLinearGroup.map σ.toRingHom g with hz
    have hzC : z ∈ center (SpecialLinearGroup (Fin 3) K) :=
      scalars_le_center 3 K ⟨μ, hμ3, hμ⟩
    have hgz : Matrix.SpecialLinearGroup.map σ.toRingHom g = g * z := by
      rw [hz, mul_inv_cancel_left]
    have hz17 : z ^ 17 = 1 := by
      have e := congrArg (fun w => w ^ 17) hgz
      rw [← map_pow, hg17, map_one, (show Commute g z from (mem_center_iff.1 hzC) g).mul_pow, hg17,
        one_mul] at e
      exact e.symm
    have hz1 : z = 1 := by
      have hz3 : z ^ 3 = 1 := by
        ext i j
        rw [Matrix.SpecialLinearGroup.coe_pow, hμ, ← map_pow, ← Units.val_pow_eq_pow_val, hμ3,
          Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
      have hz2 : z ^ 2 = 1 := by
        have e : z ^ 17 = (z ^ 3) ^ 5 * z ^ 2 := by group
        rw [hz3, one_pow, one_mul, hz17] at e
        exact e.symm
      have e : z = z ^ 3 * (z ^ 2)⁻¹ := by group
      rw [e, hz3, hz2, inv_one, mul_one]
    rw [hgz, hz1, mul_one]
  set K₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id K) with hK₀
  have hmem : ∀ i j, (g : Matrix (Fin 3) (Fin 3) K) i j ∈ K₀ := fun i j => by
    rw [RingHom.mem_eqLocusField]
    have e := congrArg (fun w : SpecialLinearGroup (Fin 3) K =>
      (w : Matrix (Fin 3) (Fin 3) K) i j) hσg
    simpa using e
  set g₀ : Matrix (Fin 3) (Fin 3) K₀ := Matrix.of fun i j => ⟨_, hmem i j⟩ with hg₀
  have hg₀map : g₀.map K₀.subtype = (g : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rfl
  have hdet : g₀.det = 1 := by
    apply K₀.subtype_injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hg₀map,
      Matrix.SpecialLinearGroup.det_coe]
  set g₁ : SpecialLinearGroup (Fin 3) K₀ := ⟨g₀, hdet⟩ with hg₁
  have hg₁map : Matrix.SpecialLinearGroup.map K₀.subtype g₁ = g := by
    ext i j
    rfl
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) K₀.subtype) := by
    intro a b e
    ext i j
    have := congrArg (fun w : SpecialLinearGroup (Fin 3) K =>
      (w : Matrix (Fin 3) (Fin 3) K) i j) e
    exact this
  have hgord : orderOf g = 17 := by
    refine orderOf_eq_prime hg17 fun e => ?_
    rw [hpg.symm.trans (by rw [e, map_one] : proj 3 K g = 1), orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hg₁ord : orderOf g₁ = 17 := by
    rw [← orderOf_injective _ hinj g₁, hg₁map, hgord]
  have hdvd : 17 ∣ Nat.card (SpecialLinearGroup (Fin 3) K₀) := by
    rw [← hg₁ord]
    exact orderOf_dvd_natCard g₁
  have h2 : 2 ≤ Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have h4 : Fintype.card K₀ ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have hp := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (Polynomial.X ^ 4 - Polynomial.X : Polynomial K)
      (Finset.univ.map ⟨((↑) : K₀ → K), Subtype.val_injective⟩) (by
        intro i hi
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hi
        have ha := (RingHom.mem_eqLocusField).1 a.2
        simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingHom.id_apply] at ha
        simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← hσ, ha])
      (by
        rw [Finset.card_map, Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq K
          (by norm_num : 1 < 4)]
        omega)
    exact FiniteField.X_pow_card_sub_X_ne_zero K (by norm_num : 1 < 4) hp
  exact not_dvd_card_SL_three h2 h4 hdvd

end FieldInvolution

open CFSG.Blueprint CFSG.ComponentClassification in
theorem false_of_lieModel_PSL3_four {H : Type} [Group H] [Finite H] {D : Subgroup H} [D.Normal]
    {a : H} (haa : a * a = 1) (hn : LieModel D .PSL 3 2 4)
    (hnt : ∃ d ∈ D, a⁻¹ * d * a ≠ d) {J : Subgroup H} (hJD : J ≤ D)
    (hJa : J ≤ centralizer ({a} : Set H)) [IsSimpleGroup J] (hJna : ∃ x y : J, x * y ≠ y * x)
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal) (hJ17 : 17 ∣ Nat.card J)
    {E : Subgroup H} (hED : E ≤ D) (hE : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 2 ^ 8)
    (haE : a ∈ normalizer (E : Set H)) : False := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hn
  have hn1 : 1 ≤ 4 := by norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set α : MulAut D := MulAut.conjNormal a with hα
  set y : MulAut (projectiveSL 3 K) := (e.symm.trans α).trans e with hy
  have hyapp : ∀ d : D, y (e d) = e (α d) := fun d => by simp [hy]
  have hαapp : ∀ d : D, ((α d : D) : H) = a * d * a⁻¹ := fun d => rfl
  have hfix : ∀ d : D, y (e d) = e d ↔ a * (d : H) = d * a := by
    intro d
    rw [hyapp, e.apply_eq_iff_eq, Subtype.ext_iff, hαapp, mul_inv_eq_iff_eq_mul]
  have hy2 : y ^ 2 = 1 := by
    refine MulEquiv.ext fun p => ?_
    obtain ⟨d, rfl⟩ := e.surjective p
    rw [sq, MulAut.mul_apply, hyapp, hyapp, MulAut.one_apply, e.apply_eq_iff_eq,
      Subtype.ext_iff, hαapp, hαapp, hainv]
    calc a * (a * (d : H) * a) * a = (a * a) * d * (a * a) := by group
      _ = d := by rw [haa, one_mul, mul_one]
  by_cases hin : y ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  ·
    obtain ⟨g, hg⟩ := hin
    have hinj := CFSG.ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
    have hg2 : g ^ 2 = 1 := hinj (by rw [map_pow, hg, hy2, map_one])
    have hg1 : g ≠ 1 := by
      rintro rfl
      obtain ⟨d, hd, hda⟩ := hnt
      apply hda
      have h1 := (hfix ⟨d, hd⟩).1 (by rw [← hg, map_one, MulAut.one_apply])
      rw [hainv]
      calc a * d * a = d * a * a := by rw [h1]
        _ = d := by rw [mul_assoc, haa, mul_one]
    have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
    have hyc : ∀ p, y p = g * p * g⁻¹ := fun p => by rw [← hg, MulAut.conj_apply]
    set C := centralizer ({g} : Set (projectiveSL 3 K)) with hC
    have hmemC : ∀ d : D, e d ∈ C ↔ a * (d : H) = d * a := by
      intro d
      rw [← hfix, hyc, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]
    set J' : Subgroup (projectiveSL 3 K) := (J.subgroupOf D).map e.toMonoidHom with hJ'
    have hJ'C : J' ≤ C := by
      rintro _ ⟨d, hd, rfl⟩
      exact (hmemC d).2 (mem_centralizer_singleton_iff.1 (hJa (mem_subgroupOf.1 hd))).symm
    set B : Subgroup C := J'.subgroupOf C with hB
    have hJq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hJna).1
    have eB : J ≃* B := ((subgroupOfEquivOfLe hJD).symm.trans
      (equivMapOfInjective _ e.toMonoidHom e.injective)).trans (subgroupOfEquivOfLe hJ'C).symm
    have hBq : CFSG.IsQuasisimple B :=
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eB).1 hJq
    have hBn : B.Normal := by
      refine ⟨fun b hb c => ?_⟩
      obtain ⟨j, hj, hjb⟩ := mem_subgroupOf.1 hb
      obtain ⟨d, hd⟩ := e.surjective (c : projectiveSL 3 K)
      have hdC : (d : H) ∈ centralizer ({a} : Set H) := by
        rw [mem_centralizer_singleton_iff]
        exact ((hmemC d).1 (hd ▸ c.2)).symm
      have hjJ : (j : H) ∈ J := mem_subgroupOf.1 hj
      have hconj : (d : H) * j * (d : H)⁻¹ ∈ J := by
        have h1 := hJn.conj_mem ⟨j, hJa hjJ⟩ (mem_subgroupOf.2 hjJ) ⟨d, hdC⟩
        rw [mem_subgroupOf] at h1
        simpa using h1
      rw [mem_subgroupOf]
      refine ⟨d * j * d⁻¹, mem_subgroupOf.2 (by simpa using hconj), ?_⟩
      rw [coe_mul, coe_mul, coe_inv, ← hjb, ← hd]
      simp
    exact OutcomeLocal.even_linear_involution_centralizers_component_free hn1 (by norm_num) hK g
      hord B ⟨hBq, hBn.isSubnormal⟩
  ·
    set E' : Subgroup (projectiveSL 3 K) := (E.subgroupOf D).map e.toMonoidHom with hE'
    have hE'2 : ∀ x ∈ E', x ^ 2 = 1 := by
      rintro _ ⟨d, hd, rfl⟩
      have hd2 : d ^ 2 = 1 := Subtype.ext (by
        rw [sq, coe_mul]
        exact hE _ (mem_subgroupOf.1 hd))
      rw [← map_pow, hd2, map_one]
    have hE'card : Nat.card E' = Nat.card K ^ 2 := by
      rw [hE', card_map_of_injective e.injective,
        Nat.card_congr (subgroupOfEquivOfLe hED).toEquiv, hcard, hK]
      norm_num
    have hyE' : ∀ x ∈ E', y x ∈ E' := by
      rintro _ ⟨d, hd, rfl⟩
      refine ⟨α d, mem_subgroupOf.2 ?_, (hyapp d).symm⟩
      rw [hαapp]
      exact (mem_normalizer_iff.1 haE _).1 (mem_subgroupOf.1 hd)
    rcases LinearThree.exists_conj_canonical_of_not_mem_range hn1 hK hy2 hin with
      ⟨-, σ, hσx, γ, hγ⟩ | ⟨γ, hγ⟩ | ⟨-, σ, hσx, γ, hγ⟩
    ·
      have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
      obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 17 hJ17
      set x : projectiveSL 3 K := e ⟨(j : H), hJD j.2⟩ with hx
      have hyx : y x = x := (hfix _).2
        (mem_centralizer_singleton_iff.1 (hJa j.2)).symm
      have hxord : orderOf x = 17 := by
        rw [hx, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hj]
      have hσ4 : ∀ c, σ c = c ^ 4 := fun c => by
        rw [hσx]
        norm_num
      apply false_of_fieldAut_fixes_seventeen (x := γ⁻¹ x) hK hσ4
      · rw [MulEquiv.orderOf_eq, hxord]
      · have e1 : γ (fieldAut 3 K σ (γ⁻¹ x)) = x := by
          rw [hγ] at hyx
          exact hyx
        calc fieldAut 3 K σ (γ⁻¹ x) = γ⁻¹ (γ (fieldAut 3 K σ (γ⁻¹ x))) := by simp
          _ = γ⁻¹ x := by rw [e1]
    ·
      refine false_of_not_mem_semilinear hE'2 hE'card (fun h => ?_) hyE'
      apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
      have h' := conj_mem_semilinearAutGroup γ⁻¹ (hγ ▸ h)
      rwa [show γ⁻¹ * (γ * dualAut 3 K * γ⁻¹) * γ⁻¹⁻¹ = dualAut 3 K by group] at h'
    ·
      refine false_of_not_mem_semilinear hE'2 hE'card (fun h => ?_) hyE'
      apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
      have h' := conj_mem_semilinearAutGroup γ⁻¹ (hγ ▸ h)
      rw [show γ⁻¹ * (γ * (fieldAut 3 K σ * dualAut 3 K) * γ⁻¹) * γ⁻¹⁻¹ =
        fieldAut 3 K σ * dualAut 3 K by group] at h'
      have h'' := mul_mem (inv_mem (fieldAut_mem_semilinearAutGroup σ)) h'
      rwa [inv_mul_cancel_left] at h''

end CFSG.LocalAnalysis.EvenBN.U5
