module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldD4
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YH

open TensorProduct Matrix Module CFSG.GroupTheory.SteinbergBK CFSG.Blueprint.EvenSource
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY
  CFSG.RankThree.PartOne.KCOrthogonalDescent

variable {K : Type} [Field K] {d : ℕ}

theorem descent_core_aux3 {ℓ f p : ℕ} [Finite K] (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = ℓ ^ f) (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hS3 : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hgates : OrthogonalGates Q f) (a : MulAut (matrixProjectiveDerived Q))
    (haD : a ∉ (linearConjugationHom Q).range) (hap : orderOf a = p) (g : similarityPairs Q)
    (hg : matrixProjectiveConjugationHom Q g = a) :
    p ∣ f ∧ orderOf g.val.right = p ∧
      Nat.card (semilinearFixedSubfield g.val.right) = ℓ ^ (f / p) ∧
      ∃ (U : similarityPairs Q) (c : Kˣ)
        (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)),
        matrixProjectiveConjugationHom Q U = a ∧ U.val.right = g.val.right ∧
        FixedFormDescent p Q U c Q₀ ∧ Nonempty (DescentSplitting Q U c Q₀) := by
  classical
  obtain ⟨hker, ⟨ψ, hψg, hψker, -⟩, -⟩ := hgates
  have ha : a ∈ matrixProjectiveImage Q := ⟨g, hg⟩
  have hψa : ψ ⟨a, ha⟩ = g.val.right := by
    rw [← hψg g]
    congr 1
    exact Subtype.ext hg.symm
  have happ : a ^ p = 1 := by
    rw [← hap]
    exact pow_orderOf_eq_one a
  have hσp : g.val.right ^ p = 1 := by
    rw [← hψa, ← map_pow]
    have h1 : (⟨a, ha⟩ : matrixProjectiveImage Q) ^ p = 1 := Subtype.ext happ
    rw [h1, map_one]
  have hσne : g.val.right ≠ 1 := by
    intro h1
    apply haD
    have h2 : (⟨a, ha⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hψa, h1]
    rw [hψker] at h2
    exact h2
  have hσord : orderOf g.val.right = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσne
    · exact h
  have hκ : matrixProjectiveConjugationHom Q (g ^ p) = 1 := by rw [map_pow, hg, happ]
  obtain ⟨-, b, hb⟩ := (hker (g ^ p)).mp hκ
  have hb' : (g.val ^ p).left = sc b := hb
  obtain ⟨U, hUr, hUp, hUκ⟩ := exists_normalized_pair Q hd g hσord hb'
  have hσ : orderOf U.val.right = p := by rw [hUr]; exact hσord
  have hap' : ∀ v, (⇑(coordinateSemilinearMap U.val))^[p] v = v := fun v => by
    rw [iterate_coordinateSemilinearMap, hUp, coordinateSemilinearMap_one]
  have hQa : ∀ v, Q (coordinateSemilinearMap U.val v) =
      (multiplier Q U : K) * U.val.right (Q v) := fun v => multiplier_spec Q U v
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨hdvd, hcard, c, Q₀, hQ₀, hnd₀, hfr, Φ, hΦ1, hΦ2⟩ :=
    exists_descent hℓ hf hK U.val.right hσ (coordinateSemilinearMap U.val)
      (coordinateSemilinearMap_smul U.val) hap' Q hnd (multiplier Q U : K) hQa
  have hfr' : finrank (fixedField U.val) (fixedSpace U.val) = d := hfr.trans (by simp)
  have : Finite (fixedField U.val) := inferInstance
  have : FiniteDimensional (fixedField U.val) (fixedSpace U.val) := Module.Finite.of_finite
  have : FiniteDimensional (fixedField U.val) K := Module.Finite.of_finite
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hnd₀
  let ι : fixedSpace U.val →+ (Fin d → K) := (fixedSpace U.val).subtype.toAddMonoidHom
  have hι : ∀ w, ((c : K) • Q) (ι w) = algebraMap (fixedField U.val) K (Q₀ w) := by
    intro w
    have h1 := hQ₀ w
    change (c : K) * Q (w : Fin d → K) = ((Q₀ w : fixedField U.val) : K)
    exact h1.symm
  have hodd : Odd (finrank (fixedField U.val) K) := by
    rw [finrank_fixedField_eq hℓ hf U.val.right hK hcard hdvd]
    exact hp.odd_of_ne_two hp2
  let bK : Basis (Fin m ⊕ Fin m ⊕ Fin δ) K (Fin d → K) := (H.b.baseChange K).map Φ
  have hbK : ∀ a, bK a = ι (H.b a) := by
    intro a
    show Φ ((H.b.baseChange K) a) = _
    rw [Basis.baseChange_apply, hΦ1, one_smul]
    rfl
  let HK : HypSplit ((c : K) • Q) m δ := H.extend ι hι hδ hodd bK hbK
  have hndR := polarBilin_smul_nondegenerate Q hnd c
  have hw₀ : sourceWittIndex ⇑Q₀ = m := H.sourceWittIndex_eq hnd₀
  have hw₁ : sourceWittIndex ⇑((c : K) • Q) = m := HK.sourceWittIndex_eq hndR
  have hw₂ : sourceWittIndex ⇑Q = m := by
    rw [← sourceWittIndex_smul Q c]
    exact hw₁
  have hdim : 2 * m + δ = d := H.finrank_eq.symm.trans hfr'
  have hm3 : 3 ≤ m := by
    obtain ⟨T, hT3, hT⟩ := hS3
    have h3 := le_sourceWittIndex (K := K) (V := Fin d → K) (⇑Q) hT
    omega
  refine ⟨hdvd, hσord, ?_, U, c, Q₀, hUκ.trans hg, hUr, ⟨hUp, hQ₀, hnd₀, ⟨Φ, hΦ1, hΦ2, ?_⟩, hfr',
    hw₀.trans hw₂.symm, H.exists_totallySingular_three hm3⟩,
    ⟨⟨m, δ, hδ, H, HK, fun a => hbK a, hdim, hw₂⟩⟩⟩
  · rw [← hUr]
    exact hcard
  · intro x y w w'
    have hpol : ((QuadraticMap.polar Q₀ w w' : fixedField U.val) : K) =
        c * QuadraticMap.polar Q (w : Fin d → K) (w' : Fin d → K) := by
      simp only [QuadraticMap.polar, Subfield.coe_sub, hQ₀, Submodule.coe_add]
      ring
    rw [hΦ1, hΦ1]
    refine ⟨?_, ?_⟩
    · rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQ₀]
      ring
    · rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hpol]
      ring

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem plus_descent3 {n ℓ f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (G : Type) [Group G]
    (h : StatedClassicalModel G .POmegaPlus n ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range) (hap : orderOf a = p) :
    OrthogonalFieldDescent ℓ f p (coordinateQuadPlus n K)
      (fun U Q₀ => PlusFieldDescent n ℓ f p (coordinateQuadPlus n K) U Q₀) a := by
  obtain ⟨hℓ, hf, hn4⟩ := h.1
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f h K hK e
  have hd : 0 < 2 * n := by omega
  obtain ⟨g₀, hg₀⟩ := ha
  refine ⟨(descent_core_aux3 hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
  rintro σ ⟨g, hg, rfl⟩
  obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
    descent_core_aux3 hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g hg
  refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
  have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
    rw [← hUr] at hcard
    exact hcard
  obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
  have hle := le_sourceWittIndex_coordinateQuadPlus n K
  obtain ⟨rfl, rfl⟩ : m = n ∧ δ = 0 := by omega
  exact plus_field_descent ⟨hℓ, hfp, hn4⟩ hcard' H HK hbK

section Fixed

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

variable {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]

theorem inclHom_injective (k : Subfield K₀) :
    Function.Injective (inclHom k (coordinateQuadPlus_isExtension k 4)) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrArg (fun z : matrixDerived (coordinateQuadPlus 4 K₀) =>
    ((z : GL (Fin (2 * 4)) K₀) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K₀) i j) hxy
  simp only [inclHom_val, glIncl_val, Matrix.map_apply] at h
  exact h

theorem conj_fixes_incl (σ : K₀ ≃+* K₀) (g : similarityPairs (coordinateQuadPlus 4 K₀))
    (hl : g.val.left = 1) (hr : g.val.right = σ) (k : Subfield K₀) (hk : ∀ x ∈ k, σ x = x)
    (x : matrixDerived (coordinateQuadPlus 4 ↥k)) :
    matrixProjectiveConjugationHom (coordinateQuadPlus 4 K₀) g
      (matrixProjectiveProjection (coordinateQuadPlus 4 K₀)
        (inclHom k (coordinateQuadPlus_isExtension k 4) x)) =
    matrixProjectiveProjection (coordinateQuadPlus 4 K₀)
        (inclHom k (coordinateQuadPlus_isExtension k 4) x) := by
  change matrixProjectiveConjugation _ g _ = _
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [matrixDerivedConjugation_val, hl, hr]
  simp only [inv_one, one_mul, mul_one]
  ext i j
  change σ (((inclHom k (coordinateQuadPlus_isExtension k 4) x : matrixDerived (coordinateQuadPlus 4 K₀)) :
    GL (Fin (2 * 4)) K₀).val i j) = _
  rw [inclHom_val, glIncl_val, Matrix.map_apply]
  exact hk _ (Subtype.mem _)

theorem exists_fixed_embedding {n : ℕ} (hn1 : 1 ≤ n) (hK₀ : Nat.card K₀ = 2 ^ n)
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K₀)))
    (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K₀))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus 4 K₀)).range) (hap : orderOf a = 3) :
    3 ∣ n ∧ ∃ k : Subfield K₀, Nat.card k = 2 ^ (n / 3) ∧
      ∀ k₁ : Subfield K₀, k₁ ≤ k → ∃ j : matrixDerived (coordinateQuadPlus 4 ↥k₁) →*
        matrixProjectiveDerived (coordinateQuadPlus 4 K₀),
          Function.Injective j ∧ ∀ x, a (j x) = j x := by
  classical
  let e : matrixProjectiveDerived (coordinateQuadPlus 4 K₀) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 K₀)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K₀) (coe_quadPlus 4 K₀)).symm
  have hmodel : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K₀))
      .POmegaPlus 4 2 n :=
    ⟨⟨Nat.prime_two, hn1, le_refl 4⟩, K₀, inferInstance, inferInstance, hK₀, ⟨e⟩⟩
  have hD := plus_descent3 Nat.prime_three (by norm_num)
    (matrixProjectiveDerived (coordinateQuadPlus 4 K₀)) hmodel K₀ hK₀ e a ha haD hap
  obtain ⟨h3n, hσ⟩ := hD
  obtain ⟨g₀, hg₀⟩ := (mem_matrixProjectiveImage_iff (coordinateQuadPlus 4 K₀) a).1 ha
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hPlus⟩ := hσ g₀.val.right ⟨g₀, hg₀, rfl⟩
  obtain ⟨ν, S₀, hsim, hmodel₀, S, ν', hν', hS, hSU, Θ, hΘA, g', hg'l, hg'r, hΘ⟩ := hPlus
  refine ⟨h3n, semilinearFixedSubfield g₀.val.right, hcard, fun k₁ hk₁ => ?_⟩
  have hQne : ∃ v, coordinateQuadPlus 4 K₀ v ≠ 0 :=
    ⟨stdU K₀, by rw [coordinateQuadPlus_stdU]; exact one_ne_zero⟩
  let Λ := CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv (coordinateQuadPlus 4 K₀) hQne
  let j : matrixDerived (coordinateQuadPlus 4 ↥k₁) →*
      matrixProjectiveDerived (coordinateQuadPlus 4 K₀) :=
    (Θ.symm.toMonoidHom.comp Λ.toMonoidHom).comp (inclHom k₁ (coordinateQuadPlus_isExtension k₁ 4))
  refine ⟨j, ?_, fun x => ?_⟩
  · exact Θ.symm.injective.comp (Λ.injective.comp (inclHom_injective k₁))
  · have hk : ∀ z ∈ k₁, g₀.val.right z = z := fun z hz =>
      RingHom.mem_eqLocusField.mp (hk₁ hz)
    have hfix := conj_fixes_incl g₀.val.right g' hg'l (hg'r.trans hUr) k₁ hk x
    apply Θ.injective
    rw [← hUκ]
    have h1 := hΘ (j x)
    have h2 : Θ (j x) = matrixProjectiveProjection (coordinateQuadPlus 4 K₀)
        (inclHom k₁ (coordinateQuadPlus_isExtension k₁ 4) x) := by
      change Θ (Θ.symm (Λ (inclHom k₁ (coordinateQuadPlus_isExtension k₁ 4) x))) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [h1, h2, hfix]

end Fixed

end CFSG.LocalAnalysis.GLTheoremA.D4YH
