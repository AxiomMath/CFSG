module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagField
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartOne.K133C.InnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

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


open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne

theorem d4_field_descent3 (G : Type) [Group G] {ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range) (hap : orderOf a = p) :
    OrthogonalFieldDescent ℓ f p (coordinateQuadPlus 4 K)
      (fun U Q₀ => PlusFieldDescent 4 ℓ f p (coordinateQuadPlus 4 K) U Q₀) a := by
  obtain ⟨hℓ, hf, hn4⟩ := h.1
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 ℓ f h K hK e
  have hd : 0 < 2 * 4 := by omega
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
  have hle := le_sourceWittIndex_coordinateQuadPlus 4 K
  obtain ⟨rfl, rfl⟩ : m = 4 ∧ δ = 0 := by omega
  exact plus_field_descent ⟨hℓ, hfp, hn4⟩ hcard' H HK hbK

theorem three_dvd_ordD_four {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ CFSG.Open.ordD 4 q := by
  unfold CFSG.Open.ordD
  set P := ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) with hP
  set g := Nat.gcd 4 (q ^ 4 - 1) with hg
  have h2 : 3 ∣ q ^ 2 - 1 := by
    have h1 : q ^ 2 % 3 = 1 := by
      rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h <;> simp [Nat.pow_mod, h]
    have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hP3 : 3 ∣ P := by
    refine h2.trans ?_
    have := Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (show 1 ∈ Finset.Icc 1 (4 - 1) by
      simp)
    simpa using this
  have hN3 : 3 ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * P := Dvd.dvd.mul_left hP3 _
  have hgN : g ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * P :=
    (Nat.gcd_dvd_right 4 (q ^ 4 - 1)).trans
      ((dvd_mul_left (q ^ 4 - 1) (q ^ (4 * (4 - 1)))).trans (dvd_mul_right _ P))
  have hg3 : Nat.Coprime 3 g :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 _) (by norm_num)
  have hmul := Nat.div_mul_cancel hgN
  have : 3 ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * P / g * g := by rw [hmul]; exact hN3
  exact hg3.dvd_of_dvd_mul_right this

theorem card_model_plus {X : Type} [Group X] {n ℓ f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus n ℓ f) : Nat.card X = CFSG.Open.ordD n (ℓ ^ f) := by
  by_cases h2 : ℓ = 2
  · subst h2
    exact (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl
  · exact (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two h2 h).2.2.2.2.1 rfl

section Balance

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

theorem d4_localDeltaIn_eq_bot_of_field (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (hℓ3 : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range) (hap : orderOf a = 3)
    {D H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (haDm : a ∈ D) (hH : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hℓ, hf, hn4⟩ := h.1
  obtain ⟨hdvd, hdesc⟩ := d4_field_descent3 G h hp hp2 K hK e a ha haD hap
  obtain ⟨g, hg⟩ := ha
  obtain ⟨hord, hcard, U, c, Q₀, hUκ, hUr, hFFD, hdisp⟩ := hdesc g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, hS₀, hmodel₀, S, ν', hQ', hS, hSU, Θ, hΘ, g', hg'l, hg'r, hg'⟩ := hdisp
  set σ := g.val.right with hσ
  set k := semilinearFixedSubfield σ with hk
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have Sset := subfieldSetup_plus k hσk hp hp2 hord (n := 4) (by norm_num)
  have hmodelK : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K))
      .POmegaPlus 4 ℓ f :=
    ⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm⟩⟩
  have hE : ∀ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      (∀ t ∈ subfieldDerivedImage k Sset.hext, β t = t) →
      β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := fun β hβ =>
    mem_matrixProjectiveImage_plus_four k hK hmodelK (statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm Sset.hext Sset.hnd₀ Sset.hT₀ β hβ
  have hconc := subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer Sset hE
  obtain ⟨⟨-, hsimp, hnonab⟩, hordy, hfixN, hJN, hJnorm, -, -, -, hfixJ, -⟩ := hconc
  have hd : 0 < 2 * 4 := by norm_num
  have hinj := CFSG.RankThree.PartOne.K133C.conj_injective_of_center_bot
    (center_matrix_eq_bot hd Sset.hnd Sset.hT)
  have hg'eq : g' = fieldPair (coordinateQuadPlus 4 K) σ Sset.hQσ :=
    Subtype.ext (SemidirectProduct.ext hg'l (hg'r.trans hUr))
  have hconj : ∀ x, a x = Θ.symm (fieldAutT (coordinateQuadPlus 4 K) σ Sset.hQσ (Θ x)) := by
    intro x
    have h1 := hg' x
    rw [hUκ, hg'eq] at h1
    apply Θ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h1
  have ha1 : a ≠ 1 := fun h1 => haD (h1 ▸ (linearConjugationHom _).range.one_mem)
  have hTq : CFSG.IsQuasisimple (subfieldDerivedImage k Sset.hext) := by
    have := hsimp
    have hab : ∃ x y : subfieldDerivedImage k Sset.hext, x * y ≠ y * x := hnonab
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hab).1
  have hℓp : ¬ 3 ∣ ℓ ^ (f / 3) := fun h3 =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3))
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hdvd) hp.pos
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 ↥k))
      .POmegaPlus 4 ℓ (f / 3) :=
    ⟨⟨hℓ, hfp, hn4⟩, ↥k, inferInstance, inferInstance, hcard, ⟨(statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 ↥k) (coe_quadPlus 4 ↥k)).symm⟩⟩
  have hTp : 3 ∣ Nat.card (subfieldDerivedImage k Sset.hext) := by
    rw [← Nat.card_congr (inclEquiv k Sset.hext hd).toEquiv, card_model_plus hmodelk]
    exact three_dvd_ordD_four hℓp
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub hp hinj hH haDm ha1 Θ.symm
    (fieldAutT (coordinateQuadPlus 4 K) σ Sset.hQσ) ?_ (subfieldDerivedImage k Sset.hext)
    (fun t ht => (hfixN t).2 (hJN ht)) ?_ hTq hTp ?_
  · ext x
    exact hconj x
  · intro x hx t ht
    have hxN : x ∈ subfieldFixedGroup k (coordinateQuadPlus 4 k) (coordinateQuadPlus 4 K) :=
      (hfixN x).1 hx
    have := hJnorm.conj_mem ⟨t, hJN ht⟩ (Subgroup.mem_subgroupOf.2 ht) ⟨x, hxN⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro g₁ hg₁ hfix
    have hmem : g₁ ∈ fixingSubgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (subfieldDerivedImage k Sset.hext :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
      (mem_fixingSubgroup_iff _).mpr fun t ht => by simpa using hfix t ht
    rw [hfixJ] at hmem
    have h1 : orderOf g₁ ∣ 3 := by rw [← hordy]; exact orderOf_dvd_of_mem_zpowers hmem
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hg₁.symm h1)

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
