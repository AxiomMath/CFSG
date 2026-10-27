module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamOrthCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

private theorem fixSubgroup_conj_eq_centralizer {X : Type} [Group X] (a : X) :
    fixSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set X) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul, eq_comm]


private theorem orth_census_of_model {S : Type} [Group S] {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (θ : S ≃* CFSG.RankThree.Classical2.ProjOrthDerived Q) (η : MulAut S) (t : S)
    (hη : η = MulAut.conj t) (ht3 : t ^ 3 = 1) (hη1 : η ≠ 1) {r : ℕ} (hr : Odd r) (hr1 : 1 < r)
    {J₁ J₂ J₃ : Subgroup S} (hJ₁ : CFSG.Open.IsComponentOf J₁ (fixSubgroup η))
    (hJ₂ : CFSG.Open.IsComponentOf J₂ (fixSubgroup η))
    (hJ₃ : CFSG.Open.IsComponentOf J₃ (fixSubgroup η))
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    (hL1 : catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r))
    (hL2 : catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r))
    (hL3 : catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r)) :
    Module.finrank K V = 8 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Nat.card K = 2 ^ r := by
  classical
  let a : CFSG.RankThree.Classical2.ProjOrthDerived Q := θ t
  have hβ : θ.symm.trans (η.trans θ) = MulAut.conj a := by
    ext y
    show θ (η (θ.symm y)) = a * y * a⁻¹
    rw [hη]
    simp [MulAut.conj_apply, a, map_mul]
  have ha3 : a ^ 3 = 1 := by
    rw [← map_pow, ht3, map_one]
  have ha1 : a ≠ 1 := by
    intro h1
    apply hη1
    have : (MulAut.congr θ) η = 1 := by
      change θ.symm.trans (η.trans θ) = 1
      rw [hβ, h1, map_one]
    exact (MulAut.congr θ).injective (by rw [this, map_one])
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ η
  rw [hβ, fixSubgroup_conj_eq_centralizer] at hfix
  have hJ' : ∀ {J : Subgroup S}, CFSG.Open.IsComponentOf J (fixSubgroup η) →
      CFSG.Open.IsComponentOf (J.map θ.toMonoidHom) (Subgroup.centralizer ({a} : Set _)) := by
    intro J hJ
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJ
    exact hfix ▸ h1
  have hLT : ∀ {J : Subgroup S},
      catalogIs (↥J ⧸ Subgroup.center ↥J) (S10.isL2n r) →
        catalogIs (↥(J.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J.map θ.toMonoidHom))
          (S10.isL2n r) := by
    intro J hJ
    have eJ : ↥J ≃* ↥(J.map θ.toMonoidHom) := J.equivMapOfInjective θ.toMonoidHom θ.injective
    have eZ : (↥J ⧸ Subgroup.center ↥J) ≃*
        (↥(J.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J.map θ.toMonoidHom)) :=
      QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
    exact (catalogIs_congr eZ).1 hJ
  exact orth_three_L2 hQ hT haord hr hr1 (hJ' hJ₁) (hJ' hJ₂) (hJ' hJ₃)
    (fun h => h12 (Subgroup.map_injective θ.injective h))
    (fun h => h13 (Subgroup.map_injective θ.injective h))
    (fun h => h23 (Subgroup.map_injective θ.injective h)) (hLT hL1) (hLT hL2) (hLT hL3)

private theorem exists_inner_of_matrixModel {S : Type} [Group S] {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)}
    (θ₁ : S ≃* CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q)
    (hZ : Subgroup.center
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q) = ⊥)
    (hinner : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β ∈ innAutDerived
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q),
      β ^ p = 1 → β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q))
    (η : MulAut S) (hmem : η ∈ innAutDerived S) (hη3 : η ^ 3 = 1) :
    ∃ t : S, η = MulAut.conj t ∧ t ^ 3 = 1 := by
  let β₁ := MulAut.congr θ₁ η
  have hβ₁mem : β₁ ∈ innAutDerived
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived Q) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ₁).2 hmem
  have hβ₁3 : β₁ ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ₁) η 3
    rw [hη3, map_one] at h3
    exact h3.symm
  obtain ⟨a₁, ha₁, hβ₁eq⟩ := CFSG.ComponentClassification.OuterAutomorphisms.exists_pow_eq_one_of_mem_inner
    hZ (hinner 3 Nat.prime_three (by norm_num) β₁ hβ₁mem hβ₁3) hβ₁3
  refine ⟨θ₁.symm a₁, ?_, ?_⟩
  · apply (MulAut.congr θ₁).injective
    rw [show MulAut.congr θ₁ (MulAut.conj (θ₁.symm a₁)) = MulAut.conj a₁ by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply, map_mul]]
    exact hβ₁eq
  · rw [← map_pow, ha₁, map_one]

theorem censusBodyTwistedD : CensusBodyTwistedD := by
  intro n q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  classical
  obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hv (MulEquiv.refl _)
  swap
  · have h4n : 4 ≤ n := hadm.2.2
    omega
  have hG0 := hSC
  haveI : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD n q, hv⟩) :=
    CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
  obtain ⟨hadm', K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := hSC
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm'.2.2
  have hn1 : 1 ≤ n := by omega
  have hchar : ringChar K = 2 :=
    (CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm'.1 hadm'.2.1 hK).trans hq2
  haveI : CharP K 2 := ringChar.of_eq hchar
  obtain ⟨-, -, hZ, hinner⟩ := KD264Lie.matrixModel_facts_pomegaMinus hG0 hK hn1 b c hirr e
  obtain ⟨t, hηt, ht3⟩ := exists_inner_of_matrixModel
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv
      K hn1 b c e) hZ hinner η hmem hη3
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) hn4 hirr
  obtain ⟨-, hplus, -⟩ := orth_census_of_model hQ hT
    (e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))) η t hηt ht3 hη1 hr hr1 hJ₁ hJ₂ hJ₃
    h12 h13 h23 hL1 hL2 hL3
  exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hn1 hirr hplus


@[expose] def CensusBodyD4Graph : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 →
    ∀ η : MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group,
      η ∈ innAutDerived (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group →
      η ^ 3 = 1 →
      (∀ t : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group,
        MulAut.conj t ≠ η) →
      ∀ r : ℕ, Odd r → 1 < r →
      ∀ J₁ J₂ J₃ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group,
        CFSG.Open.IsComponentOf J₁ (fixSubgroup η) → CFSG.Open.IsComponentOf J₂ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₃ (fixSubgroup η) → J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ →
        catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) →
        catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r) →
        catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r) → False

theorem censusBodyD_of_graph (hg : CensusBodyD4Graph) : CensusBodyD := by
  intro n q hv hq2 η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  classical
  obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hv (MulEquiv.refl _)
  swap
  · have h4n : 4 ≤ n := hadm.2.2
    omega
  have hG0 := hSC
  haveI : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.D n q, hv⟩) :=
    CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
  obtain ⟨hadm', K, hfield, hfinite, hK, ⟨e⟩⟩ := hSC
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm'.2.2
  have hchar : ringChar K = 2 :=
    (CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm'.1 hadm'.2.1 hK).trans hq2
  haveI : CharP K 2 := ringChar.of_eq hchar
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n) (by omega)
  let θ := e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
    (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    simp [Module.finrank_fintype_fun_eq_card]
    ring
  by_cases hn5 : 5 ≤ n
  ·
    exfalso
    obtain ⟨-, -, hZ, hinner⟩ := KD264Lie.matrixModel_facts_pomegaPlus hG0 hn5 hK e
    obtain ⟨t, hηt, ht3⟩ := exists_inner_of_matrixModel
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e)
      hZ hinner η hmem hη3
    obtain ⟨h8, -, -⟩ := orth_census_of_model hQ hT θ η t hηt ht3 hη1 hr hr1 hJ₁ hJ₂ hJ₃
      h12 h13 h23 hL1 hL2 hL3
    omega
  · have hn : n = 4 := by omega
    subst hn
    by_cases hinn : ∃ t, MulAut.conj t = η
    · obtain ⟨t, hηt⟩ := hinn
      have hZ : Subgroup.center (CFSG.RankThree.Classical2.ProjOrthDerived (CFSG.LieType.Universal.Spin.quadPlus 4 K)) = ⊥ := by
        obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
          CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
        exact CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
      have hS0 : Subgroup.center (TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) = ⊥ := by
        have h1 := Subgroup.map_center_eq θ
        rw [hZ] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h1
      have ht3 : t ^ 3 = 1 :=
        CFSG.mulAutConj_injective_of_center_eq_bot hS0 (by rw [map_pow, hηt, hη3, map_one])
      obtain ⟨h8, -, hcardK⟩ := orth_census_of_model hQ hT θ η t hηt.symm ht3 hη1 hr hr1 hJ₁ hJ₂ hJ₃
        h12 h13 h23 hL1 hL2 hL3
      right
      refine ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, ?_, ⟨MulEquiv.refl _⟩⟩
      show q.p = 2 ∧ q.exponent = r
      refine ⟨hq2, ?_⟩
      have h2 : 2 ^ q.exponent = 2 ^ r := by
        rw [hq2] at hK
        rw [← hK, hcardK]
      exact Nat.pow_right_injective (le_refl 2) h2
    · exfalso
      push Not at hinn
      exact hg q hv hq2 η hmem hη3 hinn r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3

end CFSG.LocalAnalysis.GLTheoremA.T1428
