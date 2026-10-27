module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLin
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Mono

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Classical CFSG.ComponentClassification.CatLeaf
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2
open CFSG.Open (StatedLieAdmissible StatedSL StatedSU StatedProj StatedScalars)

namespace Up34Chev2

theorem dualPoly_eq_self_of_natDegree_one {ℓ f : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {a : K[X]} (ha : a.Monic)
    (h1 : a.natDegree = 1) (h0 : a.coeff 0 ≠ 0) : dualPoly hK.bar a = a := by
  have hm := monic_dualPoly (σ := hK.bar) h0
  have hd : (dualPoly hK.bar a).natDegree = 1 := by rw [natDegree_dualPoly h0, h1]
  have hc : (dualPoly hK.bar a).coeff 0 = a.coeff 0 := by
    rw [coeff_zero_dualPoly ha]
    have hb3 : (a.coeff 0) ^ 3 = 1 :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.pow_three_eq_one hK hq h0
    rw [UnitaryFieldData.bar_apply, hq]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hb3)
  calc dualPoly hK.bar a = X + C ((dualPoly hK.bar a).coeff 0) := hm.eq_X_add_C hd
    _ = X + C (a.coeff 0) := by rw [hc]
    _ = a := (ha.eq_X_add_C h1).symm

section Models

theorem lieModel_centerQuotient_of_equiv_gramSU {G : Type} [Group G] {m : ℕ} {E : Type} [Field E]
    {ℓ f : ℕ} (hE : UnitaryFieldData ℓ f E) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ ℓ ^ f = 2))
    (e : G ≃* ↥(gramSU hE (idGram E m))) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .PSU m ℓ f := by
  haveI := hE.finite
  have hs := isSimpleGroup_primeFormP_one hE hm hq
  have hnc := not_commute_primeFormP_one hE hm hq
  haveI : IsSimpleGroup (primeFormP hE (idGram E m)) := hs
  have hZ : Subgroup.center ↥(gramSU hE (idGram E m)) =
      normOneScalars hE (gramSU hE (idGram E m)) m := by
    refine le_antisymm (fun z hz => ?_) (normOneScalars_le_center hE _ m)
    have hz' : (QuotientGroup.mk z : primeFormP hE (idGram E m)) ∈
        Subgroup.center (primeFormP hE (idGram E m)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.1 hz g
    have hbot : Subgroup.center (primeFormP hE (idGram E m)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (primeFormP hE (idGram E m))) with h | h
      · exact h
      · exfalso
        apply hnc
        intro x y
        have hx : x ∈ Subgroup.center (primeFormP hE (idGram E m)) := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.1 hx y).symm
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz'
    exact hz'
  have hadm : StatedLieAdmissible .PSU m ℓ f :=
    ⟨hE.prime, hE.one_le, hm, fun hc => hq ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv hE (isPrimeFormGram_one (n := m) (K := E))
  refine (lieModel_classical_iff (by decide)).mpr ⟨hadm, E, inferInstance, inferInstance,
    hE.card_eq_sq, ?_⟩
  exact ⟨((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq hZ)).trans (eP.trans (unitaryPSUEquiv hE (by omega)))⟩

end Models

section Block

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem specialBlock_eq_kerImage_c2 {a : K[X]} {Ω : Type*} [Group Ω]
    (φ : orbitFactor B x a ≃* Ω) (ι : Ω →* blockGL (x : Module.End K V) a)
    (D : Ω →* (AdjoinRoot a)ˣ) (hD : ∀ w, D w = blockGLDet (x : Module.End K V) a (ι w))
    (hcompat : ∀ s : orbitFactor B x a,
      ι (φ s) = blockRestrict x a ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) :
    specialBlock B x a = kerImage (orbitFactor B x a) φ D := by
  ext g
  rw [mem_specialBlock, mem_kerImage]
  constructor
  · rintro ⟨hs, hg, h⟩
    refine ⟨hs, ?_⟩
    rw [hD, hcompat ⟨g, hs⟩]
    exact h
  · rintro ⟨hs, h⟩
    refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
    rw [hD, hcompat ⟨g, hs⟩] at h
    exact h

theorem nonempty_specialBlock_mulEquiv_SL_c2 {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a) :
    Nonempty (↥(specialBlock B x (a : K[X])) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (AdjoinRoot (a : K[X]))) := by
  obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
  have hspec := specialBlock_eq_kerImage_c2 φ (MonoidHom.id _)
    (blockGLDet (x : Module.End K V) (a : K[X])) (fun _ => rfl)
    (fun s => blockGL_ext fun v hv => hφ s v hv)
  obtain ⟨e1⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ
    (blockGLDet (x : Module.End K V) (a : K[X]))
  obtain ⟨e2⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det (E := AdjoinRoot (a : K[X]))
    (W := primaryComponent (x : Module.End K V) (a : K[X]))
  exact ⟨((MulEquiv.subgroupCongr hspec).trans e1).trans e2.symm⟩

theorem nonempty_specialBlock_mulEquiv_sesqSU_c2 {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X])),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf)) := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ := exists_selfDualFactor hself hS
  refine ⟨hE, Hf, hHf, hHfl, ?_⟩
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage_c2 φ (sesqUnitaryGroup Hf).subtype D (fun _ => rfl)
    (fun s => blockGL_ext fun v hv => hφ s v hv)
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, blockGLDet] using h
  obtain ⟨e1⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
  exact ⟨((MulEquiv.subgroupCongr hspec).trans e1).trans
    ((MulEquiv.subgroupCongr hker).trans
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)))⟩

theorem not_isLThreeFour_specialBlock_two (hO : LieOrderFormulasInput) (hℓ : ℓ = 2)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (ha : IsGoodBlock hK x a) :
    ¬ IsLThreeFour (↥(specialBlock B x (a : K[X])) ⧸
      Subgroup.center ↥(specialBlock B x (a : K[X]))) := by
  subst hℓ
  have hprime : Nat.Prime 2 := Nat.prime_two
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  haveI := hK.finite
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos hK.one_le hd
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU_c2 hself (selfDualPrimaryBlock H a hself)
    have hgood := ha.2 hself
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    ·
      have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf
        hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      have hm2' : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
      rw [hm2'] at hgood
      have hadm : StatedLieAdmissible .PSL 2 2 (f * (a : K[X]).natDegree) :=
        ⟨hprime, hfd, le_rfl, fun hc => hgood (by
          have := (Prod.mk.inj hc).2
          simp [this]), fun hc => hgood (by
          have := (Prod.mk.inj hc).2
          simp [this])⟩
      have hmodel := lieModel_centerQuotient_of_equiv_SL_c2 hadm hE.card_fixedField (e.trans e2)
      intro hL
      rcases isLThreeFour_cases_psl_two hO hmodel hL with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    ·
      obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e2⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU
        hE b (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))))
          (Fin (Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
        (fun i j => by rw [hb i j, Matrix.one_apply])
      have hm3 : 3 ≤ Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) := hm
      have hq : ¬(Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 3 ∧
          2 ^ (f * (a : K[X]).natDegree) = 2) := by
        rintro ⟨h3, h2⟩
        exact hgood (by
          simp [show primaryMultiplicity (x : Module.End K V) (a : K[X]) = 3 from h3, h2])
      exact not_isLThreeFour_psu_two hO
        (lieModel_centerQuotient_of_equiv_gramSU hE hm3 hq (e.trans e2))
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL_c2 (pairedPrimaryBlock H a (Ne.symm hself))
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = 2 ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot hK
    have hadm : StatedLieAdmissible .PSL (primaryMultiplicity (x : Module.End K V) (a : K[X])) 2
        (2 * (f * (a : K[X]).natDegree)) :=
      ⟨hprime, by omega, hm2, fun hc => by
        have := (Prod.mk.inj hc).2
        have h4 : 2 ^ 1 ≤ 2 ^ (2 * (f * (a : K[X]).natDegree)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h5 : 2 ^ 2 ≤ 2 ^ (2 * (f * (a : K[X]).natDegree)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega, fun hc => by
        have := (Prod.mk.inj hc).2
        have h5 : 2 ^ 2 ≤ 2 ^ (2 * (f * (a : K[X]).natDegree)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega⟩
    intro hL
    have hmodel := lieModel_centerQuotient_of_equiv_SL_c2 hadm hcard e
    rcases isLThreeFour_cases_psl_two hO hmodel hL with ⟨hm3, hfd2⟩ | ⟨hm4, hfd1⟩
    ·
      have hf1 : f = 1 := by
        have : f * (a : K[X]).natDegree = 1 := by omega
        exact (Nat.eq_one_of_mul_eq_one_right this)
      have hd1 : (a : K[X]).natDegree = 1 := by
        have : f * (a : K[X]).natDegree = 1 := by omega
        exact (Nat.eq_one_of_mul_eq_one_left this)
      exact hself (dualPoly_eq_self_of_natDegree_one hK (by rw [hf1]; norm_num)
        (monic_of_mem_primaryFactors a.2) hd1
        (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree a.2))
    · omega

end Block

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
