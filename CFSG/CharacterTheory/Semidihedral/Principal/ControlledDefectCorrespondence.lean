module

public import CFSG.CharacterTheory.Wreathed.DefectNormalizerBrauerCorrespondence
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerProjectionTower

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace ControlledDefect

section Transport

variable {K K' : Type*} [Group K] [Group K']

theorem conjClasses_map_mk (e : K ≃* K') (x : K) :
    (ConjClasses.mk x).map e.toMonoidHom = ConjClasses.mk (e x) := rfl

theorem conjClasses_map_symm_map (e : K ≃* K') (C : ConjClasses K') :
    (C.map e.symm.toMonoidHom).map e.toMonoidHom = C := by
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
  change ConjClasses.mk (e (e.symm c)) = ConjClasses.mk c
  rw [e.apply_symm_apply]

theorem subgroup_map_symm_map (e : K ≃* K') (Q : Subgroup K') :
    (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
  rw [Subgroup.map_map]
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K' := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

theorem centralizer_singleton_map_equiv (e : K ≃* K') (r : K) :
    (Subgroup.centralizer ({r} : Set K)).map e.toMonoidHom =
      Subgroup.centralizer ({e r} : Set K') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change e x * e r = e r * e x
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy']

theorem subgroupSubconjugate_map_equiv (e : K ≃* K') {A B : Subgroup K}
    (h : subgroupSubconjugate A B) :
    subgroupSubconjugate (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨e g, ?_⟩
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨(MulAut.conj g) a, hg ⟨a, ha, rfl⟩, ?_⟩
  change e (g * a * g⁻¹) = e g * e a * (e g)⁻¹
  rw [map_mul, map_mul, map_inv]

variable [Finite K] [Finite K']

omit [Finite K'] in
theorem classDefect_map_equiv (p : ℕ) [Fact p.Prime] (e : K ≃* K') {C : ConjClasses K}
    {Q : Subgroup K} (h : classDefect p C Q) :
    classDefect p (C.map e.toMonoidHom) (Q.map e.toMonoidHom) := by
  obtain ⟨r, rfl, sylow, rfl⟩ := h
  let f : Subgroup.centralizer ({r} : Set K) ≃* Subgroup.centralizer ({e r} : Set K') :=
    (e.subgroupMap (Subgroup.centralizer ({r} : Set K))).trans
      (MulEquiv.subgroupCongr (centralizer_singleton_map_equiv e r))
  have hf : Function.Surjective f.toMonoidHom := fun y => ⟨f.symm y, f.apply_symm_apply y⟩
  refine ⟨e r, rfl, sylow.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  congr 1

variable [Fintype K] [Fintype K']

omit [Finite K] [Finite K'] in
theorem centralConjugacyClassSum_transport (ring : Subring ℂ) (e : K ≃* K') (C : ConjClasses K) :
    centralCoefficientTransport ring e (centralConjugacyClassSum ring C) =
      centralConjugacyClassSum ring (C.map e.toMonoidHom) := by
  apply Subtype.ext
  ext y
  rw [centralCoefficientTransport_coeff]
  change (conjugacyClassSum (ring := ℂ) C).coeff (e.symm y) =
    (conjugacyClassSum (ring := ℂ) (C.map e.toMonoidHom)).coeff y
  rw [conjugacyClassSum_coeff, conjugacyClassSum_coeff]
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
  rw [conjClasses_map_mk]
  have hiff :
      ConjClasses.mk (e.symm y) = ConjClasses.mk c ↔ ConjClasses.mk y = ConjClasses.mk (e c) := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro h
      have := e.toMonoidHom.map_isConj h
      simpa using this
    · intro h
      have := e.symm.toMonoidHom.map_isConj h
      simpa using this
  simp only [hiff]

theorem coefficientBlockDefect_map_equiv (sourceBasis : FiniteIrreducibleCharacterBasis K)
    (targetBasis : FiniteIrreducibleCharacterBasis K') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] (e : K ≃* K') {ℓ : sourceBasis.index}
    {ℓ' : targetBasis.index}
    (hres : ∀ z, centralCharacterResidueHom targetBasis ideal ℓ'
      (centralCoefficientTransport _ e z) = centralCharacterResidueHom sourceBasis ideal ℓ z)
    {D : Subgroup K} (hdefect : coefficientBlockDefect sourceBasis ideal p ℓ D) :
    coefficientBlockDefect targetBasis ideal p ℓ' (D.map e.toMonoidHom) := by
  refine ⟨?_, fun C' Q' hC' hne' => ?_⟩
  · obtain ⟨C, hC, hne⟩ := hdefect.1
    refine ⟨C.map e.toMonoidHom, classDefect_map_equiv p e hC, ?_⟩
    rw [← centralConjugacyClassSum_transport, hres]
    exact hne
  · have hC := classDefect_map_equiv p e.symm hC'
    have hne : centralCharacterResidueHom sourceBasis ideal ℓ
        (centralConjugacyClassSum _ (C'.map e.symm.toMonoidHom)) ≠ 0 := by
      rw [← hres, centralConjugacyClassSum_transport, conjClasses_map_symm_map]
      exact hne'
    have hsub := subgroupSubconjugate_map_equiv e (hdefect.2 _ _ hC hne)
    rwa [subgroup_map_symm_map] at hsub

end Transport

section Normalizer

variable {G : Type*} [Group G]

@[expose] noncomputable def normalizerInEquiv (D H : Subgroup G) (hDH : D ≤ H)
    (hND : Subgroup.normalizer (D : Set G) ≤ H) :
    Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H) ≃*
      Subgroup.normalizer (D : Set G) :=
  (MulEquiv.subgroupCongr (Subgroup.subgroupOf_normalizer_eq hDH).symm).trans
    (Subgroup.subgroupOfEquivOfLe hND)

theorem normalizerInEquiv_apply (D H : Subgroup G) (hDH : D ≤ H)
    (hND : Subgroup.normalizer (D : Set G) ≤ H)
    (x : Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H)) :
    (normalizerInEquiv D H hDH hND x : G) = ((x : H) : G) := rfl

theorem normalizerInEquiv_symm_apply (D H : Subgroup G) (hDH : D ≤ H)
    (hND : Subgroup.normalizer (D : Set G) ≤ H) (y : Subgroup.normalizer (D : Set G)) :
    (((normalizerInEquiv D H hDH hND).symm y : H) : G) = y := rfl

theorem normalizerInEquiv_map_defect (D H : Subgroup G) (hDH : D ≤ H)
    (hND : Subgroup.normalizer (D : Set G) ≤ H) :
    ((D.subgroupOf H).subgroupOf (Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H))).map
        (normalizerInEquiv D H hDH hND).toMonoidHom =
      D.subgroupOf (Subgroup.normalizer (D : Set G)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨(normalizerInEquiv D H hDH hND).symm y, hy, MulEquiv.apply_symm_apply _ _⟩

theorem normalizerInEquiv_symm_map_defect (D H : Subgroup G) (hDH : D ≤ H)
    (hND : Subgroup.normalizer (D : Set G) ≤ H) :
    (D.subgroupOf (Subgroup.normalizer (D : Set G))).map
        (normalizerInEquiv D H hDH hND).symm.toMonoidHom =
      (D.subgroupOf H).subgroupOf
        (Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H)) := by
  rw [← normalizerInEquiv_map_defect D H hDH hND, Subgroup.map_map]
  have hcomp : (normalizerInEquiv D H hDH hND).symm.toMonoidHom.comp
      (normalizerInEquiv D H hDH hND).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

variable [Fintype G]

theorem brauerProjection_compose (ring : Subring ℂ) (P H D : Subgroup G)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (hPD : P ≤ D) (hDH : D ≤ H) (hND : Subgroup.normalizer (D : Set G) ≤ H)
    (z : centralCoefficientSubring (G := G) ring) :
    centralCoefficientTransport ring (normalizerInEquiv D H hDH hND)
        (centralNormalizerCoefficientProjection ring (D.subgroupOf H)
          (Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H))
          (Subgroup.centralizer_le_normalizer _) le_rfl
          (centralNormalizerCoefficientProjection ring P H hCH hHN z)) =
      centralNormalizerCoefficientProjection ring D (Subgroup.normalizer (D : Set G))
        (Subgroup.centralizer_le_normalizer _) le_rfl z := by
  apply Subtype.ext
  ext y
  rw [centralCoefficientTransport_coeff, centralNormalizerCoefficientProjection_coeff,
    centralNormalizerCoefficientProjection_coeff, centralNormalizerCoefficientProjection_coeff]
  have hmem : ((normalizerInEquiv D H hDH hND).symm y).val ∈
      Subgroup.centralizer ((D.subgroupOf H : Subgroup H) : Set H) ↔
        (y : G) ∈ Subgroup.centralizer (D : Set G) :=
    relativeCentralizer_mem_iff D H hDH _
  by_cases hy : (y : G) ∈ Subgroup.centralizer (D : Set G)
  · rw [ite_eq_left (hmem.mpr hy), ite_eq_left hy]
    have hyP : (((normalizerInEquiv D H hDH hND).symm y : H) : G) ∈
        Subgroup.centralizer (P : Set G) := Subgroup.centralizer_le hPD hy
    rw [ite_eq_left hyP]
    rfl
  · rw [ite_eq_right (fun h => hy (hmem.mp h)), ite_eq_right hy]

end Normalizer

end ControlledDefect

open ControlledDefect

theorem intermediate_normalizer_controlled_defect_correspondence {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup G) (hP : IsPGroup p P)
    (H : Subgroup G) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (D : Subgroup G) (hD : IsPGroup p D)
    (hPD : P ≤ D) (hDH : D ≤ H) (hND : Subgroup.normalizer (D : Set G) ≤ H)
    (localBasis : FiniteIrreducibleCharacterBasis H) :
    (∀ β : localBasis.index, ∃ χ : basis.index,
      brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN localBasis β =
        centralCharacterResidueHom basis ideal χ) ∧
    (∀ (β : localBasis.index) (χ : basis.index),
      coefficientBlockDefect localBasis ideal p β (D.subgroupOf H) →
      brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN localBasis β =
        centralCharacterResidueHom basis ideal χ →
      coefficientBlockDefect basis ideal p χ D) ∧
    (∀ χ : basis.index, coefficientBlockDefect basis ideal p χ D →
      ∃ β : localBasis.index, coefficientBlockDefect localBasis ideal p β (D.subgroupOf H) ∧
        brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN localBasis β =
          centralCharacterResidueHom basis ideal χ) ∧
    (∀ β₁ β₂ : localBasis.index,
      coefficientBlockDefect localBasis ideal p β₁ (D.subgroupOf H) →
      coefficientBlockDefect localBasis ideal p β₂ (D.subgroupOf H) →
      brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN localBasis β₁ =
        brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN localBasis β₂ →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₁ β₂) := by
  have hDHp : IsPGroup p (D.subgroupOf H) := hD.comap_subtype
  set e := normalizerInEquiv D H hDH hND with he
  obtain ⟨normalizerBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer (D : Set G))
  obtain ⟨localNormalizerBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H))
  obtain ⟨-, hmapG, hsurjG, hinjG⟩ := CFSG.Wreathed.defect_normalizer_brauer_correspondence basis
    ideal p D hD normalizerBasis
  obtain ⟨himageH, hmapH, hsurjH, -⟩ := CFSG.Wreathed.defect_normalizer_brauer_correspondence
    localBasis ideal p (D.subgroupOf H) hDHp localNormalizerBasis
  have hcompose : ∀ (α : normalizerBasis.index) (α' : localNormalizerBasis.index)
      (β : localBasis.index),
      (∀ w, centralCharacterResidueHom normalizerBasis ideal α (centralCoefficientTransport _ e w) =
        centralCharacterResidueHom localNormalizerBasis ideal α' w) →
      brauerNormalizerCharacterResidueHom ideal p (D.subgroupOf H) hDHp
          (Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H))
          (Subgroup.centralizer_le_normalizer _) le_rfl localNormalizerBasis α' =
        centralCharacterResidueHom localBasis ideal β →
      brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN localBasis β =
        brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis α := by
    intro α α' β hres hβ
    apply RingHom.ext
    intro z
    change centralCharacterResidueHom localBasis ideal β
      (centralNormalizerCoefficientProjection _ P H hCH hHN z) =
        centralCharacterResidueHom normalizerBasis ideal α
          (centralNormalizerCoefficientProjection _ D _ (Subgroup.centralizer_le_normalizer _)
            le_rfl z)
    rw [← hβ, ← brauerProjection_compose _ P H D hCH hHN hPD hDH hND z, hres]
    rfl
  have hdown : ∀ α' : localNormalizerBasis.index, ∃ α : normalizerBasis.index,
      ∀ w, centralCharacterResidueHom normalizerBasis ideal α (centralCoefficientTransport _ e w) =
        centralCharacterResidueHom localNormalizerBasis ideal α' w := fun α' =>
    centralCharacterResidueHom_transport_exists localNormalizerBasis normalizerBasis ideal e α'
  have hup : ∀ α : normalizerBasis.index, ∃ α' : localNormalizerBasis.index,
      ∀ w, centralCharacterResidueHom normalizerBasis ideal α (centralCoefficientTransport _ e w) =
        centralCharacterResidueHom localNormalizerBasis ideal α' w := by
    intro α
    obtain ⟨α', hα'⟩ := centralCharacterResidueHom_transport_exists normalizerBasis
      localNormalizerBasis ideal e.symm α
    refine ⟨α', fun w => ?_⟩
    rw [← hα', centralCoefficientTransport_inverse]
  have hdefectDown : ∀ {α : normalizerBasis.index} {α' : localNormalizerBasis.index},
      (∀ w, centralCharacterResidueHom normalizerBasis ideal α (centralCoefficientTransport _ e w) =
        centralCharacterResidueHom localNormalizerBasis ideal α' w) →
      coefficientBlockDefect localNormalizerBasis ideal p α'
        ((D.subgroupOf H).subgroupOf
          (Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H))) →
      coefficientBlockDefect normalizerBasis ideal p α
        (D.subgroupOf (Subgroup.normalizer (D : Set G))) := by
    intro α α' hres hα'
    have h := coefficientBlockDefect_map_equiv localNormalizerBasis normalizerBasis ideal p e hres
      hα'
    rwa [he, normalizerInEquiv_map_defect] at h
  have hdefectUp : ∀ {α : normalizerBasis.index} {α' : localNormalizerBasis.index},
      (∀ w, centralCharacterResidueHom normalizerBasis ideal α (centralCoefficientTransport _ e w) =
        centralCharacterResidueHom localNormalizerBasis ideal α' w) →
      coefficientBlockDefect normalizerBasis ideal p α
        (D.subgroupOf (Subgroup.normalizer (D : Set G))) →
      coefficientBlockDefect localNormalizerBasis ideal p α'
        ((D.subgroupOf H).subgroupOf
          (Subgroup.normalizer ((D.subgroupOf H : Subgroup H) : Set H))) := by
    intro α α' hres hα
    have hres' : ∀ z, centralCharacterResidueHom localNormalizerBasis ideal α'
        (centralCoefficientTransport _ e.symm z) =
          centralCharacterResidueHom normalizerBasis ideal α z := by
      intro z
      rw [← hres]
      congr 1
      have h := centralCoefficientTransport_inverse (localizedComplexIntegerRing ideal) e.symm z
      rwa [MulEquiv.symm_symm] at h
    have h := coefficientBlockDefect_map_equiv normalizerBasis localNormalizerBasis ideal p e.symm
      hres' hα
    rwa [he, normalizerInEquiv_symm_map_defect] at h
  refine ⟨fun β => brauerNormalizer_block_image_exists basis ideal p P hP H hCH hHN localBasis β,
    fun β χ hβ hχ => ?_, fun χ hχ => ?_, fun β₁ β₂ h₁ h₂ hBr => ?_⟩
  · obtain ⟨α', hα'def, hα'⟩ := hsurjH β hβ
    obtain ⟨α, hres⟩ := hdown α'
    exact hmapG α χ (hdefectDown hres hα'def) ((hcompose α α' β hres hα').symm.trans hχ)
  · obtain ⟨α, hαdef, hα⟩ := hsurjG χ hχ
    obtain ⟨α', hres⟩ := hup α
    obtain ⟨β, hβ⟩ := himageH α'
    exact ⟨β, hmapH α' β (hdefectUp hres hαdef) hβ, (hcompose α α' β hres hβ).trans hα⟩
  · obtain ⟨α₁', hα₁'def, hα₁'⟩ := hsurjH β₁ h₁
    obtain ⟨α₂', hα₂'def, hα₂'⟩ := hsurjH β₂ h₂
    obtain ⟨α₁, hres₁⟩ := hdown α₁'
    obtain ⟨α₂, hres₂⟩ := hdown α₂'
    have hsame := hinjG α₁ α₂ (hdefectDown hres₁ hα₁'def) (hdefectDown hres₂ hα₂'def)
      ((hcompose α₁ α₁' β₁ hres₁ hα₁').symm.trans (hBr.trans (hcompose α₂ α₂' β₂ hres₂ hα₂')))
    have hequal := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq normalizerBasis ideal
      α₁ α₂).mp hsame
    have hlocal : centralCharacterResidueHom localNormalizerBasis ideal α₁' =
        centralCharacterResidueHom localNormalizerBasis ideal α₂' := by
      apply RingHom.ext
      intro w
      rw [← hres₁, ← hres₂, hequal]
    rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq, ← hα₁', ← hα₂']
    apply RingHom.ext
    intro z
    change centralCharacterResidueHom localNormalizerBasis ideal α₁' _ =
      centralCharacterResidueHom localNormalizerBasis ideal α₂' _
    rw [hlocal]

theorem centralizer_normalizer_controlled_defect_correspondence {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup G) (hP : IsPGroup p P)
    (D : Subgroup G) (hD : IsPGroup p D) (hPD : P ≤ D)
    (hDC : D ≤ Subgroup.centralizer (P : Set G))
    (hND : Subgroup.normalizer (D : Set G) ≤ Subgroup.centralizer (P : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set G))) :
    (∀ β : localBasis.index, ∃ χ : basis.index,
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis β =
          centralCharacterResidueHom basis ideal χ) ∧
    (∀ (β : localBasis.index) (χ : basis.index),
      coefficientBlockDefect localBasis ideal p β
        (D.subgroupOf (Subgroup.centralizer (P : Set G))) →
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis β =
          centralCharacterResidueHom basis ideal χ →
      coefficientBlockDefect basis ideal p χ D) ∧
    (∀ χ : basis.index, coefficientBlockDefect basis ideal p χ D →
      ∃ β : localBasis.index,
        coefficientBlockDefect localBasis ideal p β
          (D.subgroupOf (Subgroup.centralizer (P : Set G))) ∧
        brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis β =
            centralCharacterResidueHom basis ideal χ) ∧
    (∀ β₁ β₂ : localBasis.index,
      coefficientBlockDefect localBasis ideal p β₁
        (D.subgroupOf (Subgroup.centralizer (P : Set G))) →
      coefficientBlockDefect localBasis ideal p β₂
        (D.subgroupOf (Subgroup.centralizer (P : Set G))) →
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis β₁ =
        brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis β₂ →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₁ β₂) :=
  intermediate_normalizer_controlled_defect_correspondence basis ideal p P hP
    (Subgroup.centralizer (P : Set G)) le_rfl (Subgroup.centralizer_le_normalizer _) D hD hPD hDC
    hND localBasis

end CFSG.Semidihedral.Principal
