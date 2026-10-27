module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinBlock

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Open
  CFSG.LocalAnalysis.GLTheoremB

section SelfDualFactor

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem exists_selfDual_factor_of_good (H : UnitaryPrimaryData hK.bar B x)
    {a : primaryFactors (x : Module.End K V)} (hself : dualPoly hK.bar (a : K[X]) = a)
    (ha : IsGoodBlock hK x a) :
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F),
        Fintype.card F = ℓ ^ (f * (a : K[X]).natDegree) ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (3 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) ∧
        ∃ (E : Type) (_ : Field E) (_ : Fintype E),
          Fintype.card E = (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 ∧
          Nonempty (↥(specialBlock B x (a : K[X])) ≃*
            ↥(StatedSU (primaryMultiplicity (x : Module.End K V) (a : K[X]))
              (ℓ ^ (f * (a : K[X]).natDegree)) E))) := by
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
    nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
  have hgood : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
  · have hm2 : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
    have hV : Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := hm2
    obtain ⟨e2⟩ :=
      CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
    haveI : Finite hE.fixedField := inferInstance
    letI : Fintype hE.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card hE.fixedField = ℓ ^ (f * (a : K[X]).natDegree) := by
      rw [← Nat.card_eq_fintype_card, hE.card_fixedField]
    exact Or.inl ⟨hm2, hE.fixedField, inferInstance, inferInstance, hcardF, ⟨e.trans e2⟩⟩
  · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
    obtain ⟨e2⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))))
        (Fin (Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
      (fun i j => by rw [hb i j, Matrix.one_apply])
    have hcardE : Fintype.card (AdjoinRoot (a : K[X])) =
        (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hE.card_eq_sq]
    refine Or.inr ⟨hm, AdjoinRoot (a : K[X]), inferInstance, inferInstance, hcardE, ?_⟩
    exact ⟨(e.trans e2).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)⟩

end SelfDualFactor

section FieldType

variable {ℓ f n : ℕ} {K : Type} [Field K]

private theorem ne_zero_of_isComponentOf_fixSubgroup (h : UnitaryFieldData ℓ f K)
    (A : primeFormUnitary h (idGram K n)) {T : Subgroup (primeFormP h (idGram K n))}
    (hT : IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A))) : n ≠ 0 := by
  intro hn
  subst hn
  haveI : Subsingleton (Matrix (Fin 0) (Fin 0) K) :=
    ⟨fun _ _ => Matrix.ext fun i _ => Fin.elim0 i⟩
  haveI : Subsingleton (GL (Fin 0) K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  haveI : Subsingleton ↥(gramSU h (idGram K 0)) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : Subsingleton (primeFormP h (idGram K 0)) := inferInstance
  haveI : Subsingleton ↥(fixSubgroup (primeFormConjHom h (idGram K 0) A)) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : Subsingleton ↥T := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hcenter : Subgroup.center ↥T = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subsingleton.elim _ _
  haveI : Subsingleton (↥T ⧸ Subgroup.center ↥T) :=
    QuotientGroup.subsingleton_iff.mpr hcenter
  haveI : IsSimpleGroup (↥T ⧸ Subgroup.center ↥T) := hT.2.2.2
  haveI hnt : Nontrivial (↥T ⧸ Subgroup.center ↥T) := hT.2.2.2.toNontrivial
  exact not_subsingleton_iff_nontrivial.2 hnt inferInstance

theorem unitary_fieldType_component {p : ℕ} (hp : p.Prime) {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hpℓ : p ≠ ℓ) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {T : Subgroup (primeFormP h (idGram K n))}
    (hT : IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A))) :
    p ∣ n ∧ 2 ≤ n / p ∧
      (∀ T' : Subgroup (primeFormP h (idGram K n)),
        IsComponentOf T' (fixSubgroup (primeFormConjHom h (idGram K n) A)) → T' = T) ∧
      ((n / p = 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
          Fintype.card F = ℓ ^ (f * p) ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (3 ≤ n / p ∧ ∃ (E : Type) (_ : Field E) (_ : Fintype E),
          Fintype.card E = (ℓ ^ (f * p)) ^ 2 ∧
          ∃ g : ↥(StatedSU (n / p) (ℓ ^ (f * p)) E) →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center ↥(StatedSU (n / p) (ℓ ^ (f * p)) E))) := by
  classical
  haveI := h.finite
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) with hx
  have hn0 : n ≠ 0 := ne_zero_of_isComponentOf_fixSubgroup h A hT
  have hmin :=
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.minpoly_linEnd_of_pow_scalar_irreducible
      (K := K) hp c hA hc hn0
  have hH : UnitaryPrimaryData h.bar (idForm h n) x := primaryData_toLin' h A.2 hp hpℓ hA
  have hfac : primaryFactors (x : Module.End K (Fin n → K)) = {X ^ p - C (c : K)} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · have h := CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.minpoly_mem_primaryFactors
        (y := (A : GL (Fin n) K)) (K := K) hmin.2
      rwa [hmin.1] at h
    · intro y hy
      have h := CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.eq_minpoly_of_mem_primaryFactors
        (y := (A : GL (Fin n) K)) (K := K) hmin.2 hy
      rwa [hmin.1] at h
  have hdeg : (X ^ p - C (c : K) : K[X]).natDegree = p := natDegree_X_pow_sub_C
  obtain ⟨a, haT⟩ := exists_good_primaryFactor_of_component hq A hx hH T hT
  have haf : (a.1 : K[X]) = X ^ p - C (c : K) := by
    have hmem : (a.1 : K[X]) ∈ ({X ^ p - C (c : K)} : Finset K[X]) := by
      rw [← hfac]
      exact a.1.2
    exact Finset.mem_singleton.mp hmem
  have hda : (a.1 : K[X]).natDegree = p := by rw [haf, hdeg]
  have hself : dualPoly h.bar (a.1 : K[X]) = a.1 := by
    have hmem : dualPoly h.bar (a.1 : K[X]) ∈ ({X ^ p - C (c : K)} : Finset K[X]) := by
      rw [← hfac]
      exact dualPoly_mem_primaryFactors hH a.1.2
    rw [Finset.mem_singleton.mp hmem, ← haf]
  have hcount : p * primaryMultiplicity (x : Module.End K (Fin n → K)) (a.1 : K[X]) = n := by
    have h := CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.finrank_eq_natDegree_mul_mult
      (y := (A : GL (Fin n) K)) (K := K) hmin.2 a.1
    rw [hmin.1, hdeg] at h
    exact h.symm
  have hdiv : n / p = primaryMultiplicity (x : Module.End K (Fin n → K)) (a.1 : K[X]) := by
    conv_lhs => rw [← hcount]
    rw [Nat.mul_comm p, Nat.mul_div_left _ hp.pos]
  have hdvd : p ∣ n := ⟨_, hcount.symm⟩
  refine ⟨hdvd, ?_, ?_, ?_⟩
  · rw [hdiv]
    exact a.2.1
  ·
    intro T' hT'
    obtain ⟨a', ha'T'⟩ := exists_good_primaryFactor_of_component hq A hx hH T' hT'
    have ha' : (a'.1 : K[X]) = (a.1 : K[X]) := by
      have hmem : (a'.1 : K[X]) ∈ ({X ^ p - C (c : K)} : Finset K[X]) := by
        rw [← hfac]
        exact a'.1.2
      rw [Finset.mem_singleton.mp hmem, haf]
    rw [ha'T', haT, ha']
  ·
    obtain ⟨g, hg, hker⟩ := exists_surjective_specialBlock hq hH a T haT
    rcases exists_selfDual_factor_of_good hH hself a.2 with
        ⟨hm2, F, hF, hFt, hcardF, ⟨eSL⟩⟩ | ⟨hm3, E, hE, hEt, hcardE, ⟨eSU⟩⟩
    · refine Or.inl ⟨?_, F, hF, hFt, ?_, ?_⟩
      · rw [hdiv]; exact hm2
      · rw [hcardF, hda]
      · letI : Field F := hF
        letI : Fintype F := hFt
        refine ⟨g.comp eSL.symm.toMonoidHom, hg.comp eSL.symm.surjective, ?_⟩
        rw [← MonoidHom.comap_ker]
        exact (Subgroup.comap_mono hker).trans
          (Subgroup.comap_center_le_center (f := eSL.symm.toMonoidHom) eSL.symm.injective)
    · refine Or.inr ⟨?_, E, hE, hEt, ?_, ?_⟩
      · rw [hdiv]; exact hm3
      · rw [hcardE, hda]
      · letI : Field E := hE
        letI : Fintype E := hEt
        have hgoal : ∃ g' : ↥(StatedSU (n / p) (ℓ ^ (f * p)) E) →* ↥T,
            Function.Surjective g' ∧
              g'.ker ≤ Subgroup.center ↥(StatedSU (n / p) (ℓ ^ (f * p)) E) := by
          rw [hdiv, ← hda]
          exact ⟨g.comp eSU.symm.toMonoidHom, hg.comp eSU.symm.surjective, by
            rw [← MonoidHom.comap_ker]
            exact (Subgroup.comap_mono hker).trans
              (Subgroup.comap_center_le_center (f := eSU.symm.toMonoidHom) eSU.symm.injective)⟩
        exact hgoal

end FieldType

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

