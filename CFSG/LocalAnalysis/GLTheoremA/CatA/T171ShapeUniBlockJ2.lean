module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockJ
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniPsu
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockComm
import CFSG.RankThree.PartOne.KF.UnitaryDiag
import CFSG.Models.PGLSimple
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryField
import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LieType.SemisimpleCentralizers.HeldLang CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.Burgoyne.U CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCPrimary
open Polynomial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open scoped commutatorElement MatrixGroups

theorem isSimpleGroup_statedSU_good {E : Type} [Field E] [Finite E] {k m : ℕ}
    (hE : UnitaryFieldData 2 k E) (hm2 : 2 ≤ m)
    (hbad : ((m, 2 ^ k) : ℕ × ℕ) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))) :
    IsSimpleGroup (LargeEvenProj (StatedSU m (2 ^ k) E)) := by
  rcases lt_or_ge m 3 with h3 | h3
  · have hm : m = 2 := by omega
    subst hm
    have hk2 : 2 ≤ k := by
      by_contra hk
      have hk1 : k = 1 := by
        have := hE.one_le
        omega
      exact hbad (by simp [hk1])
    exact isSimpleGroup_statedProj_statedSU_two hE hk2
  · refine CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU E 2 k ?_ m h3 ?_
    · calc Nat.card E = 2 ^ (2 * k) := hE.card
        _ = 2 ^ (k * 2) := by rw [Nat.mul_comm]
        _ = (2 ^ k) ^ 2 := by rw [pow_mul]
    · intro h
      exact hbad (by rw [h]; simp)

@[expose] def UniJSelfDualModel {Ω : Type} [Group Ω] (p : ℕ) (J : Subgroup Ω) (y : Ω)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) : Prop :=
  ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (k : ℕ)
    (hE : UnitaryFieldData 2 k E) (B₁ : GL (Fin m) E)
    (hB₁ : B₁ ∈ primeFormUnitary hE (idGram E m))
    (hconj : ∀ P : ↥(StatedSU m (2 ^ k) E),
      B₁ * (P : GL (Fin m) E) * B₁⁻¹ ∈ StatedSU m (2 ^ k) E)
    (e₀ : PSimple p J ≃* LargeEvenProj (StatedSU m (2 ^ k) E)),
    2 ≤ m ∧ (m = 2 → 2 ≤ k) ∧ (m = 3 → 2 ≤ k) ∧
    ∀ P : ↥(StatedSU m (2 ^ k) E),
      MulAut.congr e₀ (MI.indAut p J y hJy)
          (LargeEvenProjMk (StatedSU m (2 ^ k) E) P) =
        LargeEvenProjMk (StatedSU m (2 ^ k) E)
          ⟨B₁ * (P : GL (Fin m) E) * B₁⁻¹, hconj P⟩

@[expose] def UniJPairedModel {Ω : Type} [Group Ω] (p : ℕ) (J : Subgroup Ω) (y : Ω)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) : Prop :=
  ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (k : ℕ)
    (hk : Nat.card E = 2 ^ k) (B₁ : GL (Fin m) E)
    (e₀ : PSimple p J ≃* LargeEvenProj (StatedSL m E)),
    2 ≤ m ∧ 2 ≤ k ∧
    ∀ P : ↥(StatedSL m E),
      MulAut.congr e₀ (MI.indAut p J y hJy)
          (LargeEvenProjMk (StatedSL m E) P) =
        LargeEvenProjMk (StatedSL m E)
          ⟨B₁ * (P : GL (Fin m) E) * B₁⁻¹,
            (inferInstance : (StatedSL m E).Normal).conj_mem P P.2 B₁⟩

theorem uniJ_equiv_comm_selfDual {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJS : J ≤ S) (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {N n : ℕ} {K : Type} [Field K] [Finite K] (hfield : UnitaryFieldData 2 n K)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (unitarySU 2 n K N))
    (A B : GL (Fin N) K) (hB : B ∈ primeFormUnitary hfield (idGram K N))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)))
    (hindy : LargeEvenInduces θ (conjRel y)
      (TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩))
    (hcomm : Commute A B)
    (H : UnitaryPrimaryData hfield.bar (idForm hfield N)
      (Matrix.GeneralLinearGroup.toLin A))
    (a : {a : primaryFactors ((Matrix.GeneralLinearGroup.toLin A :
        LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) //
      IsGoodBlock hfield (Matrix.GeneralLinearGroup.toLin A) a})
    (hz : ∀ z : StatedProj (StatedSU N (2 ^ n) K),
      z ∈ (J.subgroupOf S).map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))) ↔
      ∃ g : GL (Fin N) K, Matrix.GeneralLinearGroup.toLin g ∈
        specialBlock (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ∧
        ∃ hg : g ∈ StatedSU N (2 ^ n) K,
          LargeEvenProjMk (StatedSU N (2 ^ n) K) ⟨g, hg⟩ = z)
    (hself : dualPoly hfield.bar (a.1 : K[X]) = a.1) :
    UniJSelfDualModel p J y hJy := by
  classical
  have hn : 1 ≤ n := hfield.one_le
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set m := primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin A :
    LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) (a.1 : K[X])
    with hm
  have hm2 : 2 ≤ m := by rw [hm]; exact a.2.1
  have htot : m = primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K))
      (a.1 : K[X]) := hm
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  haveI : Finite (AdjoinRoot (a.1 : K[X])) := Module.finite_of_finite K
  obtain ⟨hE, Hf, e, ι, hHf, hHfl, he, hιinj, hSB, hscalK, hconjι, hiso⟩ :=
    l154_selfDual_model_block H a.1 hself htot
  let Hm : Subgroup (GL (Fin m) (AdjoinRoot (a.1 : K[X]))) :=
    StatedSU m (2 ^ (n * (a.1 : K[X]).natDegree)) (AdjoinRoot (a.1 : K[X]))
  have hξ : Matrix.GeneralLinearGroup.toLin B ∈
      unitaryCentralizer (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) := by
    rw [mem_unitaryCentralizer]
    refine ⟨(CFSG.RankThree.PartOne.KCUnitaryModel.toLin_mem_sesqUnitaryGroup_iff B).2 hB, ?_⟩
    rw [Commute, SemiconjBy]
    have h1 : Matrix.GeneralLinearGroup.toLin B * Matrix.GeneralLinearGroup.toLin A =
        Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin B := by
      calc Matrix.GeneralLinearGroup.toLin B * Matrix.GeneralLinearGroup.toLin A
          = Matrix.GeneralLinearGroup.toLin (B * A) := (map_mul _ B A).symm
        _ = Matrix.GeneralLinearGroup.toLin (A * B) := by
          rw [show B * A = A * B from hcomm.eq.symm]
        _ = Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin B :=
          map_mul _ A B
    exact congrArg Units.val h1
  let f : ↥Hm →* GL (Fin N) K :=
    (Matrix.GeneralLinearGroup.toLin.symm :
      LinearMap.GeneralLinearGroup K (Fin N → K) ≃* GL (Fin N) K).toMonoidHom.comp
      (ι.comp Hm.subtype)
  have hfmem : ∀ P : ↥Hm, f P ∈ unitarySU 2 n K N := by
    intro P
    have hmem : ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) ∈
        specialBlock (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) :=
      hSB ▸ Subgroup.mem_map_of_mem ι P.2
    have hsu := specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hmem
    rw [unitarySU_eq_gramSU hfield]
    refine (toLin_mem_sesqSpecialUnitaryGroup_iff hfield (idGram K N) _).1 ?_
    show Matrix.GeneralLinearGroup.toLin (f P) ∈
      sesqSpecialUnitaryGroup (gramForm hfield (idGram K N))
    rw [show Matrix.GeneralLinearGroup.toLin (f P) =
        ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) from
      MulEquiv.apply_symm_apply _ _]
    exact hsu
  let ιm : ↥Hm →* ↥(unitarySU 2 n K N) := f.codRestrict _ hfmem
  let B₁ : GL (Fin m) (AdjoinRoot (a.1 : K[X])) :=
    (Matrix.GeneralLinearGroup.toLin' e).symm
      (blockRestrict (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ⟨_, hξ.2⟩)
  have hB₁mem : B₁ ∈ primeFormUnitary hE (idGram (AdjoinRoot (a.1 : K[X])) m) :=
    hiso (Matrix.GeneralLinearGroup.toLin B) hξ
  have hsimple : IsSimpleGroup (LargeEvenProj Hm) :=
    isSimpleGroup_statedSU_good hE hm2 (a.2.2 hself)
  have hmemB : ∀ P : ↥Hm, B * (ιm P : GL (Fin N) K) * B⁻¹ ∈ unitarySU 2 n K N :=
    fun P => CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU hfield hB (ιm P).2
  have hψ : ∀ P : ↥Hm,
      TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩
          (LargeEvenProjMk (unitarySU 2 n K N) (ιm P)) =
        LargeEvenProjMk (unitarySU 2 n K N)
          ⟨B * (ιm P : GL (Fin N) K) * B⁻¹, hmemB P⟩ :=
    fun P => rfl
  have hconj_mem : ∀ P : ↥Hm,
      B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹ ∈ Hm := by
    intro P
    have hmem : ι (B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹) ∈ Hm.map ι := by
      rw [← hSB, hconjι (Matrix.GeneralLinearGroup.toLin B) hξ
        (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))]
      exact conj_mem_specialBlock hξ (hSB ▸ Subgroup.mem_map_of_mem ι P.2)
    obtain ⟨Q, hQ, hQeq⟩ := Subgroup.mem_map.mp hmem
    rwa [hιinj hQeq] at hQ
  have hconj : ∀ P : ↥Hm,
      ((ιm ⟨B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹, hconj_mem P⟩ :
        ↥(unitarySU 2 n K N)) : GL (Fin N) K) = B * (ιm P : GL (Fin N) K) * B⁻¹ := by
    intro P
    change Matrix.GeneralLinearGroup.toLin.symm
        (ι (B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹)) =
      B * Matrix.GeneralLinearGroup.toLin.symm
        (ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))) * B⁻¹
    rw [hconjι (Matrix.GeneralLinearGroup.toLin B) hξ
      (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hscal : ∀ P : ↥Hm, (∃ z : Kˣ,
      (ιm P : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) z) →
      ∃ w : (AdjoinRoot (a.1 : K[X]))ˣ,
        (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) =
          Matrix.GeneralLinearGroup.scalar (Fin m) w := by
    intro P ⟨z, hz'⟩
    have hzT : Matrix.GeneralLinearGroup.toLin (ιm P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.scalar (Fin N) z) := by rw [hz']
    have hιP : ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) =
        Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.scalar (Fin N) z) := by
      rw [← hzT]
      exact (MulEquiv.apply_symm_apply _ _).symm
    have h1 : ((ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) = (z : K) • 1 := by
      rw [hιP]
      exact l154_toLin_scalar z
    have hz0 : algebraMap K (AdjoinRoot (a.1 : K[X])) (z : K) ≠ 0 := by
      intro h0
      refine z.ne_zero ((algebraMap K (AdjoinRoot (a.1 : K[X]))).injective ?_)
      simpa using h0
    exact l154_scalar_of_matrix_eq (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))
      (algebraMap K (AdjoinRoot (a.1 : K[X])) (z : K)) hz0
      (hscalK (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) (z : K) h1)
  have hJPeq : (J.subgroupOf S).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))) =
      ιm.range.map (LargeEvenProjMk (unitarySU 2 n K N)) := by
    ext z
    rw [hz z]
    constructor
    · rintro ⟨g, hgSB, hg, hπ⟩
      have hg' : Matrix.GeneralLinearGroup.toLin g ∈
          (StatedSU m (2 ^ (n * (a.1 : K[X]).natDegree))
            (AdjoinRoot (a.1 : K[X]))).map ι := hSB ▸ hgSB
      obtain ⟨P, hP, hPi⟩ := Subgroup.mem_map.mp hg'
      refine Subgroup.mem_map.mpr ⟨ιm ⟨P, hP⟩, MonoidHom.mem_range.mpr ⟨⟨P, hP⟩, rfl⟩, ?_⟩
      rw [← hπ]
      congr 1
      apply Subtype.ext
      show Matrix.GeneralLinearGroup.toLin.symm (ι P) = g
      rw [hPi, MulEquiv.symm_apply_apply]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨P, rfl⟩ := MonoidHom.mem_range.mp hw
      refine ⟨(ιm P : GL (Fin N) K), ?_, (ιm P).2, rfl⟩
      show Matrix.GeneralLinearGroup.toLin ((ιm P : GL (Fin N) K)) ∈
        specialBlock (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])
      rw [show Matrix.GeneralLinearGroup.toLin (ιm P : GL (Fin N) K) =
          ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) from
        MulEquiv.apply_symm_apply _ _]
      exact hSB ▸ Subgroup.mem_map_of_mem ι P.2
  obtain ⟨e₀, he₀⟩ := uniJ_equiv_comm_core hp hJ hJS hJy θ
    (TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩) hindy Hm ιm B B₁ hsimple hmemB hψ
    hconj_mem hconj hJPeq hscal
  refine ⟨m, AdjoinRoot (a.1 : K[X]), inferInstance, inferInstance,
    n * (a.1 : K[X]).natDegree, hE, B₁, hB₁mem, hconj_mem, e₀, hm2, ?_, ?_, he₀⟩
  · intro hm2'
    by_contra hk
    have hk1 : n * (a.1 : K[X]).natDegree = 1 := by
      have h1 : 1 ≤ n * (a.1 : K[X]).natDegree :=
        Nat.mul_pos hfield.one_le (Irreducible.natDegree_pos Fact.out)
      omega
    have hq2 : 2 ^ (n * (a.1 : K[X]).natDegree) = 2 := by rw [hk1]; norm_num
    exact a.2.2 hself (by rw [← hm, hm2']; simp [hq2])
  · intro hm3'
    by_contra hk
    have hk1 : n * (a.1 : K[X]).natDegree = 1 := by
      have h1 : 1 ≤ n * (a.1 : K[X]).natDegree :=
        Nat.mul_pos hfield.one_le (Irreducible.natDegree_pos Fact.out)
      omega
    have hq2 : 2 ^ (n * (a.1 : K[X]).natDegree) = 2 := by rw [hk1]; norm_num
    exact a.2.2 hself (by rw [← hm, hm3']; simp [hq2])

theorem uniJ_equiv_comm_paired {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJS : J ≤ S) (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {N n : ℕ} {K : Type} [Field K] [Finite K] (hfield : UnitaryFieldData 2 n K)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (unitarySU 2 n K N))
    (A B : GL (Fin N) K) (hB : B ∈ primeFormUnitary hfield (idGram K N))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)))
    (hindy : LargeEvenInduces θ (conjRel y)
      (TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩))
    (hcomm : Commute A B)
    (H : UnitaryPrimaryData hfield.bar (idForm hfield N)
      (Matrix.GeneralLinearGroup.toLin A))
    (a : {a : primaryFactors ((Matrix.GeneralLinearGroup.toLin A :
        LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) //
      IsGoodBlock hfield (Matrix.GeneralLinearGroup.toLin A) a})
    (hz : ∀ z : StatedProj (StatedSU N (2 ^ n) K),
      z ∈ (J.subgroupOf S).map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))) ↔
      ∃ g : GL (Fin N) K, Matrix.GeneralLinearGroup.toLin g ∈
        specialBlock (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ∧
        ∃ hg : g ∈ StatedSU N (2 ^ n) K,
          LargeEvenProjMk (StatedSU N (2 ^ n) K) ⟨g, hg⟩ = z)
    (hne : (a.1 : K[X]) ≠ dualPoly hfield.bar (a.1 : K[X])) :
    UniJPairedModel p J y hJy := by
  classical
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hfield.one_le
  set m := primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin A :
    LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) (a.1 : K[X])
    with hm
  have hm2 : 2 ≤ m := by rw [hm]; exact a.2.1
  have htot : m = primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K))
      (a.1 : K[X]) := hm
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  haveI : Finite (AdjoinRoot (a.1 : K[X])) := Module.finite_of_finite K
  obtain ⟨e, ι, hιinj, hSB, hscalK, hconjι⟩ :=
    l154_paired_model_block H a.1 hne htot
  have hkpos : 1 ≤ n * (a.1 : K[X]).natDegree :=
    Nat.mul_pos hfield.one_le (Irreducible.natDegree_pos Fact.out)
  have hEcard : Nat.card (AdjoinRoot (a.1 : K[X])) =
      2 ^ (2 * (n * (a.1 : K[X]).natDegree)) :=
    CFSG.RankThree.PartOne.KCUnitary.natCard_adjoinRoot hfield
  have h4 : 4 ≤ Nat.card (AdjoinRoot (a.1 : K[X])) := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (n * (a.1 : K[X]).natDegree)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  let Hm : Subgroup (GL (Fin m) (AdjoinRoot (a.1 : K[X]))) :=
    StatedSL m (AdjoinRoot (a.1 : K[X]))
  let f : ↥Hm →* GL (Fin N) K :=
    (Matrix.GeneralLinearGroup.toLin.symm :
      LinearMap.GeneralLinearGroup K (Fin N → K) ≃* GL (Fin N) K).toMonoidHom.comp
      (ι.comp Hm.subtype)
  have hfmem : ∀ P : ↥Hm, f P ∈ unitarySU 2 n K N := by
    intro P
    have hmem : ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) ∈
        specialBlock (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) :=
      hSB ▸ Subgroup.mem_map_of_mem ι P.2
    have hsu := specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hmem
    rw [unitarySU_eq_gramSU hfield]
    refine (toLin_mem_sesqSpecialUnitaryGroup_iff hfield (idGram K N) _).1 ?_
    show Matrix.GeneralLinearGroup.toLin (f P) ∈
      sesqSpecialUnitaryGroup (gramForm hfield (idGram K N))
    rw [show Matrix.GeneralLinearGroup.toLin (f P) =
        ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) from
      MulEquiv.apply_symm_apply _ _]
    exact hsu
  let ιm : ↥Hm →* ↥(unitarySU 2 n K N) := f.codRestrict _ hfmem
  have hξ : Matrix.GeneralLinearGroup.toLin B ∈
      unitaryCentralizer (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) := by
    rw [mem_unitaryCentralizer]
    refine ⟨(CFSG.RankThree.PartOne.KCUnitaryModel.toLin_mem_sesqUnitaryGroup_iff B).2 hB, ?_⟩
    rw [Commute, SemiconjBy]
    have h1 : Matrix.GeneralLinearGroup.toLin B * Matrix.GeneralLinearGroup.toLin A =
        Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin B := by
      calc Matrix.GeneralLinearGroup.toLin B * Matrix.GeneralLinearGroup.toLin A
          = Matrix.GeneralLinearGroup.toLin (B * A) := (map_mul _ B A).symm
        _ = Matrix.GeneralLinearGroup.toLin (A * B) := by
          rw [show B * A = A * B from hcomm.eq.symm]
        _ = Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin B :=
          map_mul _ A B
    exact congrArg Units.val h1
  let B₁ : GL (Fin m) (AdjoinRoot (a.1 : K[X])) :=
    (Matrix.GeneralLinearGroup.toLin' e).symm
      (blockRestrict (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ⟨_, hξ.2⟩)
  have hsimple : IsSimpleGroup (LargeEvenProj Hm) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (AdjoinRoot (a.1 : K[X])) hm2
      (Or.inr (by omega)) (Or.inr (by omega))
  have hmemB : ∀ P : ↥Hm, B * (ιm P : GL (Fin N) K) * B⁻¹ ∈ unitarySU 2 n K N :=
    fun P => CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU hfield hB (ιm P).2
  have hψ : ∀ P : ↥Hm,
      TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩
          (LargeEvenProjMk (unitarySU 2 n K N) (ιm P)) =
        LargeEvenProjMk (unitarySU 2 n K N)
          ⟨B * (ιm P : GL (Fin N) K) * B⁻¹, hmemB P⟩ :=
    fun P => rfl
  have hconj_mem : ∀ P : ↥Hm,
      B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹ ∈ Hm :=
    fun P => (inferInstance : Hm.Normal).conj_mem P P.2 B₁
  have hconj : ∀ P : ↥Hm,
      ((ιm ⟨B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹, hconj_mem P⟩ :
        ↥(unitarySU 2 n K N)) : GL (Fin N) K) = B * (ιm P : GL (Fin N) K) * B⁻¹ := by
    intro P
    change Matrix.GeneralLinearGroup.toLin.symm
        (ι (B₁ * (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) * B₁⁻¹)) =
      B * Matrix.GeneralLinearGroup.toLin.symm
        (ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))) * B⁻¹
    rw [hconjι (Matrix.GeneralLinearGroup.toLin B) hξ (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hscal : ∀ P : ↥Hm, (∃ z : Kˣ,
      (ιm P : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) z) →
      ∃ w : (AdjoinRoot (a.1 : K[X]))ˣ,
        (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) =
          Matrix.GeneralLinearGroup.scalar (Fin m) w := by
    intro P ⟨z, hz'⟩
    have hzT : Matrix.GeneralLinearGroup.toLin (ιm P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.scalar (Fin N) z) := by rw [hz']
    have hιP : ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) =
        Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.scalar (Fin N) z) := by
      rw [← hzT]
      exact (MulEquiv.apply_symm_apply _ _).symm
    have h1 : ((ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) = (z : K) • 1 := by
      rw [hιP]
      exact l154_toLin_scalar z
    have hz0 : algebraMap K (AdjoinRoot (a.1 : K[X])) (z : K) ≠ 0 := by
      intro h0
      refine z.ne_zero ((algebraMap K (AdjoinRoot (a.1 : K[X]))).injective ?_)
      simpa using h0
    exact l154_scalar_of_matrix_eq (P : GL (Fin m) (AdjoinRoot (a.1 : K[X])))
      (algebraMap K (AdjoinRoot (a.1 : K[X])) (z : K)) hz0
      (hscalK (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) (z : K) h1)
  have hJPeq : (J.subgroupOf S).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))) =
      ιm.range.map (LargeEvenProjMk (unitarySU 2 n K N)) := by
    ext z
    rw [hz z]
    constructor
    · rintro ⟨g, hgSB, hg, hπ⟩
      have hg' : Matrix.GeneralLinearGroup.toLin g ∈
          (StatedSL m (AdjoinRoot (a.1 : K[X]))).map ι := hSB ▸ hgSB
      obtain ⟨P, hP, hPi⟩ := Subgroup.mem_map.mp hg'
      refine Subgroup.mem_map.mpr ⟨ιm ⟨P, hP⟩, MonoidHom.mem_range.mpr ⟨⟨P, hP⟩, rfl⟩, ?_⟩
      rw [← hπ]
      congr 1
      apply Subtype.ext
      show Matrix.GeneralLinearGroup.toLin.symm (ι P) = g
      rw [hPi, MulEquiv.symm_apply_apply]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨P, rfl⟩ := MonoidHom.mem_range.mp hw
      refine ⟨(ιm P : GL (Fin N) K), ?_, (ιm P).2, rfl⟩
      show Matrix.GeneralLinearGroup.toLin ((ιm P : GL (Fin N) K)) ∈
        specialBlock (idForm hfield N) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])
      rw [show Matrix.GeneralLinearGroup.toLin (ιm P : GL (Fin N) K) =
          ι (P : GL (Fin m) (AdjoinRoot (a.1 : K[X]))) from
        MulEquiv.apply_symm_apply _ _]
      exact hSB ▸ Subgroup.mem_map_of_mem ι P.2
  obtain ⟨e₀, he₀⟩ := uniJ_equiv_comm_core hp hJ hJS hJy θ
    (TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩) hindy Hm ιm B B₁ hsimple hmemB hψ
    hconj_mem hconj hJPeq hscal
  exact ⟨m, AdjoinRoot (a.1 : K[X]), inferInstance, inferInstance,
    2 * (n * (a.1 : K[X]).natDegree), hEcard, B₁, e₀, hm2, by omega, he₀⟩

theorem uniJ_equiv_comm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hyN : y ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {N n : ℕ} {K : Type} [Field K] [Finite K] (hfield : UnitaryFieldData 2 n K)
    (hN : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2))
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (unitarySU 2 n K N))
    (A B : GL (Fin N) K) (hA : A ∈ primeFormUnitary hfield (idGram K N))
    (hB : B ∈ primeFormUnitary hfield (idGram K N))
    (hAN : A ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)))
    (hAc : ∃ c : Kˣ, A ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hcomm : Commute A B)
    (hindx : LargeEvenInduces θ (conjRel x)
      (TableB.projConj (unitarySU 2 n K N) ⟨A, hAN⟩))
    (hindy : LargeEvenInduces θ (conjRel y)
      (TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩)) :
    UniJSelfDualModel p J y hJy ∨ UniJPairedModel p J y hJy := by
  classical
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hn : 1 ≤ n := hfield.one_le
  let ρS : ↥S →* LargeEvenProj (unitarySU 2 n K N) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  have hker : ρS.ker ≤ Subgroup.center ↥S := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h1 : QuotientGroup.mk' (Subgroup.center ↥S) s = 1 := by
      apply θ.injective
      rw [map_one]
      exact hs
    exact (QuotientGroup.eq_one_iff s).1 h1
  have hsurj : Function.Surjective ρS := by
    intro r
    obtain ⟨a, ha⟩ := θ.surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) a
    exact ⟨s, ha⟩
  let α : MulAut ↥S := S.normalizerMonoidHom ⟨x⁻¹, Subgroup.inv_mem _ hxN⟩
  have hα : ∀ s : ↥S, ((α s : ↥S) : Ω) = x⁻¹ * (s : Ω) * x := by
    intro s
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hfix : fixSubgroup α = (S ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S := by
    ext s
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hs
      have h2 : ((α s : ↥S) : Ω) = (s : Ω) := congrArg Subtype.val hs
      rw [hα] at h2
      refine ⟨s.2, ?_⟩
      calc (s : Ω) * x = x * (x⁻¹ * (s : Ω) * x) := by group
        _ = x * (s : Ω) := by rw [h2]
    · rintro ⟨-, hs⟩
      apply Subtype.ext
      rw [hα]
      calc x⁻¹ * (s : Ω) * x = x⁻¹ * ((s : Ω) * x) := by group
        _ = x⁻¹ * (x * (s : Ω)) := by rw [hs]
        _ = (s : Ω) := by group
  let u : MulAut (StatedProj (StatedSU N (2 ^ n) K)) :=
    TableB.projConj (unitarySU 2 n K N) ⟨A, hAN⟩
  have hαβ : ∀ s : ↥S, ρS (α s) = u (ρS s) := by
    intro s
    exact (hindx s (α s) (hα s)).symm
  have hJsub : GLAPComponent p ((S ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S)
      (J.subgroupOf S) := by
    refine (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff (p := p) hp
      (Subgroup.subtype_injective S)).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le hJS]
  let JP : Subgroup (StatedProj (StatedSU N (2 ^ n) K)) :=
    (J.subgroupOf S).map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S)))
  have hJPraw : GLAPComponent p (fixSubgroup u) ((J.subgroupOf S).map ρS) :=
    glaPComponent_map_fixSubgroup ρS hker α u hαβ hsurj hp (hfix ▸ hJsub)
  have hJPc : GLAPComponent p (fixSubgroup u) JP := hJPraw
  have hu : ∀ g g' : ↥(StatedSU N (2 ^ n) K),
      (g' : GL (Fin N) K) = A * (g : GL (Fin N) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU N (2 ^ n) K) g) =
        LargeEvenProjMk (StatedSU N (2 ^ n) K) g' := by
    intro g g' hgg
    rw [show LargeEvenProjMk (StatedSU N (2 ^ n) K) g =
        (g : LargeEvenProj (StatedSU N (2 ^ n) K)) from rfl,
      show LargeEvenProjMk (StatedSU N (2 ^ n) K) g' =
        (g' : LargeEvenProj (StatedSU N (2 ^ n) K)) from rfl,
      TableB.projConj_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hgg]
  obtain ⟨c, hc⟩ := hAc
  obtain ⟨H, a, hz⟩ := l154_uni_good_block hn hN hfield hp hp2 A hA hc u hu JP hJPc
  by_cases hself : dualPoly hfield.bar (a.1 : K[X]) = a.1
  · exact Or.inl (uniJ_equiv_comm_selfDual hp hJ hJS hJy hfield θ A B hB hBN hindy hcomm
      H a hz hself)
  · exact Or.inr (uniJ_equiv_comm_paired hp hJ hJS hJy hfield θ A B hB hBN hindy hcomm
      H a hz (fun h => hself h.symm))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
