module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniBlock
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
public import CFSG.LieType.SemisimpleCentralizers.HeldLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniLine
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open Polynomial Module CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ComponentClassification.Burgoyne.U
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
  (toLinSU toLinSU_apply toLinSU_injective exists_good_block_of_component primaryData_toLin'
    mem_range_toLinSU nonempty_specialBlock_mulEquiv_sesqSU)
open CFSG.LieType.SemisimpleCentralizers.HeldLang (scalar_mul_comm)

section Transport

variable {n d : ℕ} {K : Type} [Field K]

theorem l154_JP_iff (hd : 1 ≤ d) (h : UnitaryFieldData 2 n K)
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K)))
    (SB : Subgroup (LinearMap.GeneralLinearGroup K (Fin d → K))) (M₀ : Subgroup (GL (Fin d) K))
    (hM₀ : ∀ g : GL (Fin d) K, g ∈ M₀ ↔ Matrix.GeneralLinearGroup.toLin g ∈ SB)
    (hT : JP.map (uTransport h hd).toMonoidHom =
      ((SB.comap (toLinSU h d)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d)))) :
    ∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔
      ∃ g ∈ M₀, ∃ hg : g ∈ StatedSU d (2 ^ n) K,
        LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨g, hg⟩ = z := by
  intro z
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : (QuotientGroup.mk s ∈ JP) ↔
      uTransport h hd (QuotientGroup.mk s) ∈ JP.map (uTransport h hd).toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hSU : StatedSU d (2 ^ n) K = gramSU h (idGram K d) := statedSU_eq_gramSU h
  have hmk' : ∀ t : ↥(StatedSU d (2 ^ n) K), uTransport h hd (QuotientGroup.mk t) =
      (QuotientGroup.mk ((MulEquiv.subgroupCongr hSU) t) : primeFormP h (idGram K d)) :=
    fun t => uTransport_mk h hd t
  rw [h1, hT]
  constructor
  · intro hz
    obtain ⟨g, hg, hgq⟩ := Subgroup.mem_map.1 hz
    have hgSU : (g : GL (Fin d) K) ∈ StatedSU d (2 ^ n) K := by rw [hSU]; exact g.2
    refine ⟨g, (hM₀ _).2 (Subgroup.mem_comap.1 hg), hgSU, ?_⟩
    apply (uTransport h hd).injective
    have e1 : uTransport h hd (QuotientGroup.mk ⟨(g : GL (Fin d) K), hgSU⟩) =
        (QuotientGroup.mk g : primeFormP h (idGram K d)) := hmk' ⟨(g : GL (Fin d) K), hgSU⟩
    exact e1.trans hgq
  · rintro ⟨g, hgM, hg, hgs⟩
    refine Subgroup.mem_map.2 ⟨(MulEquiv.subgroupCongr hSU) ⟨g, hg⟩, ?_, ?_⟩
    · rw [Subgroup.mem_comap, toLinSU_apply]
      exact (hM₀ g).1 hgM
    · have := congrArg (uTransport h hd) hgs
      exact (hmk' ⟨g, hg⟩).symm.trans this

end Transport

section Setup

variable {n d : ℕ} {K : Type} [Field K]

theorem l154_uni_good_block (hn : 1 ≤ n) (hd : 3 ≤ d) (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (A : GL (Fin d) K) (hA : A ∈ primeFormUnitary h (idGram K d)) {c : Kˣ}
    (hAc : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (u : MulAut (StatedProj (StatedSU d (2 ^ n) K)))
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K))) (hJP : GLAPComponent p (fixSubgroup u) JP) :
    ∃ (H : UnitaryPrimaryData h.bar (idForm h d) (Matrix.GeneralLinearGroup.toLin A))
      (a : {a : primaryFactors ((Matrix.GeneralLinearGroup.toLin A :
          LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) //
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin A) a}),
      ∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔
        ∃ g : GL (Fin d) K, Matrix.GeneralLinearGroup.toLin g ∈
          specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ∧
          ∃ hg : g ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨g, hg⟩ = z := by
  classical
  haveI := h.finite
  have hd1 : 1 ≤ d := by omega
  have hq : 2 ≤ 2 ^ n := by
    have := Nat.one_lt_pow (by omega : n ≠ 0) Nat.one_lt_two
    omega
  set A' : primeFormUnitary h (idGram K d) := ⟨A, hA⟩ with hA'
  have hu' : u = uConjAut h hd1 A' := by
    ext r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective r
    have h1 := hu g ⟨A * (g : GL (Fin d) K) * A⁻¹, uConjSU_mem h A' g⟩ rfl
    exact h1.trans (uConjAut_proj h hd1 A' g).symm
  have hcompat : ∀ r : StatedProj (StatedSU d (2 ^ n) K),
      (uTransport h hd1).toMonoidHom (u r) =
        primeFormConjHom h (idGram K d) A' ((uTransport h hd1).toMonoidHom r) := by
    intro r
    rw [hu']
    show uTransport h hd1 (uConjAut h hd1 A' r) = _
    have : uConjAut h hd1 A' = (MulAut.congr (uTransport h hd1)).symm
        (primeFormConjHom h (idGram K d) A') := rfl
    rw [this]
    simp [MulAut.congr_apply]
  have hker : (uTransport h hd1).toMonoidHom.ker ≤ Subgroup.center (StatedProj (StatedSU d (2 ^ n) K)) := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have : z = 1 := (uTransport h hd1).injective (hz.trans (map_one (uTransport h hd1)).symm)
    subst this
    exact Subgroup.one_mem _
  haveI : Finite (StatedProj (StatedSU d (2 ^ n) K)) := by
    haveI : Finite ↥(StatedSU d (2 ^ n) K) := inferInstance
    exact inferInstance
  have hL : GLAPComponent p (fixSubgroup (primeFormConjHom h (idGram K d) A'))
      (JP.map (uTransport h hd1).toMonoidHom) :=
    glaPComponent_map_fixSubgroup (uTransport h hd1).toMonoidHom hker u
      (primeFormConjHom h (idGram K d) A') hcompat (uTransport h hd1).surjective hp hJP
  have hperf : ⁅JP.map (uTransport h hd1).toMonoidHom, JP.map (uTransport h hd1).toMonoidHom⁆ =
      JP.map (uTransport h hd1).toMonoidHom := glaPComponent_perfect hL
  have hle := LieSemisimple.perfectInLayer_primeFormConjHom h hp hp2 A' hAc _ hL.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hL hle
  have H := primaryData_toLin' h hA hp hp2 hAc
  obtain ⟨a, hLeq⟩ := exists_good_block_of_component hq A' rfl H _ hcomp
  refine ⟨H, a, ?_⟩
  exact l154_JP_iff hd1 h JP _ ((specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])).comap
    (Matrix.GeneralLinearGroup.toLin : GL (Fin d) K ≃* LinearMap.GeneralLinearGroup K (Fin d → K)).toMonoidHom)
    (fun g => Iff.rfl) hLeq

end Setup

section Main

variable {n d : ℕ} {K : Type} [Field K]

theorem l154_toLin_symm_coe (g : LinearMap.GeneralLinearGroup K (Fin d → K)) :
    ((Matrix.GeneralLinearGroup.toLin.symm g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      LinearMap.toMatrix' (g : Module.End K (Fin d → K)) := rfl

theorem l154_toLin_scalar (z : Kˣ) :
    ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin d) z) :
      LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) =
        (z : K) • (1 : Module.End K (Fin d → K)) := by
  ext v i
  simp [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, Matrix.mulVec_smul]
  by_cases hi : i = v
  · subst hi; simp
  · simp [Pi.single_apply, hi]

theorem l154_line_matrix (g : LinearMap.GeneralLinearGroup K (Fin d → K)) (N : Module.End K (Fin d → K)) (c : K)
    (hg : (g : Module.End K (Fin d → K)) = 1 + c • N) :
    ((Matrix.GeneralLinearGroup.toLin.symm g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 + c • LinearMap.toMatrix' N := by
  rw [l154_toLin_symm_coe, hg, map_add, map_smul, LinearMap.toMatrix'_one]

theorem l154_matrix_ne_zero {N : Module.End K (Fin d → K)} (hN : N ≠ 0) : LinearMap.toMatrix' N ≠ 0 :=
  fun h0 => hN (LinearMap.toMatrix'.injective (h0.trans (map_zero _).symm))

theorem l154_scalar_of_matrix_eq {m : ℕ} {E : Type} [Field E] (P : GL (Fin m) E) (z : E) (hz : z ≠ 0)
    (hP : (P : Matrix (Fin m) (Fin m) E) = z • (1 : Matrix (Fin m) (Fin m) E)) :
    ∃ c : Eˣ, P = Matrix.GeneralLinearGroup.scalar (Fin m) c := by
  refine ⟨Units.mk0 z hz, ?_⟩
  ext i j
  rw [hP]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

@[expose] def L154BlockSU (n d : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 n K)
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K))) : Prop :=
  ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (k : ℕ) (ι : GL (Fin m) E →* GL (Fin d) K)
      (N : Matrix (Fin d) (Fin d) K),
    3 ≤ m ∧ 1 ≤ k ∧ (m = 3 → 2 ≤ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧ N ≠ 0 ∧
    (∀ c : K, h.bar c = c → ∃ t ∈ StatedSU m (2 ^ k) E,
      ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N) ∧
    (∀ t ∈ StatedSU m (2 ^ k) E, ι t ∈ StatedSU d (2 ^ n) K) ∧
    (∀ (P : GL (Fin m) E) (z : Kˣ), ι P = Matrix.GeneralLinearGroup.scalar (Fin d) z →
      ∃ c : Eˣ, P = Matrix.GeneralLinearGroup.scalar (Fin m) c) ∧
    (∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔ ∃ t ∈ StatedSU m (2 ^ k) E,
      ∃ ht : ι t ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, ht⟩ = z)

@[expose] def L154BlockSL (n d : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 n K)
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K))) : Prop :=
  ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (k : ℕ) (ι : GL (Fin m) E →* GL (Fin d) K)
      (N : Matrix (Fin d) (Fin d) K),
    2 ≤ m ∧ 2 ≤ k ∧ Nat.card E = 2 ^ k ∧ N ≠ 0 ∧
    (∀ c : K, h.bar c = c → ∃ t ∈ StatedSL m E,
      ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N) ∧
    (∀ t ∈ StatedSL m E, ι t ∈ StatedSU d (2 ^ n) K) ∧
    (∀ (P : GL (Fin m) E) (z : Kˣ), ι P = Matrix.GeneralLinearGroup.scalar (Fin d) z →
      ∃ c : Eˣ, P = Matrix.GeneralLinearGroup.scalar (Fin m) c) ∧
    (∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔ ∃ t ∈ StatedSL m E,
      ∃ ht : ι t ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, ht⟩ = z)

@[expose] def L154BlockSL2 (n d : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 n K)
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K))) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (k : ℕ) (ι : ↥(StatedSL 2 F) →* GL (Fin d) K)
      (N : Matrix (Fin d) (Fin d) K),
    2 ≤ k ∧ Nat.card F = 2 ^ k ∧ N ≠ 0 ∧ Function.Injective ι ∧
    (∀ c : K, h.bar c = c → ∃ t : ↥(StatedSL 2 F),
      ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N) ∧
    (∀ t : ↥(StatedSL 2 F), ι t ∈ StatedSU d (2 ^ n) K) ∧
    (∀ t : ↥(StatedSL 2 F), (∃ z : Kˣ, ι t = Matrix.GeneralLinearGroup.scalar (Fin d) z) →
      t ∈ Subgroup.center ↥(StatedSL 2 F)) ∧
    (∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔ ∃ t : ↥(StatedSL 2 F),
      ∃ ht : ι t ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, ht⟩ = z)

section Branches

variable (hn : 1 ≤ n) (h : UnitaryFieldData 2 n K) (A : GL (Fin d) K)
  (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K)))
  (H : UnitaryPrimaryData h.bar (idForm h d) (Matrix.GeneralLinearGroup.toLin A))
  (a : {a : primaryFactors ((Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) //
    IsGoodBlock h (Matrix.GeneralLinearGroup.toLin A) a})
  (hz : ∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔
    ∃ g : GL (Fin d) K, Matrix.GeneralLinearGroup.toLin g ∈
      specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ∧
      ∃ hg : g ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨g, hg⟩ = z)

include hn H a hz

private theorem l154_hmemSU
    (g : LinearMap.GeneralLinearGroup K (Fin d → K))
    (hg : g ∈ specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])) :
    Matrix.GeneralLinearGroup.toLin.symm g ∈ StatedSU d (2 ^ n) K := by
  have hq : 2 ≤ 2 ^ n := by
    have := Nat.one_lt_pow (by omega : n ≠ 0) Nat.one_lt_two
    omega
  have := specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg
  rw [statedSU_eq_gramSU h]
  refine (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K d) _).1 ?_
  rw [MulEquiv.apply_symm_apply]
  exact this

theorem l154_uni_block_su (hself : dualPoly h.bar (a.1 : K[X]) = a.1)
    (hm3 : 3 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K))
      (a.1 : K[X])) : L154BlockSU n d K h JP := by
  classical
  haveI := h.finite
  have hq : 2 ≤ 2 ^ n := by
    have := Nat.one_lt_pow (by omega : n ≠ 0) Nat.one_lt_two
    omega
  have hgood := a.2
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  have hdeg : 1 ≤ (a.1 : K[X]).natDegree := Irreducible.natDegree_pos Fact.out
  have hk1 : 1 ≤ n * (a.1 : K[X]).natDegree := Nat.mul_pos hn hdeg
  haveI : Finite (AdjoinRoot (a.1 : K[X])) := Module.finite_of_finite K
  obtain ⟨hE, ι, hinj, hspec, hscal⟩ := l154_selfDual_model H a.1 hself
  obtain ⟨N, hN, hline⟩ := l154_selfDual_line H a.1 hself hgood.1
  refine ⟨_, AdjoinRoot (a.1 : K[X]), inferInstance, inferInstance, n * (a.1 : K[X]).natDegree,
    (Matrix.GeneralLinearGroup.toLin.symm : _ ≃* GL (Fin d) K).toMonoidHom.comp ι,
    LinearMap.toMatrix' N, hm3, hk1, ?_, hE.card_eq_sq, l154_matrix_ne_zero hN, ?_, ?_, ?_, ?_⟩
  · intro hm
    have h3 := (isGoodBlock_numeric hq hself hgood).2 hm
    by_contra hk
    have hk' : n * (a.1 : K[X]).natDegree ≤ 1 := by omega
    have : 2 ^ (n * (a.1 : K[X]).natDegree) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk'
    omega
  · intro c hc
    obtain ⟨g, hg, hgc⟩ := hline c hc
    have hg' : g ∈ (StatedSU _ (2 ^ (n * (a.1 : K[X]).natDegree)) (AdjoinRoot (a.1 : K[X]))).map ι :=
      hspec ▸ hg
    obtain ⟨t, ht, rfl⟩ := hg'
    exact ⟨t, ht, l154_line_matrix _ N c hgc⟩
  · intro t ht
    exact l154_hmemSU hn h A JP H a hz _ (hspec ▸ Subgroup.mem_map_of_mem ι ht)
  · intro P z hzP
    have h1 : (ι P : LinearMap.GeneralLinearGroup K (Fin d → K)) =
        Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin d) z) := by
      rw [← hzP]
      exact (MulEquiv.apply_symm_apply _ _).symm
    have h2 := hscal P (z : K) (by
      have := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin d → K) =>
        (g : Module.End K (Fin d → K))) h1
      exact this.trans (l154_toLin_scalar z))
    exact l154_scalar_of_matrix_eq P _ (by simpa using z.ne_zero) h2
  · intro z
    rw [hz z]
    constructor
    · rintro ⟨g, hgSB, hg, hπ⟩
      obtain ⟨t, ht, hιt⟩ := (hspec ▸ hgSB :
        Matrix.GeneralLinearGroup.toLin g ∈ (StatedSU _ (2 ^ (n * (a.1 : K[X]).natDegree))
          (AdjoinRoot (a.1 : K[X]))).map ι)
      have hg_eq : Matrix.GeneralLinearGroup.toLin.symm (ι t) = g := by
        rw [hιt]; exact MulEquiv.symm_apply_apply _ _
      subst hg_eq
      exact ⟨t, ht, hg, hπ⟩
    · rintro ⟨t, ht, hιt, hπ⟩
      refine ⟨Matrix.GeneralLinearGroup.toLin.symm (ι t), ?_, hιt, hπ⟩
      rw [MulEquiv.apply_symm_apply]
      exact hspec ▸ Subgroup.mem_map_of_mem ι ht

theorem l154_uni_block_sl (hself : ¬ dualPoly h.bar (a.1 : K[X]) = a.1) : L154BlockSL n d K h JP := by
  classical
  haveI := h.finite
  have hgood := a.2
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  have hdeg : 1 ≤ (a.1 : K[X]).natDegree := Irreducible.natDegree_pos Fact.out
  haveI : Finite (AdjoinRoot (a.1 : K[X])) := Module.finite_of_finite K
  have hne : (a.1 : K[X]) ≠ dualPoly h.bar (a.1 : K[X]) := fun h' => hself h'.symm
  obtain ⟨ι, hinj, hspec, hscal⟩ := l154_paired_model H a.1 hne
  obtain ⟨N, hN, hline⟩ := l154_paired_line H a.1 hne hgood.1
  refine ⟨_, AdjoinRoot (a.1 : K[X]), inferInstance, inferInstance, 2 * (n * (a.1 : K[X]).natDegree),
    (Matrix.GeneralLinearGroup.toLin.symm : _ ≃* GL (Fin d) K).toMonoidHom.comp ι,
    LinearMap.toMatrix' N, hgood.1, by nlinarith [Nat.mul_pos hn hdeg], natCard_adjoinRoot h,
    l154_matrix_ne_zero hN, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨g, hg, hgc⟩ := hline c hc
    have hg' : g ∈ (StatedSL _ (AdjoinRoot (a.1 : K[X]))).map ι := hspec ▸ hg
    obtain ⟨t, ht, rfl⟩ := hg'
    exact ⟨t, ht, l154_line_matrix _ N c hgc⟩
  · intro t ht
    exact l154_hmemSU hn h A JP H a hz _ (hspec ▸ Subgroup.mem_map_of_mem ι ht)
  · intro P z hzP
    have h1 : (ι P : LinearMap.GeneralLinearGroup K (Fin d → K)) =
        Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin d) z) := by
      rw [← hzP]
      exact (MulEquiv.apply_symm_apply _ _).symm
    have h2 := hscal P (z : K) (by
      have := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin d → K) =>
        (g : Module.End K (Fin d → K))) h1
      exact this.trans (l154_toLin_scalar z))
    exact l154_scalar_of_matrix_eq P _ (by simpa using z.ne_zero) h2
  · intro z
    rw [hz z]
    constructor
    · rintro ⟨g, hgSB, hg, hπ⟩
      obtain ⟨t, ht, hιt⟩ := (hspec ▸ hgSB :
        Matrix.GeneralLinearGroup.toLin g ∈ (StatedSL _ (AdjoinRoot (a.1 : K[X]))).map ι)
      have hg_eq : Matrix.GeneralLinearGroup.toLin.symm (ι t) = g := by
        rw [hιt]; exact MulEquiv.symm_apply_apply _ _
      subst hg_eq
      exact ⟨t, ht, hg, hπ⟩
    · rintro ⟨t, ht, hιt, hπ⟩
      refine ⟨Matrix.GeneralLinearGroup.toLin.symm (ι t), ?_, hιt, hπ⟩
      rw [MulEquiv.apply_symm_apply]
      exact hspec ▸ Subgroup.mem_map_of_mem ι ht

theorem l154_sl2_equiv (hself : dualPoly h.bar (a.1 : K[X]) = a.1)
    (hm3 : ¬ 3 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K))
      (a.1 : K[X])) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (k : ℕ), 2 ≤ k ∧ Nat.card F = 2 ^ k ∧
      Nonempty (↥(specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])) ≃*
        ↥(StatedSL 2 F)) := by
  classical
  haveI := h.finite
  have hq : 2 ≤ 2 ^ n := by
    have := Nat.one_lt_pow (by omega : n ≠ 0) Nat.one_lt_two
    omega
  have hgood := a.2
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  have hm2 : primaryMultiplicity (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K))
      (a.1 : K[X]) = 2 := by
    have := hgood.1
    omega
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
    nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a.1 hself)
  have hV : Module.finrank (AdjoinRoot (a.1 : K[X]))
      (primaryComponent (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K)) (a.1 : K[X])) = 2 :=
    hm2
  obtain ⟨e2⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
  haveI : Finite hE.fixedField := inferInstance
  refine ⟨hE.fixedField, inferInstance, inferInstance, n * (a.1 : K[X]).natDegree, ?_,
    hE.card_fixedField,
    ⟨(e.trans e2).trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 hE.fixedField)⟩⟩
  have h4 := (isGoodBlock_numeric hq hself hgood).1 hm2
  by_contra hk
  have hk' : n * (a.1 : K[X]).natDegree ≤ 1 := by omega
  have : 2 ^ (n * (a.1 : K[X]).natDegree) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk'
  omega

theorem l154_uni_block_sl2 (hself : dualPoly h.bar (a.1 : K[X]) = a.1)
    (hm3 : ¬ 3 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K))
      (a.1 : K[X])) : L154BlockSL2 n d K h JP := by
  classical
  have hgood := a.2
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  obtain ⟨F, hF, hFfin, k, hk2, hcard, ⟨eSB⟩⟩ := l154_sl2_equiv hn h A JP H a hz hself hm3
  obtain ⟨N, hN, hline⟩ := l154_selfDual_line H a.1 hself hgood.1
  let ι' : ↥(StatedSL 2 F) →* GL (Fin d) K :=
    (Matrix.GeneralLinearGroup.toLin.symm : _ ≃* GL (Fin d) K).toMonoidHom.comp
      ((specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])).subtype.comp
        eSB.symm.toMonoidHom)
  have hι'inj : Function.Injective ι' := by
    intro t t' htt
    have h1 := Matrix.GeneralLinearGroup.toLin.symm.injective htt
    exact eSB.symm.injective (Subtype.ext h1)
  have hι'app : ∀ t, ι' t = Matrix.GeneralLinearGroup.toLin.symm
      ((eSB.symm t : ↥(specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin d → K)) := fun t => rfl
  refine ⟨F, hF, hFfin, k, ι', LinearMap.toMatrix' N, hk2, hcard, l154_matrix_ne_zero hN, hι'inj,
    ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨g, hg, hgc⟩ := hline c hc
    refine ⟨eSB ⟨g, hg⟩, ?_⟩
    rw [hι'app, MulEquiv.symm_apply_apply]
    exact l154_line_matrix g N c hgc
  · intro t
    exact l154_hmemSU hn h A JP H a hz _ (eSB.symm t).2
  · rintro t ⟨z, hzt⟩
    rw [Subgroup.mem_center_iff]
    intro t'
    apply hι'inj
    rw [map_mul, map_mul, hzt]
    exact (scalar_mul_comm z _).symm
  · intro z
    rw [hz z]
    constructor
    · rintro ⟨g, hgSB, hg, hπ⟩
      have ht : ι' (eSB ⟨Matrix.GeneralLinearGroup.toLin g, hgSB⟩) = g := by
        rw [hι'app, MulEquiv.symm_apply_apply]
        exact MulEquiv.symm_apply_apply _ _
      refine ⟨eSB ⟨Matrix.GeneralLinearGroup.toLin g, hgSB⟩, ?_⟩
      have hmem : ι' (eSB ⟨Matrix.GeneralLinearGroup.toLin g, hgSB⟩) ∈ StatedSU d (2 ^ n) K := by
        rw [ht]; exact hg
      refine ⟨hmem, ?_⟩
      have : (⟨ι' (eSB ⟨Matrix.GeneralLinearGroup.toLin g, hgSB⟩), hmem⟩ : ↥(StatedSU d (2 ^ n) K)) =
          ⟨g, hg⟩ := Subtype.ext ht
      rw [this]
      exact hπ
    · rintro ⟨t, ht, hπ⟩
      refine ⟨ι' t, ?_, ht, hπ⟩
      rw [hι'app, MulEquiv.apply_symm_apply]
      exact (eSB.symm t).2

omit hn H a hz

end Branches

variable (hd : 3 ≤ d)

theorem l154_uni_block_data (hn : 1 ≤ n) (hd : 3 ≤ d) (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (A : GL (Fin d) K) (hA : A ∈ primeFormUnitary h (idGram K d)) {c : Kˣ}
    (hAc : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (u : MulAut (StatedProj (StatedSU d (2 ^ n) K)))
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K))) (hJP : GLAPComponent p (fixSubgroup u) JP) :
    L154BlockSU n d K h JP ∨ L154BlockSL n d K h JP ∨ L154BlockSL2 n d K h JP := by
  obtain ⟨H, a, hz⟩ := l154_uni_good_block hn hd h hp hp2 A hA hAc u hu JP hJP
  by_cases hself : dualPoly h.bar (a.1 : K[X]) = a.1
  · by_cases hm3 : 3 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K))
        (a.1 : K[X])
    · exact Or.inl (l154_uni_block_su hn h A JP H a hz hself hm3)
    · exact Or.inr (Or.inr (l154_uni_block_sl2 hn h A JP H a hz hself hm3))
  · exact Or.inr (Or.inl (l154_uni_block_sl hn h A JP H a hz hself))

end Main



end CFSG.LocalAnalysis.GLTheoremA.K155X
