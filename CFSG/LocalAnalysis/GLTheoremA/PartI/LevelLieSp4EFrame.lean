module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4ETypeA
public import CFSG.Adapters.LinearCatalog
public import CFSG.Models.PGLSimple
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4ENorm
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open scoped commutatorElement

theorem kLevel_le_two_of_k2' {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  by_cases h1 : IsChevSimple p S
  · rw [if_pos h1]
    norm_num
  · rw [if_neg h1, if_pos h]

theorem pSimple_map_equiv' {G G' : Type} [Group G] [Group G'] (p : ℕ) (e : G ≃* G')
    (K : Subgroup G) : Nonempty (PSimple p (K.map e.toMonoidHom) ≃* PSimple p K) := by
  let eK : ↥K ≃* ↥(K.map e.toMonoidHom) := K.equivMapOfInjective e.toMonoidHom e.injective
  have hO : (GLAPPrimeCore p ↥K).map eK.toMonoidHom = GLAPPrimeCore p ↥(K.map e.toMonoidHom) :=
    glaPPrimeCore_map_iso p eK
  let pq : PQuot p (K.map e.toMonoidHom) ≃* PQuot p K :=
    (QuotientGroup.congr (GLAPPrimeCore p ↥K) (GLAPPrimeCore p ↥(K.map e.toMonoidHom)) eK hO).symm
  exact ⟨QuotientGroup.congr _ _ pq (Subgroup.map_center_eq pq)⟩

theorem map_centralizer_equiv' {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (s : G) :
    (Subgroup.centralizer {s}).map e.toMonoidHom = Subgroup.centralizer {e s} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e y * e s = e s * e y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    change e (e.symm x * s) = e (s * e.symm x)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx

theorem pSimple_equiv_of_simple' {Γ : Type} [Group Γ] [Finite Γ] (K : Subgroup Γ) [IsSimpleGroup K]
    (hnc : ¬ IsMulCommutative K) (h3 : 3 ∣ Nat.card K) : Nonempty (PSimple 3 K ≃* K) := by
  have hO : GLAPPrimeCore 3 K = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup
      Nat.prime_three h3
  let pq0 : PQuot 3 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hZK : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center K := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  have hZP : Subgroup.center (PQuot 3 K) = ⊥ := by
    have h1 := Subgroup.map_center_eq pq0
    rw [hZK] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ pq0.injective).1 h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZP).trans (QuotientGroup.quotientBot.trans pq0)⟩

section SL2

variable {K : Type} [Field K] [CharP K 2]

theorem isSimpleGroup_SL2 [Finite K] (hK : Nat.card K = 8) : IsSimpleGroup ↥(StatedSL 2 K) := by
  have h1 : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    isSimpleGroup_statedProj_statedSL K (by norm_num) (Or.inr (by omega)) (Or.inr (by omega))
  let e : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSL_two_eq_bot (K := K))).trans
      QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem nat_card_SL2 [Finite K] (hK : Nat.card K = 8) : Nat.card ↥(StatedSL 2 K) = 504 := by
  rw [card_statedSL_two, hK]
  norm_num

theorem not_comm_SL2 [Finite K] : ¬ IsMulCommutative ↥(StatedSL 2 K) := by
  intro h
  let a : ↥(StatedSL 2 K) := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1]
    (by simp [Matrix.det_fin_two]), by
      rw [mem_statedSL_iff]
      simp [Matrix.det_fin_two]⟩
  let b : ↥(StatedSL 2 K) := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1]
    (by simp [Matrix.det_fin_two]), by
      rw [mem_statedSL_iff]
      simp [Matrix.det_fin_two]⟩
  have hab := h.is_comm.comm a b
  have hm := congrArg (fun x : ↥(StatedSL 2 K) => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hab
  simp [a, b, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero] at hm

theorem not_comm_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : ¬ IsMulCommutative G') : ¬ IsMulCommutative G := by
  intro hG
  apply h
  refine ⟨⟨fun a b => ?_⟩⟩
  have hab := hG.is_comm.comm (e.symm a) (e.symm b)
  have := congrArg e hab
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem catalog_SL2 [Fintype K] (hK : Nat.card K = 8) : catalogIs ↥(StatedSL 2 K) (k2 3) := by
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hq8 : q.p ^ q.exponent = 8 := by norm_num [q]
  have hqcard : q.card = 8 := (TauCeti.PrimePower.card_def q).trans hq8
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    constructor
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      simp [hq8]
    · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp [hq8]
  let F := GaloisField 2 3
  have hF : Nat.card F = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  let e1 := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  let e2 := projectiveSpecialLinearGroupEquivStatedProj (1 + 1) F
  let e3 : StatedProj (StatedSL (1 + 1) F) ≃* ↥(StatedSL (1 + 1) F) :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSL_two_eq_bot (K := F))).trans
      QuotientGroup.quotientBot
  let e : (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩) ≃* ↥(StatedSL 2 F) :=
    e1.trans (e2.trans e3)
  haveI : Fintype F := Fintype.ofFinite F
  have hcardK : Fintype.card K = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF]
  let φ : K ≃+* F := FiniteField.ringEquivOfCardEq hcardK
  let eK : ↥(StatedSL 2 K) ≃* ↥(StatedSL 2 F) :=
    (MulEquiv.subgroupMap (glCongr (ι := Fin 2) φ) (StatedSL 2 K)).trans
      (MulEquiv.subgroupCongr (glCongr_statedSL φ 2))
  refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩, ?_, ⟨eK.trans e.symm⟩⟩
  show (3 = 3 ∧ ¬ 3 ∣ q.card)
  exact ⟨rfl, by rw [hqcard]; norm_num⟩

end SL2

section D0Facts

variable {K : Type} [Field K] [CharP K 2]

noncomputable def eD0 : ↥(StatedSL 2 K) ≃* ↥(D0 K) :=
  MonoidHom.ofInjective (iotaH_injective (K := K))

theorem isSimpleGroup_D0 [Finite K] (hK : Nat.card K = 8) : IsSimpleGroup ↥(D0 K) := by
  haveI := isSimpleGroup_SL2 hK
  exact (eD0 (K := K)).symm.isSimpleGroup

theorem card_D0 [Finite K] (hK : Nat.card K = 8) : Nat.card ↥(D0 K) = 504 :=
  (Nat.card_congr (eD0 (K := K)).toEquiv).symm.trans (nat_card_SL2 hK)

theorem not_comm_D0 [Finite K] : ¬ IsMulCommutative ↥(D0 K) :=
  not_comm_of_mulEquiv (eD0 (K := K)).symm not_comm_SL2

theorem kLevel_D0_le [Fintype K] (hK : Nat.card K = 8) : kLevel 3 ↥(D0 K) ≤ 2 := by
  rw [← kLevel_congr 3 (eD0 (K := K))]
  exact kLevel_le_two_of_k2' (catalog_SL2 hK)

end D0Facts

section TypeA

variable {K : Type} [Field K] [CharP K 2]

theorem typeA_kLevel [Fintype K] (hK : Nat.card K = 8) {A : ↥(StatedSp 2 K)} (hA3 : A ^ 3 = 1)
    (hP0 : Pm (mat A) ≠ 0) (hP1 : Pm (mat A) ≠ 1) {I : Subgroup ↥(StatedSp 2 K)}
    (hI : GLAPComponent 3 (Subgroup.centralizer ({A} : Set ↥(StatedSp 2 K))) I) :
    kLevel 3 (PSimple 3 I) ≤ 2 := by
  have hcard : Fintype.card K = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  haveI : IsSimpleGroup ↥(D0 K) := isSimpleGroup_D0 hK
  have h3' : mat A ^ 3 = 1 := by
    have := congrArg (fun x : ↥(StatedSp 2 K) => ((x : GL Ix K) : Matrix Ix Ix K)) hA3
    unfold mat
    simpa using this
  have h3 : mat A * mat A * mat A = 1 := by
    rw [← pow_three']
    exact h3'
  obtain ⟨c, g, hc, hgsym, hconj⟩ := exists_conj_planeMat hcard (mem_mat A) h3 hP0 hP1
  set g' : ↥(StatedSp 2 K) := ⟨g, mem_statedSp_iff.2 hgsym⟩ with hg'
  set τ : ↥(StatedSp 2 K) ≃* ↥(StatedSp 2 K) := MulAut.conj g'⁻¹ with hτ
  have hB : mat (τ A) = planeMat ![1, Tmat c] := by
    have hτA : τ A = g'⁻¹ * A * g' := by
      rw [hτ, MulAut.conj_apply, inv_inv]
    rw [hτA, mat_mul, mat_mul]
    have hg'm : mat g' = (g : Matrix Ix Ix K) := rfl
    have hgi : mat g'⁻¹ = ((g⁻¹ : GL Ix K) : Matrix Ix Ix K) := rfl
    rw [hg'm, hgi]
    have hA : mat A * (g : Matrix Ix Ix K) = (g : Matrix Ix Ix K) * planeMat ![1, Tmat c] := hconj
    rw [mul_assoc, hA, ← mul_assoc, Units.inv_mul, one_mul]
  have hI' := glaPComponent_map_mulEquiv Nat.prime_three τ hI
  rw [map_centralizer_equiv'] at hI'
  have hIeq : I.map τ.toMonoidHom = D0 K := components_eq_D0 hc hB hI'
  obtain ⟨eI⟩ := pSimple_map_equiv' 3 τ I
  have h1 : kLevel 3 (PSimple 3 (I.map τ.toMonoidHom)) = kLevel 3 (PSimple 3 I) :=
    kLevel_congr 3 eI
  rw [← h1, hIeq]
  have hord : 3 ∣ Nat.card ↥(D0 K) := by
    rw [card_D0 hK]
    norm_num
  obtain ⟨eP⟩ := pSimple_equiv_of_simple' (D0 K) not_comm_D0 hord
  rw [kLevel_congr 3 eP]
  exact kLevel_D0_le hK

end TypeA

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
