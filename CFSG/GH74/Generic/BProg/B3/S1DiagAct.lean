module

public import CFSG.GH74.Generic.BProg.B3.S1DiagActFrame
public import CFSG.GH74.Generic.BProg.B3.S1DiagActMat
public import CFSG.GH74.Generic.BProg.B3.S1DiagActModel
public import CFSG.GH74.Generic.BProg.B1.PilotS1Facts
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicIso4
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
public import CFSG.GH74.Generic.BProg.B2.GenLocU3
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS1
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

namespace S1DiagAct

theorem exists_quaternion_pair {X : Type} [Group X] {F : Type} [Field F] [Finite F] {z u : X}
    {J₁ J₂ : Subgroup X} (hS : SplitAt F (⊤ : Subgroup X) z u J₁ J₂) :
    (2 : F) ≠ 0 ∧ ∃ a ∈ J₁, ∃ b ∈ J₁, a * a = u ∧ b * b = u ∧ a * b = u * (b * a) := by
  obtain ⟨e₁⟩ := hS.equiv₁
  set uJ : ↥J₁ := ⟨u, hS.u_mem⟩ with huJ
  have hcen : ∀ y : ↥J₁, y * uJ = uJ * y := fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hS.le₁ y.2).1)
  have hZ : e₁ uJ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := e₁.surjective s
    rw [← map_mul, ← map_mul, hcen y]
  obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hZ
  have hu1 : u ≠ 1 := by
    intro h
    have := hS.ord
    rw [h, orderOf_one] at this
    omega
  have huJ1 : uJ ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  rw [Fintype.card_fin] at hr
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply huJ1
    apply e₁.injective
    rw [map_one]
    apply Subtype.ext
    rw [← hrs]
    simp
  have hrm : r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hr1
    · exact eq_neg_of_add_eq_zero_left h
  have h2 : (2 : F) ≠ 0 := by
    intro h
    apply hr1
    rw [hrm]
    linear_combination -h
  refine ⟨h2, ?_⟩
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨⟨a, b, hab⟩, H⟩ := odd_field_two_dimensional_quaternion_matrices hF2
  obtain ⟨hdI, hdJ, hII, hJJ, hIJ, -⟩ := H a b hab
  let I' : SL(2, F) := ⟨quatI F, hdI⟩
  let J' : SL(2, F) := ⟨quatJ a b, hdJ⟩
  have heu : ((e₁ uJ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [← hrs, hrm, map_neg, map_one]
  refine ⟨(e₁.symm I' : ↥J₁), (e₁.symm I').2, (e₁.symm J' : ↥J₁), (e₁.symm J').2, ?_, ?_, ?_⟩
  · have : e₁.symm I' * e₁.symm I' = uJ := by
      apply e₁.injective
      rw [map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, heu]
      exact hII
    exact congrArg Subtype.val this
  · have : e₁.symm J' * e₁.symm J' = uJ := by
      apply e₁.injective
      rw [map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, heu]
      exact hJJ
    exact congrArg Subtype.val this
  · have : e₁.symm I' * e₁.symm J' = uJ * (e₁.symm J' * e₁.symm I') := by
      apply e₁.injective
      rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, heu]
      rw [neg_mul, one_mul]
      exact hIJ
    exact congrArg Subtype.val this

theorem exists_invol_in_J₂ {X : Type} [Group X] {F : Type} [Field F] [Finite F] {z u : X}
    {J₁ J₂ : Subgroup X} (hS : SplitAt F (⊤ : Subgroup X) z u J₁ J₂) (h2 : (2 : F) ≠ 0) :
    ∃ w ∈ J₂, w ≠ 1 ∧ w * w = 1 := by
  obtain ⟨e₂⟩ := hS.equiv₂
  let m : SL(2, F) := ⟨-1, by simp [Matrix.det_neg]⟩
  have hm1 : m ≠ 1 := by
    intro h
    have h' := congrFun (congrFun (congrArg Subtype.val h) 0) 0
    simp only [m, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.SpecialLinearGroup.coe_one] at h'
    apply h2
    linear_combination -h'
  have hmm : m * m = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    simp [m]
  refine ⟨(e₂.symm m : ↥J₂), (e₂.symm m).2, ?_, ?_⟩
  · intro h
    apply hm1
    apply e₂.symm.injective
    rw [map_one]
    exact Subtype.ext h
  · have : e₂.symm m * e₂.symm m = 1 := by rw [← map_mul, hmm, map_one]
    exact congrArg Subtype.val this

theorem not_central {X : Type} [Group X] {F : Type} [Field F] [Finite F] {z u : X}
    {J₁ J₂ : Subgroup X} (hS : SplitAt F (⊤ : Subgroup X) z u J₁ J₂) (hz : ∀ g : X, g * z = z * g)
    {z₀ : X} (hcenter : ∀ g : X, g ∈ Subgroup.center X ↔ g = 1 ∨ g = z₀) (h2 : (2 : F) ≠ 0)
    (hu : u ≠ 1) (hucen : ∀ g : X, g * u = u * g) : False := by
  have hu0 : u = z₀ := ((hcenter u).1 (Subgroup.mem_center_iff.2 hucen)).resolve_left hu
  have hz1 : z ≠ 1 := by
    intro h
    have hzu := hS.zu_mem
    rw [h, one_mul] at hzu
    exact hu (Subgroup.disjoint_def.1 hS.disj hS.u_mem hzu)
  have hzz : z = z₀ := ((hcenter z).1 (Subgroup.mem_center_iff.2 hz)).resolve_left hz1
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hS.ord, pow_two] at this
  obtain ⟨w, hw, hw1, hww⟩ := exists_invol_in_J₂ hS h2
  have hwc : ∀ j ∈ J₁, w * j = j * w := fun j hj => (hS.commute j hj w hw).symm
  rcases hS.invol w (Subgroup.mem_top _) hww hwc with h | h | h | h
  · exact hw1 h
  · have : u ∈ J₂ := by rw [hu0, ← hzz, ← h]; exact hw
    exact hu (Subgroup.disjoint_def.1 hS.disj hS.u_mem this)
  · have : u ∈ J₂ := h ▸ hw
    exact hu (Subgroup.disjoint_def.1 hS.disj hS.u_mem this)
  · apply hw1
    rw [h, hzz, ← hu0, huu]

end S1DiagAct

open S1DiagActMat S1DiagActFrame S1DiagActModel

theorem sl4_diag_action {Kt : Type} [Group Kt] [Finite Kt] (hK : QShape1 Kt) {Ab : Subgroup Kt}
    (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8) {F : Type} [Field F] [Finite F]
    {z u : Kt} {J₁ J₂ : Subgroup Kt} (huA : u ∈ Ab)
    (hS : B1.PilotS1.SplitAt F (⊤ : Subgroup Kt) z u J₁ J₂) (hz : ∀ g : Kt, g * z = z * g)
    (δ : MulAut Kt) (hδ : δ * δ = 1) (hδA : ∀ e ∈ Ab, δ e = e) (hδJ : ∀ g ∈ J₁, δ g = g) :
    ∃ e ∈ Ab, ∀ g ∈ J₂, δ g = e * g * e⁻¹ := by
  classical
  obtain ⟨h2, a₀, ha₀, b₀, hb₀, haa, hbb, hab⟩ := S1DiagAct.exists_quaternion_pair hS
  have hu1 : u ≠ 1 := by
    intro h
    have := hS.ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨F', _, _, ι, hinj, h2', hdet, hform⟩ := matrix_dichotomy hK δ hδ
  have hune : ι u ≠ -1 := by
    intro h
    obtain ⟨z₀, -, -, -, hcenter, -⟩ := IsSL4Model.exists_q8_frame hK
    refine S1DiagAct.not_central hS hz hcenter h2 hu1 (fun g => ?_)
    apply hinj
    rw [map_mul, map_mul, h]
    simp
  let E : Subgroup (GL (Fin 4) F') := Ab.map ι
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ι (congrArg Subtype.val (hAe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hsq : ∀ a ∈ Ab, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Ab) a ha
    rwa [pow_two] at this
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  have hEdet : ∀ x ∈ E, (x : Matrix (Fin 4) (Fin 4) F').det = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hdet a
  have hEcard : Nat.card E = 8 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hA8
  obtain ⟨P, hPu, hPe⟩ := exists_frame h2' E hEcomm hEsq hEdet hEcard (Subgroup.mem_map_of_mem ι huA)
    (fun h => hu1 (hinj (h.trans (map_one ι).symm))) hune
  obtain ⟨X, hX⟩ : ∃ X : Kt → Matrix (Fin 4) (Fin 4) F',
      ∀ x, X x = cj P ((ι x : GL (Fin 4) F') : Matrix (Fin 4) (Fin 4) F') := ⟨_, fun _ => rfl⟩
  have hXmul : ∀ x y, X (x * y) = X x * X y := fun x y => by
    rw [hX, hX, hX, map_mul, Units.val_mul, cj_mul]
  have hXu : X u = Matrix.diagonal ![-1, -1, 1, 1] := by
    rw [hX, cj_gl]; exact hPu
  have hBD : ∀ x, x * u = u * x → IsBD (X x) := fun x hx => by
    apply isBD_of_commute h2'
    rw [← hXu, ← hXmul, ← hXmul, hx]
  have hXe : ∀ ε : Fin 4 → F', (∀ i, ε i = 1 ∨ ε i = -1) → ε 0 * ε 1 * ε 2 * ε 3 = 1 →
      ∃ e ∈ Ab, X e = Matrix.diagonal ε := by
    intro ε hε hp
    obtain ⟨_, ⟨e, he, rfl⟩, h⟩ := hPe ε hε hp
    exact ⟨e, he, by rw [hX, cj_gl]; exact h⟩
  have hv1 : ∀ i, (![-1, -1, 1, 1] : Fin 4 → F') i = 1 ∨ (![-1, -1, 1, 1] : Fin 4 → F') i = -1 :=
    fun i => by fin_cases i <;> simp
  have hv2 : ∀ i, (![-1, 1, -1, 1] : Fin 4 → F') i = 1 ∨ (![-1, 1, -1, 1] : Fin 4 → F') i = -1 :=
    fun i => by fin_cases i <;> simp
  obtain ⟨e₁, he₁, hXe₁⟩ := hXe ![-1, -1, 1, 1] hv1 (by simp)
  obtain ⟨e₂, he₂, hXe₂⟩ := hXe ![-1, 1, -1, 1] hv2 (by simp)
  have hcu₁ : ∀ j ∈ J₁, j * u = u * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hS.le₁ hj).1
  have hcu₂ : ∀ j ∈ J₂, j * u = u * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hS.le₂ hj).1
  have hA2 : tl (X a₀) * tl (X a₀) = -1 := by
    rw [← tl_mul (hBD a₀ (hcu₁ a₀ ha₀)) (hBD a₀ (hcu₁ a₀ ha₀)), ← hXmul, haa, hXu, tl_y0]
  have hC2 : tl (X b₀) * tl (X b₀) = -1 := by
    rw [← tl_mul (hBD b₀ (hcu₁ b₀ hb₀)) (hBD b₀ (hcu₁ b₀ hb₀)), ← hXmul, hbb, hXu, tl_y0]
  have hAC : tl (X a₀) * tl (X b₀) = -(tl (X b₀) * tl (X a₀)) := by
    have hBa := hBD a₀ (hcu₁ a₀ ha₀)
    have hBb := hBD b₀ (hcu₁ b₀ hb₀)
    rw [← tl_mul hBa hBb, ← tl_mul hBb hBa, ← hXmul, ← hXmul, hab, hXmul, hXmul, hXu,
      tl_mul (isBD_diagonal _) (isBD_mul hBb hBa), tl_mul hBb hBa, tl_y0, neg_mul, one_mul]
  rcases hform with ⟨g, c, hc0, hg, hgc⟩ | ⟨B, hB⟩
  ·
    obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin 4) (Fin 4) F', G = cj P (g : Matrix (Fin 4) (Fin 4) F') :=
      ⟨_, rfl⟩
    have hGc : G * G = c • 1 := by rw [hG, ← cj_mul, hgc, cj_smul_one]
    have hcomm_e : ∀ e ∈ Ab, X e * G = G * X e := by
      intro e he
      have h1 : ι e * g = g * ι e := by
        have := hg e
        rw [hδA e he] at this
        calc ι e * g = g * ι e * g⁻¹ * g := by rw [← this]
          _ = g * ι e := by group
      have h2 : cj P ((ι e * g : GL (Fin 4) F') : Matrix (Fin 4) (Fin 4) F') =
          cj P ((g * ι e : GL (Fin 4) F') : Matrix (Fin 4) (Fin 4) F') := by rw [h1]
      rw [Units.val_mul, Units.val_mul, cj_mul, cj_mul, ← hG] at h2
      rw [hX e]
      exact h2
    have hGoff : ∀ i j, i ≠ j → G i j = 0 := by
      refine offdiag_eq_zero_of_commute h2' ?_ ?_
      · have := hcomm_e e₁ he₁
        rw [hXe₁] at this
        exact this.symm
      · have := hcomm_e e₂ he₂
        rw [hXe₂] at this
        exact this.symm
    obtain ⟨γ, hGγ⟩ : ∃ γ : Fin 4 → F', G = Matrix.diagonal γ :=
      ⟨_, diagonal_of_offdiag_zero hGoff⟩
    have hγ : ∀ i, γ i * γ i = c := fun i => by
      have := sq_diag_entries hGoff hGc i
      rw [hGγ] at this
      simpa using this
    subst hGγ
    have hγ2 : γ 2 ≠ 0 := fun h => hc0 (by rw [← hγ 2, h, mul_zero])
    obtain ⟨s, hs⟩ : ∃ s : F', s = γ 3 / γ 2 := ⟨_, rfl⟩
    have hss : s * s = 1 := by
      rw [hs]
      field_simp
      linear_combination hγ 3 - hγ 2
    have hs_sign : s = 1 ∨ s = -1 := by
      have : (s - 1) * (s + 1) = 0 := by linear_combination hss
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have hε : ∀ i, (![1, s, 1, s] : Fin 4 → F') i = 1 ∨ (![1, s, 1, s] : Fin 4 → F') i = -1 := by
      intro i
      fin_cases i
      · exact Or.inl rfl
      · exact hs_sign
      · exact Or.inl rfl
      · exact hs_sign
    obtain ⟨e₀, he₀, hXe₀⟩ := hXe ![1, s, 1, s] hε (by simpa using hss)
    have hdiag : X e₀ * Matrix.diagonal γ =
        Matrix.diagonal (fun i => (![1, s, 1, s] : Fin 4 → F') i * γ i) := by
      rw [hXe₀, Matrix.diagonal_mul_diagonal]
    have hd : (![1, s, 1, s] : Fin 4 → F') 2 * γ 2 = (![1, s, 1, s] : Fin 4 → F') 3 * γ 3 := by
      show (1 : F') * γ 2 = s * γ 3
      rw [hs]
      field_simp
      linear_combination hγ 2 - hγ 3
    refine ⟨e₀, he₀, fun h hh => ?_⟩
    have hBh := hBD h (hcu₂ h hh)
    have hBa := hBD a₀ (hcu₁ a₀ ha₀)
    have hBb := hBD b₀ (hcu₁ b₀ hb₀)
    have hha : tl (X h) * tl (X a₀) = tl (X a₀) * tl (X h) := by
      rw [← tl_mul hBh hBa, ← tl_mul hBa hBh, ← hXmul, ← hXmul, hS.commute a₀ ha₀ h hh]
    have hhb : tl (X h) * tl (X b₀) = tl (X b₀) * tl (X h) := by
      rw [← tl_mul hBh hBb, ← tl_mul hBb hBh, ← hXmul, ← hXmul, hS.commute b₀ hb₀ h hh]
    obtain ⟨c', hc'⟩ := scalar_of_commute_pair h2' hA2 hC2 hAC hha hhb
    obtain ⟨h01, h10, h11⟩ := entries_of_tl_scalar hc'
    have hcomm := commute_diagonal_of_block hBh h01 h10 h11
      (fun i => (![1, s, 1, s] : Fin 4 → F') i * γ i) hd
    have hK : ι e₀ * g * ι h = ι h * (ι e₀ * g) := by
      apply Units.ext
      apply cj_injective P
      simp only [Units.val_mul, cj_mul, ← hX, ← hG]
      rw [hdiag.symm] at hcomm
      exact hcomm
    have hee : ι e₀ * ι e₀ = 1 := by rw [← map_mul, hsq e₀ he₀, map_one]
    have hinvι : (ι e₀)⁻¹ = ι e₀ := inv_eq_of_mul_eq_one_right hee
    have he0inv : e₀⁻¹ = e₀ := inv_eq_of_mul_eq_one_right (hsq e₀ he₀)
    apply hinj
    rw [hg h, he0inv, map_mul, map_mul]
    calc g * ι h * g⁻¹ = (ι e₀)⁻¹ * (ι e₀ * g * ι h) * g⁻¹ := by group
      _ = (ι e₀)⁻¹ * (ι h * (ι e₀ * g)) * g⁻¹ := by rw [hK]
      _ = (ι e₀)⁻¹ * ι h * ι e₀ := by group
      _ = ι e₀ * ι h * ι e₀ := by rw [hinvι]
  ·
    exfalso
    obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 4) (Fin 4) F', B' = cjB P (B : Matrix (Fin 4) (Fin 4) F') :=
      ⟨_, rfl⟩
    have hinv : ∀ x, δ x = x → X x * B' * (X x)ᵀ = B' := by
      intro x hx
      have := hB x
      rw [hx] at this
      rw [hX x, hB']
      exact cj_invariant P this
    have hD1 : B' * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * B' := by
      have := hinv e₁ (hδA e₁ he₁)
      rw [hXe₁] at this
      exact commute_of_invariant_sign _ (fun i => by fin_cases i <;> simp) this
    have hD2 : B' * Matrix.diagonal ![-1, 1, -1, 1] = Matrix.diagonal ![-1, 1, -1, 1] * B' := by
      have := hinv e₂ (hδA e₂ he₂)
      rw [hXe₂] at this
      exact commute_of_invariant_sign _ (fun i => by fin_cases i <;> simp) this
    have hoff : ∀ i j, i ≠ j → B' i j = 0 := offdiag_eq_zero_of_commute h2' hD1 hD2
    obtain ⟨hβ₀, hβ₁⟩ := diag_entries_ne_zero hoff (by rw [hB']; exact det_cjB_ne_zero P B)
    have htl : tl B' = Matrix.diagonal ![B' 0 0, B' 1 1] :=
      tl_diagonal_of_offdiag (hoff 0 1 (by decide)) (hoff 1 0 (by decide))
    have hBa := hBD a₀ (hcu₁ a₀ ha₀)
    have hBb := hBD b₀ (hcu₁ b₀ hb₀)
    have hA := congrArg tl (hinv a₀ (hδJ a₀ ha₀))
    rw [tl_mul3 hBa hBa, htl] at hA
    have hC := congrArg tl (hinv b₀ (hδJ b₀ hb₀))
    rw [tl_mul3 hBb hBb, htl] at hC
    exact no_skew_pair h2' hβ₀ hβ₁ hA2 hC2 hAC hA hC

end CFSG.GH74.Generic.BProg.B3
