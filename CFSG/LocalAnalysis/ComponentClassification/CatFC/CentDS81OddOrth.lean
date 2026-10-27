module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFam
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddProj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOType
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOReduce
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthSign
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOFam
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.GH74.Generic.S1.TQ3BarVert
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.GH74.GLS.TwoThin.ClassCongr
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.GH74.Generic.S1.SymSystem
public import CFSG.GH74.Generic.S45.PumpB1
public import CFSG.GH74.Generic.S45.PumpLeaves
public import CFSG.GH74.Generic.S45.PumpTail
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)
open scoped MatrixGroups commutatorElement

theorem isSolvable_sup_of_commute {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) [Group.IsSolvable A] [Group.IsSolvable B] :
    Group.IsSolvable ↥(A ⊔ B) := by
  let f : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => hcomm a a.2 b b.2)
  have hrange : f.range = A ⊔ B := by
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => hcomm a a.2 b b.2)
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
  have : Group.IsSolvable (A × B) := inferInstance
  have h1 : Group.IsSolvable ↥f.range := solvable_of_surjective f.rangeRestrict_surjective
  rw [hrange] at h1
  exact h1

theorem isSolvable_of_perfect_le {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    [Group.IsSolvable S] (h : ∀ Q : Subgroup G, ⁅Q, Q⁆ = Q → Q ≤ S) : Group.IsSolvable G := by
  refine CFSG.GH74.Generic.S1.isSolvable_of_forall_perfect fun Q hQ => ?_
  have hle : Q ≤ S := h Q hQ
  haveI : Group.IsSolvable ↥Q :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQ
  by_contra hne
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  exact Group.IsPerfect.not_isSolvable (G := ↥Q) ‹_›

variable {K : Type} [Field K] [Finite K]

theorem sign_dichotomy (hK : ringChar K ≠ 2) {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J : Finset (Fin d)) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    (hJne : J.Nonempty) (hJcne : Jᶜ.Nonempty) :
    SolvableOrComponent (StatedProj (matrixDerived (oQ (diagGL hw))))
      (projH _ ⟨signGL K J, hJ⟩) := by
  set x := projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) with hx
  set C := centralizer ({x} : Set (StatedProj (matrixDerived (oQ (diagGL hw))))) with hC
  have hIc : ∀ I, (I = J ∨ I = Jᶜ) → Iᶜ.Nonempty := by
    rintro I (rfl | rfl)
    · exact hJcne
    · rwa [compl_compl]
  have hblock : ∀ I, (I = J ∨ I = Jᶜ) →
      (∃ Kc : Subgroup ↥C, IsComponent Kc) ∨ Group.IsSolvable (blockP K hw I) := by
    intro I hI
    rcases blockP_cases hw hK I (hIc I hI) with hs | hq | ⟨-, -, hsplit⟩
    · exact Or.inr hs
    · left
      have hle := blockP_le_centralizer hw J I hI hJ
      exact ⟨(blockP K hw I).subgroupOf C,
        LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq,
        isSubnormal_blockP hw hK J I hI hJ⟩
    · left
      obtain ⟨L₁, L₂, -, hL₁, hL₂, hn₁, hn₂, hq₁, hq₂, -, -⟩ := hsplit
      obtain ⟨hle, hsn⟩ := isSubnormal_projBlock hw hK J I hI hJ hL₁ hn₁
      exact ⟨(projBlock hw I L₁).subgroupOf C,
        LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq₁, hsn⟩
  rcases hblock J (Or.inl rfl) with h | hJs
  · exact Or.inr h
  rcases hblock Jᶜ (Or.inr rfl) with h | hJcs
  · exact Or.inr h
  left
  haveI := hJs
  haveI := hJcs
  have hcomm : ∀ a ∈ blockP K hw J, ∀ b ∈ blockP K hw Jᶜ, a * b = b * a := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact commute_of_mem_oIsoBlock hw (oBlock_le_oIsoBlock hw J hg) (oBlock_le_oIsoBlock hw Jᶜ hh)
  haveI hB : Group.IsSolvable ↥(blockP K hw J ⊔ blockP K hw Jᶜ) :=
    isSolvable_sup_of_commute _ _ hcomm
  have hBC : blockP K hw J ⊔ blockP K hw Jᶜ ≤ C :=
    sup_le (blockP_le_centralizer hw J J (Or.inl rfl) hJ)
      (blockP_le_centralizer hw J Jᶜ (Or.inr rfl) hJ)
  haveI : Group.IsSolvable ↥((blockP K hw J ⊔ blockP K hw Jᶜ).subgroupOf C) :=
    solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBC).symm.surjective
  refine isSolvable_of_perfect_le ((blockP K hw J ⊔ blockP K hw Jᶜ).subgroupOf C) ?_
  intro Q hQ
  have hperf : ⁅Q.map C.subtype, Q.map C.subtype⁆ = Q.map C.subtype := by
    rw [← Subgroup.map_commutator, hQ]
  have hle : Q.map C.subtype ≤ blockP K hw J ⊔ blockP K hw Jᶜ :=
    le_blockP_sup_of_perfect hw hK J hJ (Subgroup.map_subtype_le Q) hperf
  intro g hg
  exact hle ⟨g, hg, rfl⟩

theorem pc_dichotomy (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f)
    {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat c)) :
    SolvableOrComponent (StatedProj (matrixDerived (oQ R))) (projH _ A) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat, diagonal_transpose]
  set Z := isoCent R (A : GL (Fin (2 * n)) K) with hZ
  have hq := isQuasisimple_isoCent_pc hK hp hKc hc hn hR hA
  have hZΩ : ⁅Z, Z⁆ ≤ matrixDerived (oQ R) := by
    rw [matrixDerived_oQ h2 R hRs]
    exact commutator_mono inf_le_left inf_le_left
  set B := (⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R)) with hB
  have hBq : IsQuasisimple ↥B :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZΩ).symm hq
  have hZB : ∀ {C : matrixDerived (oQ R)}, C ∈ centralizer ({A} : Set (matrixDerived (oQ R))) →
      (C : GL (Fin (2 * n)) K) ∈ Z := by
    intro C hC
    refine ⟨?_, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hC))⟩
    have := matrixDerived_le_isometries (oQ R) C.2
    rwa [matrixIsometries_oQ h2 R hRs] at this
  have hBC : B ≤ centralizer ({A} : Set (matrixDerived (oQ R))) := by
    intro g hg
    have hgc : (g : GL (Fin (2 * n)) K) ∈ ⁅Z, Z⁆ := hg
    have hgZ : (g : GL (Fin (2 * n)) K) ∈ Z := commutator_le_self _ hgc
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hgZ).2
  have hBnorm : ∀ g ∈ centralizer ({A} : Set (matrixDerived (oQ R))), ∀ f ∈ B, g * f * g⁻¹ ∈ B := by
    intro g hg f hf
    have hgZ : (g : GL (Fin (2 * n)) K) ∈ Z := hZB hg
    have hfc : (f : GL (Fin (2 * n)) K) ∈ ⁅Z, Z⁆ := hf
    have hfZ : (f : GL (Fin (2 * n)) K) ∈ Z := commutator_le_self _ hfc
    have h1 : ⁅(g : GL (Fin (2 * n)) K), (f : GL (Fin (2 * n)) K)⁆ ∈ ⁅Z, Z⁆ :=
      commutator_mem_commutator hgZ hfZ
    have h3 : (g : GL (Fin (2 * n)) K) * f * (g : GL (Fin (2 * n)) K)⁻¹ ∈ ⁅Z, Z⁆ := by
      have := (⁅Z, Z⁆).mul_mem h1 hfc
      simpa [commutatorElement_def, mul_assoc] using this
    exact h3
  obtain ⟨D, hDq, hDC, hDsn⟩ := CFSG.RankThree.PartOne.exists_component_of_block (projH _)
    projH_surjective (by rw [QuotientGroup.ker_mk']; exact scalars_subgroupOf_le_center) A B hBq
    hBC hBnorm
  exact Or.inr ⟨D.subgroupOf (centralizer ({projH _ A} : Set _)),
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDC).symm hDq, hDsn⟩

theorem orth_dichotomy (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f)
    {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (x : StatedProj (matrixDerived (oQ R))) (hx : orderOf x = 2) :
    SolvableOrComponent (StatedProj (matrixDerived (oQ R))) x := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hxx : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
  obtain ⟨T, hT, rfl, hTsq⟩ := HarrisLit.T1.P51e.Orth.exists_lift_sq h2 (by omega) hR hxx
  rcases hTsq with hT2 | hT2
  ·
    have hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    obtain ⟨w, hw, J, hJ, θ, hJne, hJcne, -, hθ⟩ :=
      HarrisLit.T1.P51e.Orth.exists_sign_frame hK hR hT hT2 hT1
    refine solvableOrComponent_of_mulEquiv θ _ ?_
    rw [hθ]
    exact sign_dichotomy hK hw J hJ hJne hJcne
  ·
    have hdet := det_eq_one_of_mem_commutator (H := matrixIsometries (oQ R)) hT
    have hdodd : ¬ Odd d := by
      intro hodd
      have h1 := congrArg Matrix.det hT2
      rw [Matrix.det_mul, hdet, mul_one, Matrix.det_neg, Matrix.det_one, mul_one,
        Fintype.card_fin, hodd.neg_one_pow] at h1
      exact h2 (by linear_combination h1)
    obtain ⟨m, rfl⟩ : ∃ m, d = 2 * m := by
      rcases Nat.even_or_odd d with ⟨m, hm⟩ | h
      · exact ⟨m, by omega⟩
      · exact absurd h hdodd
    obtain ⟨R₁, A, θ, hR₁, hA, hθ⟩ := HarrisLit.T1.P51Q.exists_pc_model hK hR hT hT2
    refine solvableOrComponent_of_mulEquiv θ _ ?_
    rw [hθ]
    exact pc_dichotomy hK hp hKc (c := -1) (neg_ne_zero.mpr one_ne_zero) (by omega) hR₁ hA

end CFSG.ComponentClassification.CatFC.DS81
