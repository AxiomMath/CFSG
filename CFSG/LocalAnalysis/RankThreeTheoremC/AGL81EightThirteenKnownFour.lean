module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL44
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
import CFSG.RankThree.PartTwo.KFacts.KS21Sp64
import CFSG.RankThree.PartOne.Q1327C.BSp6Matrix
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNoTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Abs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPFrame
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AGEVCoverStar
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec20.Contra
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.RankThree.PartOne.KF.ClsBasic
import CFSG.RankThree.PartOne.KF.R10Final
import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.RankThree.PartOne.Q1327C.BBase
import CFSG.RankThree.PartOne.Q1327C.BDefs
import CFSG.RankThree.PartOne.Q1327C.BRows
import CFSG.RankThree.PartOne.Q1327C.P5Glue
import CFSG.RankThree.PartOne.S12.InputsKF2
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix

private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {X : Subgroup G} [Finite X]
    {g : G} (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  have hinj : Function.Injective (fun x : X => (⟨g * x * g⁻¹, h x x.2⟩ : X)) := fun a b hab =>
    Subtype.ext (by simpa using congrArg Subtype.val hab)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj ⟨_, hx⟩
  have hyx : (y : G) = x := by simpa using congrArg Subtype.val hy
  exact hyx ▸ y.2

section L44

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.SL44
open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4)

private theorem eq_top_of_transvection_mem {n : ℕ} {K : Type*} [Field K]
    {H : Subgroup (SpecialLinearGroup (Fin n) K)} (i : Fin n)
    (hA : ∀ {j : Fin n} (hij : i ≠ j) (c : K), SpecialLinearGroup.transvection hij c ∈ H)
    (hB : ∀ {j : Fin n} (hji : j ≠ i) (c : K), SpecialLinearGroup.transvection hji c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff,
    ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨⟨j, k, hjk, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  by_cases hj : j = i
  · subst hj
    exact hA hjk c
  by_cases hk : k = i
  · subst hk
    exact hB hjk c
  have hcomm := SpecialLinearGroup.commutatorElement_transvection hj (Ne.symm hk) hjk c (1 : K)
  rw [mul_one] at hcomm
  rw [← hcomm, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hB hj c) (hA (Ne.symm hk) 1))
    (H.inv_mem (hB hj c))) (H.inv_mem (hA (Ne.symm hk) 1))

private noncomputable abbrev slPlane (i j : Fin 4) : Subgroup (SpecialLinearGroup (Fin 4) F4) :=
  (ratio i j).ker.map diagSL

private theorem card_slPlane {i j : Fin 4} (hij : i ≠ j) : Nat.card (slPlane i j) = 3 ^ 2 := by
  rw [Subgroup.card_map_of_injective diagSL_injective, card_ker_ratio hij]
  norm_num

private theorem transvection_mem_normalizer_slPlane {i j a b : Fin 4} (hab : a ≠ b)
    (h : ∀ s : torus, ratio i j s = 1 → (s : Fin 4 → F4ˣ) a = (s : Fin 4 → F4ˣ) b) (c : F4) :
    SpecialLinearGroup.transvection hab c ∈ Subgroup.normalizer (slPlane i j : Set _) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
  rintro _ ⟨s, hs, rfl⟩
  exact Subtype.ext (transvection_mul_diagonal hab (congrArg Units.val (h s hs)) c).symm

local notation "σ₂₃" => Equiv.swap (2 : Fin 4) 3

private noncomputable def swapSL : SpecialLinearGroup (Fin 4) F4 :=
  ⟨Equiv.Perm.permMatrix F4 σ₂₃, by
    rw [det_permutation, Equiv.Perm.sign_swap (by decide)]
    simp [CharTwo.neg_eq]⟩

private theorem swapSL_mul_eq_mul_swapSL {A B : Matrix (Fin 4) (Fin 4) F4}
    (h : ∀ a b, A (σ₂₃ a) b = B a (σ₂₃ b)) :
    Equiv.Perm.permMatrix F4 σ₂₃ * A = B * Equiv.Perm.permMatrix F4 σ₂₃ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_swap]
  ext a b
  exact h a b

private theorem swapSL_mem_normalizer : swapSL ∈ Subgroup.normalizer (slPlane 0 1 : Set _) := by
  haveI : Finite (slPlane 0 1) :=
    Nat.finite_of_card_ne_zero (by rw [card_slPlane (by decide)]; norm_num)
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : torus, ∀ k, (s' : Fin 4 → F4ˣ) k = (s : Fin 4 → F4ˣ) (σ₂₃ k) :=
    ⟨⟨fun k => (s : Fin 4 → F4ˣ) (σ₂₃ k), mem_torus.2
      ((Equiv.prod_comp σ₂₃ fun k => (s : Fin 4 → F4ˣ) k).trans (mem_torus.1 s.2))⟩,
      fun _ => rfl⟩
  have hmul : swapSL * diagSL s = diagSL s' * swapSL := by
    refine Subtype.ext (swapSL_mul_eq_mul_swapSL (A := diagonal fun k => ((s : Fin 4 → F4ˣ) k : F4))
      (B := diagonal fun k => ((s' : Fin 4 → F4ˣ) k : F4)) fun a b => ?_)
    simp only [diagonal_apply, hs']
    by_cases hab : σ₂₃ a = b
    · rw [if_pos hab, if_pos (by rw [← hab, Equiv.swap_apply_self])]
    · rw [if_neg hab, if_neg fun h => hab (by rw [h, Equiv.swap_apply_self])]
  rw [hmul, mul_inv_cancel_right]
  refine ⟨s', ?_, rfl⟩
  have hs1 : ratio 0 1 s = 1 := hs
  have e0 : σ₂₃ 0 = 0 := by decide
  have e1 : σ₂₃ 1 = 1 := by decide
  change ratio 0 1 s' = 1
  rw [ratio_apply] at hs1 ⊢
  rw [hs', hs', e0, e1]
  exact hs1

private theorem swapSL_conj_transvection {a b a' b' : Fin 4} (hab : a ≠ b) (hab' : a' ≠ b')
    (ha : σ₂₃ a = a') (hb : σ₂₃ b = b') (c : F4) :
    swapSL * SpecialLinearGroup.transvection hab c * swapSL⁻¹ =
      SpecialLinearGroup.transvection hab' c := by
  subst ha hb
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (swapSL_mul_eq_mul_swapSL (A := 1 + single a b c)
    (B := 1 + single (σ₂₃ a) (σ₂₃ b) c) fun x y => ?_)
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Equiv.apply_eq_iff_eq,
    Equiv.swap_apply_eq_iff]

theorem threePlaneGen_SL44 : ThreePlaneGen (SpecialLinearGroup (Fin 4) (GaloisField 2 2)) := by
  refine ⟨D₀, slPlane 0 1, slPlane 0 2, 3, isElemAbelian_D₀, le_rfl,
    by rw [card_D₀]; norm_num, Subgroup.map_le_range _ _, card_slPlane (by decide),
    Subgroup.map_le_range _ _, card_slPlane (by decide), ?_⟩
  set H := Subgroup.normalizer (slPlane 0 1 : Set (SpecialLinearGroup (Fin 4) F4)) ⊔
    Subgroup.normalizer (slPlane 0 2 : Set (SpecialLinearGroup (Fin 4) F4))
  have hd : ∀ s : torus, ∀ i j : Fin 4, ratio i j s = 1 →
      (s : Fin 4 → F4ˣ) i = (s : Fin 4 → F4ˣ) j := fun s i j hs => by
    rwa [ratio_apply, mul_inv_eq_one] at hs
  have h1 : ∀ {a b : Fin 4} (hab : a ≠ b), (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) →
      ∀ c, SpecialLinearGroup.transvection hab c ∈ H := by
    rintro a b hab (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) c
    · exact Subgroup.mem_sup_left (transvection_mem_normalizer_slPlane hab
        (fun s hs => hd s 0 1 hs) c)
    · exact Subgroup.mem_sup_left (transvection_mem_normalizer_slPlane hab
        (fun s hs => (hd s 0 1 hs).symm) c)
  have h2 : ∀ {a b : Fin 4} (hab : a ≠ b), (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) →
      ∀ c, SpecialLinearGroup.transvection hab c ∈ H := by
    rintro a b hab (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) c
    · exact Subgroup.mem_sup_right (transvection_mem_normalizer_slPlane hab
        (fun s hs => hd s 0 2 hs) c)
    · exact Subgroup.mem_sup_right (transvection_mem_normalizer_slPlane hab
        (fun s hs => (hd s 0 2 hs).symm) c)
  have hsw : swapSL ∈ H := Subgroup.mem_sup_left swapSL_mem_normalizer
  have hconj : ∀ {a b a' b' : Fin 4} (hab : a ≠ b) (hab' : a' ≠ b'), σ₂₃ a = a' → σ₂₃ b = b' →
      ∀ c, SpecialLinearGroup.transvection hab c ∈ H →
        SpecialLinearGroup.transvection hab' c ∈ H :=
    fun hab hab' ha hb c h => by
      rw [← swapSL_conj_transvection hab hab' ha hb c]
      exact H.mul_mem (H.mul_mem hsw h) (H.inv_mem hsw)
  have hj : ∀ j : Fin 4, j ≠ 0 → j = 1 ∨ j = 2 ∨ j = 3 := by decide
  refine eq_top_of_transvection_mem 0 (fun {j} h0j c => ?_) (fun {j} hj0 c => ?_)
  · rcases hj j (Ne.symm h0j) with rfl | rfl | rfl
    · exact h1 h0j (.inl ⟨rfl, rfl⟩) c
    · exact h2 h0j (.inl ⟨rfl, rfl⟩) c
    · exact hconj (a := 0) (b := 2) (by decide) h0j (by decide) (by decide) c
        (h2 _ (.inl ⟨rfl, rfl⟩) c)
  · rcases hj j hj0 with rfl | rfl | rfl
    · exact h1 hj0 (.inr ⟨rfl, rfl⟩) c
    · exact h2 hj0 (.inr ⟨rfl, rfl⟩) c
    · exact hconj (a := 2) (b := 0) (by decide) hj0 (by decide) (by decide) c
        (h2 _ (.inr ⟨rfl, rfl⟩) c)

theorem threeCoreAt_L44 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 2 2)) :=
  threeCoreAt_of_threePlaneGen CFSG.RankThree.PartTwo.KFacts.KS21.L44.equivSL.symm
    threePlaneGen_SL44

end L44

section Sp64

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank

private theorem eq_top_of_basis_centers {r : ℕ} {K : Type} [Field K]
    {H : Subgroup (StatedSp r K)}
    (he : ∀ i, IsSpCenter H (Pi.single (Sum.inl i) 1))
    (hf : ∀ i, IsSpCenter H (Pi.single (Sum.inr i) 1))
    (hpair0 : ∀ i j, i ≠ j →
      IsSpCenter H (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1)) :
    H = ⊤ := by
  have hplane : ∀ i, ∀ c ∈ spPlane i, IsSpCenter H c := by
    intro i c hc
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hc
    by_cases hα : α = 0
    · rw [hα, zero_smul, zero_add]
      exact (hf i).smul β
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero]
      exact (he i).smul α
    refine ((he i).smul α).add ((hf i).smul β) ?_
    obtain ⟨-, -, c3, -⟩ := spForm_single_one_cases (K := K) i i
    simp [c3, hα, hβ]
  have he0 : ∀ k : Fin r, (Pi.single (Sum.inl k) 1 : Fin r ⊕ Fin r → K) ≠ 0 :=
    fun k h => one_ne_zero (Pi.single_eq_zero_iff.mp h)
  have hpair : ∀ i j, i ≠ j → ∀ y ∈ spPlane i, ∀ y' ∈ spPlane j, y ≠ 0 → y' ≠ 0 →
      IsSpCenter H (y + y') := by
    intro i j hij y hy y' hy' hy0 hy'0
    obtain ⟨g₁, hg₁, hg₁e, hg₁z⟩ := exists_mem_fixing_eq (nondegenerate_spPlane i) (hplane i)
      (single_inl_mem_spPlane i) hy (he0 i) hy0
    obtain ⟨g₂, hg₂, hg₂e, hg₂z⟩ := exists_mem_fixing_eq (nondegenerate_spPlane j) (hplane j)
      (single_inl_mem_spPlane j) hy' (he0 j) hy'0
    have h1 := ((hpair0 i j hij).map hg₁).map hg₂
    rwa [map_add, hg₁e, hg₁z _ fun c hc => spForm_eq_zero_of_mem_spPlane (Ne.symm hij)
      (single_inl_mem_spPlane j) hc, map_add, hg₂e,
      hg₂z _ fun c hc => spForm_eq_zero_of_mem_spPlane hij hy hc] at h1
  exact eq_top_of_isSpCenter (isSpCenter_of_pairs iSup_spPlane
    (fun i j hij u hu v hv => spForm_eq_zero_of_mem_spPlane hij hu hv) nondegenerate_spPlane
    hplane hpair)

private noncomputable abbrev spPlaneA : Subgroup (StatedSp 3 (GaloisField 2 2)) :=
  (Pi.evalMonoidHom (fun _ : Fin 3 => (GaloisField 2 2)ˣ) 0).ker.map torusHom

private noncomputable abbrev spPlaneB : Subgroup (StatedSp 3 (GaloisField 2 2)) :=
  (Pi.evalMonoidHom (fun _ : Fin 3 => (GaloisField 2 2)ˣ) 0 /
    Pi.evalMonoidHom (fun _ : Fin 3 => (GaloisField 2 2)ˣ) 1).ker.map torusHom

private theorem card_spPlaneA : Nat.card spPlaneA = 3 ^ 2 := by
  have h : 3 * Nat.card spPlaneA = 3 ^ 3 :=
    (three_mul_card_map_ker (r := 3)
      (φ := Pi.evalMonoidHom (fun _ : Fin 3 => (GaloisField 2 2)ˣ) 0)
      fun u => ⟨fun _ => u, rfl⟩).trans card_torus_gf4
  norm_num at h ⊢
  omega

private theorem card_spPlaneB : Nat.card spPlaneB = 3 ^ 2 := by
  have h : 3 * Nat.card spPlaneB = 3 ^ 3 :=
    (three_mul_card_map_ker (r := 3)
      (φ := Pi.evalMonoidHom (fun _ : Fin 3 => (GaloisField 2 2)ˣ) 0 /
        Pi.evalMonoidHom (fun _ : Fin 3 => (GaloisField 2 2)ˣ) 1)
      fun u => ⟨Pi.mulSingle 0 u, by
        rw [MonoidHom.div_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply,
          Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne' (by decide), div_one]⟩).trans
      card_torus_gf4
  norm_num at h ⊢
  omega

private theorem spTransvection_mem_normalizer_A {v : Fin 3 ⊕ Fin 3 → GaloisField 2 2}
    (hv : ∀ t : Fin 3 → (GaloisField 2 2)ˣ, t 0 = 1 → spEnd (torusHom t) v = v)
    (c : GaloisField 2 2) :
    spTransvection v c ∈ Subgroup.normalizer (spPlaneA : Set (StatedSp 3 (GaloisField 2 2))) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
  rintro _ ⟨t, ht, rfl⟩
  exact commute_spTransvection_of_fixed (hv t ht) c

private theorem spShortRoot_mem_normalizer_B (h01 : (0 : Fin 3) ≠ 1) :
    spShortRoot (K := GaloisField 2 2) 0 1 h01 ∈
      Subgroup.normalizer (spPlaneB : Set (StatedSp 3 (GaloisField 2 2))) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
  rintro _ ⟨t, ht, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.div_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply, div_eq_one] at ht
  exact torusHom_mul_spShortRoot h01 ht

private theorem rho01_mem_normalizer_B (h01 : (0 : Fin 3) ≠ 1) :
    rho (k := GaloisField 2 2) 0 1 h01 sl2W ∈
      Subgroup.normalizer (spPlaneB : Set (StatedSp 3 (GaloisField 2 2))) := by
  haveI : Finite spPlaneB := Nat.finite_of_card_ne_zero (by rw [card_spPlaneB]; norm_num)
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [CFSG.RankThree.PartOne.Q1327C.conj_rho01_torus h01]
  refine ⟨![t 1, t 0, t 2], ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.div_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply, div_eq_one] at ht ⊢
  exact ht.symm

private theorem conj_rho12_torus (h12 : (1 : Fin 3) ≠ 2) (t : Fin 3 → (GaloisField 2 2)ˣ) :
    rho 1 2 h12 sl2W * (torusHom t : StatedSp 3 (GaloisField 2 2)) * (rho 1 2 h12 sl2W)⁻¹ =
      torusHom ![t 0, t 2, t 1] := by
  have ht : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
    funext m
    fin_cases m <;> simp
  have h2 : (![t 0, t 2, t 1] : Fin 3 → (GaloisField 2 2)ˣ) =
      Pi.mulSingle 0 (t 0) * Pi.mulSingle 2 (t 1) * Pi.mulSingle 1 (t 2) := by
    funext m
    fin_cases m <;> simp
  rw [h2]
  conv_lhs => rw [ht]
  simp only [map_mul]
  rw [show ∀ A B C W : StatedSp 3 (GaloisField 2 2), W * (A * B * C) * W⁻¹ =
      (W * A * W⁻¹) * (W * B * W⁻¹) * (W * C * W⁻¹) from fun A B C W => by group]
  rw [CFSG.RankThree.PartOne.Q1327C.conj_rho_torus_single h12,
    CFSG.RankThree.PartOne.Q1327C.conj_rho_torus_single h12,
    CFSG.RankThree.PartOne.Q1327C.conj_rho_torus_single h12]
  have s0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have s1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have s2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
  rw [s0, s1, s2]

private theorem rho12_mem_normalizer_A (h12 : (1 : Fin 3) ≠ 2) :
    rho (k := GaloisField 2 2) 1 2 h12 sl2W ∈
      Subgroup.normalizer (spPlaneA : Set (StatedSp 3 (GaloisField 2 2))) := by
  haveI : Finite spPlaneA := Nat.finite_of_card_ne_zero (by rw [card_spPlaneA]; norm_num)
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [conj_rho12_torus h12]
  exact ⟨![t 0, t 2, t 1], ht, rfl⟩

private theorem spEnd_rho01 (h01 : (0 : Fin 3) ≠ 1) :
    spEnd (rho (k := GaloisField 2 2) 0 1 h01 sl2W) (Pi.single (Sum.inl 0) 1) =
        Pi.single (Sum.inl 1) 1 ∧
      spEnd (rho (k := GaloisField 2 2) 0 1 h01 sl2W) (Pi.single (Sum.inr 0) 1) =
        Pi.single (Sum.inr 1) 1 ∧
      spEnd (rho (k := GaloisField 2 2) 0 1 h01 sl2W) (Pi.single (Sum.inl 2) 1) =
        Pi.single (Sum.inl 2) 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [spEnd_apply, coe_rho', coe_sl2W, coe_sl2W_inv, mulVec_single_one] <;>
    funext y <;> rcases y with y | y <;> fin_cases y <;> simp [pairMat, Pi.single_apply]

private theorem spEnd_rho12 (h12 : (1 : Fin 3) ≠ 2) :
    spEnd (rho (k := GaloisField 2 2) 1 2 h12 sl2W) (Pi.single (Sum.inl 1) 1) =
        Pi.single (Sum.inl 2) 1 ∧
      spEnd (rho (k := GaloisField 2 2) 1 2 h12 sl2W) (Pi.single (Sum.inr 1) 1) =
        Pi.single (Sum.inr 2) 1 ∧
      spEnd (rho (k := GaloisField 2 2) 1 2 h12 sl2W) (Pi.single (Sum.inl 0) 1) =
        Pi.single (Sum.inl 0) 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [spEnd_apply, coe_rho', coe_sl2W, coe_sl2W_inv, mulVec_single_one] <;>
    funext y <;> rcases y with y | y <;> fin_cases y <;> simp [pairMat, Pi.single_apply]

theorem threePlaneGen_Sp64 : ThreePlaneGen (StatedSp 3 (GaloisField 2 2)) := by
  refine ⟨torus 3 (GaloisField 2 2), spPlaneA, spPlaneB, 3, isElemAbelian_torus_gf4, le_rfl,
    card_torus_gf4, Subgroup.map_le_range _ _, card_spPlaneA, Subgroup.map_le_range _ _,
    card_spPlaneB, ?_⟩
  set H := Subgroup.normalizer (spPlaneA : Set (StatedSp 3 (GaloisField 2 2))) ⊔
    Subgroup.normalizer (spPlaneB : Set (StatedSp 3 (GaloisField 2 2)))
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have he0 : IsSpCenter H (Pi.single (Sum.inl 0) 1) := fun c => Subgroup.mem_sup_left
    (spTransvection_mem_normalizer_A (fun t ht => by
      rw [spEnd_torusHom_inl, ht, Units.val_one, one_smul]) c)
  have hf0 : IsSpCenter H (Pi.single (Sum.inr 0) 1) := fun c => Subgroup.mem_sup_left
    (spTransvection_mem_normalizer_A (fun t ht => by
      rw [spEnd_torusHom_inr, ht, inv_one, Units.val_one, one_smul]) c)
  have hw01 : rho (k := GaloisField 2 2) 0 1 h01 sl2W ∈ H :=
    Subgroup.mem_sup_right (rho01_mem_normalizer_B h01)
  have hw12 : rho (k := GaloisField 2 2) 1 2 h12 sl2W ∈ H :=
    Subgroup.mem_sup_left (rho12_mem_normalizer_A h12)
  have hx01 : spShortRoot (K := GaloisField 2 2) 0 1 h01 ∈ H :=
    Subgroup.mem_sup_right (spShortRoot_mem_normalizer_B h01)
  obtain ⟨r0, r0f, r02⟩ := spEnd_rho01 h01
  obtain ⟨r1, r1f, r10⟩ := spEnd_rho12 h12
  have he1 : IsSpCenter H (Pi.single (Sum.inl 1) 1) := by
    have h := he0.map hw01
    rwa [r0] at h
  have hf1 : IsSpCenter H (Pi.single (Sum.inr 1) 1) := by
    have h := hf0.map hw01
    rwa [r0f] at h
  have he2 : IsSpCenter H (Pi.single (Sum.inl 2) 1) := by
    have h := he1.map hw12
    rwa [r1] at h
  have hf2 : IsSpCenter H (Pi.single (Sum.inr 2) 1) := by
    have h := hf1.map hw12
    rwa [r1f] at h
  have p01 : IsSpCenter H (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 1) 1) := by
    have h := he0.map hx01
    rwa [spEnd_spShortRoot] at h
  have p02 : IsSpCenter H (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 2) 1) := by
    have h := p01.map hw12
    rwa [map_add, r10, r1] at h
  have p12 : IsSpCenter H (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inl 2) 1) := by
    have h := p02.map hw01
    rwa [map_add, r0, r02] at h
  have hi : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have hij : ∀ i j : Fin 3, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
      (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide
  refine eq_top_of_basis_centers (fun i => ?_) (fun i => ?_) fun i j hne => ?_
  · rcases hi i with rfl | rfl | rfl
    · exact he0
    · exact he1
    · exact he2
  · rcases hi i with rfl | rfl | rfl
    · exact hf0
    · exact hf1
    · exact hf2
  · rcases hij i j hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact p01
    · exact p02
    · exact p12
    · rw [add_comm]
      exact p01
    · rw [add_comm]
      exact p02
    · rw [add_comm]
      exact p12

theorem threeCoreAt_Sp64 :
    ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSp 3 (GaloisField 2 2)) :=
  threeCoreAt_of_threePlaneGen CFSG.RankThree.PartTwo.KFacts.KS21.Sp64.equivSp.symm
    threePlaneGen_Sp64

end Sp64

end CFSG.LocalAnalysis.RankThreeTheoremC
