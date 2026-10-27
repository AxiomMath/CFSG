module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
public import CFSG.Open.StatedDefs

import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem nonempty_psl2_card_four_mulEquiv_alt_five_gl2 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := K) (CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact @CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _
    _ _ hsimple hcard

private noncomputable def catEquivProjectiveSL_gl2 {m : ℕ} {k : Type} [Field k] [Finite k]
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 0 < e) (hkc : Nat.card k = ℓ ^ e)
    (hv : (TauCeti.LieTypeIndex.A m ⟨ℓ, e, hℓ, he⟩).Valid) :
    (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A m ⟨ℓ, e, hℓ, he⟩, hv⟩).Group ≃*
      projectiveSL (m + 1) k := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := Fintype.ofFinite k
  haveI := Fintype.ofFinite (GaloisField ℓ e)
  have hcard : Fintype.card (GaloisField ℓ e) = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card ℓ e he.ne', hkc]
  exact ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m ⟨ℓ, e, hℓ, he⟩ hv).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      (m + 1) _)).trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcard))

private theorem nonempty_projectiveSL_mulEquiv_lie_gl2 {n : ℕ} {k : Type} [Field k] [Finite k]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A n q).Valid)
    (hk : Nat.card k = q.card) :
    Nonempty (projectiveSL (n + 1) k ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group) := by
  obtain ⟨p, e, hp, he⟩ := q
  have hq : Nat.card k = p ^ e := hk.trans (TauCeti.PrimePower.card_def ⟨p, e, hp, he⟩)
  exact ⟨(catEquivProjectiveSL_gl2 (m := n) (k := k) (ℓ := p) (e := e) hp he hq hv).symm⟩

private noncomputable def centerQuotientEquivPSL2_gl2 {K : Type} [Group K] {F : Type} [Field F]
    (e : K ≃* ↥(CFSG.Open.StatedSL 2 F)) :
    K ⧸ Subgroup.center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.congr (Subgroup.center K)
    ((CFSG.Open.StatedScalars (Fin 2) F).subgroupOf (CFSG.Open.StatedSL 2 F)) e
    ((Subgroup.map_center_eq e).trans <|
      (Subgroup.map_center_eq
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)).symm.trans
        (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 F))).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm

private theorem valid_A_one_two_pow_gl2 {m : ℕ} (hm0 : 0 < m) (hm : 2 < m) :
    (TauCeti.LieTypeIndex.A 1 (⟨2, m, Nat.prime_two, hm0⟩ : TauCeti.PrimePower)).Valid := by
  let q : TauCeti.PrimePower := ⟨2, m, Nat.prime_two, hm0⟩
  change (TauCeti.LieTypeIndex.A 1 q).Valid
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  have hqcard : q.card = 2 ^ m := TauCeti.PrimePower.card_def q
  have h8raw : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h8 : 8 ≤ q.card := hqcard ▸ h8raw
  have hne : ¬ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9) := by
    rw [hqcard]
    rintro (h | h | h)
    · have hm2 : m = 2 :=
        (Nat.pow_right_inj (by norm_num : 1 < 2)).mp
          (h.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
      omega
    · have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega : m ≠ 0)
      rw [h] at h2
      norm_num at h2
    · have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega : m ≠ 0)
      rw [h] at h2
      norm_num at h2
  refine ⟨⟨le_rfl, fun _ => by omega⟩, ?_⟩
  rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
  · exact hne h
  · omega
  · omega

theorem isGomiL2_of_mulEquiv_statedSL {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    {m : ℕ} (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) (e : K ≃* ↥(CFSG.Open.StatedSL 2 F)) :
    IsGomiL2 (K ⧸ Subgroup.center K) := by
  have hφ := centerQuotientEquivPSL2_gl2 e
  rcases lt_or_eq_of_le hm with hm3 | hm2
  · have hm0 : 0 < m := by omega
    let q : TauCeti.PrimePower := ⟨2, m, Nat.prime_two, hm0⟩
    have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := valid_A_one_two_pow_gl2 hm0 hm3
    refine Or.inr ⟨⟨TauCeti.LieTypeIndex.A 1 q, hv⟩, ⟨q, rfl, rfl⟩, ?_⟩
    have hqcard : q.card = 2 ^ m := TauCeti.PrimePower.card_def q
    obtain ⟨e₃⟩ := nonempty_projectiveSL_mulEquiv_lie_gl2 q hv (hF.trans hqcard.symm)
    exact ⟨hφ.trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        2 F).trans e₃)⟩
  · have h4 : Nat.card F = 4 := by
      rw [hF, ← hm2]
      norm_num
    obtain ⟨e₂⟩ := nonempty_psl2_card_four_mulEquiv_alt_five_gl2 h4
    exact Or.inl ⟨hφ.trans e₂⟩

end CFSG.GroupTheory
