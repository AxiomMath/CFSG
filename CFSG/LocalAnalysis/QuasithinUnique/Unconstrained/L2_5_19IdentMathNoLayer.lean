module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayerCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Id2519.MathNoLayer

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Certificates CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Spec

variable {n : ℕ}

theorem tblEq_symm' {S T : Table} (h : tblEq n S T = true) : tblEq n T S = true := by
  rw [tblEq_iff] at h ⊢
  exact fun i hi => (h i hi).symm

theorem exists_mem_memT {L : List Table} {x : Table} (h : memT n x L = true) :
    ∃ y ∈ L, tblEq n x y = true := by
  simpa [memT] using h

theorem exists_normal_selfcentralizing (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (E : List Table) (h : noLayerOK n E (allTables Q) = true) :
    ∃ F : Subgroup (Equiv.Perm (Fin n)), F ≤ Q.originalSubgroup ∧
      (∀ q ∈ Q.originalSubgroup, ∀ e ∈ F, q * e * q⁻¹ ∈ F) ∧ (∀ e ∈ F, e ^ 4 = 1) ∧
      ∀ q ∈ Q.originalSubgroup, (∀ e ∈ F, q * e = e * q) → q ∈ F := by
  simp only [noLayerOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hid, hEK⟩, hEcl⟩, hnorm⟩, hcent⟩, hpow⟩ := h
  have hA := forall₂_allTables hn Q
  have hmem : ∀ g, g ∈ (enumeration Q).reverse ↔ g ∈ Q.originalSubgroup := fun g => by
    rw [List.mem_reverse, mem_enumeration_iff Q hQ]
  have hKrep : ∀ q ∈ Q.originalSubgroup, ∃ T ∈ allTables Q, Rep n T q := fun q hq => by
    obtain ⟨T, hT, hTq⟩ := exists_mem_of_forall₂_left hA q ((hmem q).2 hq)
    exact ⟨T, hT, hTq⟩
  have hErep : ∀ T ∈ E, ∃ g ∈ Q.originalSubgroup, Rep n T g := fun T hT => by
    obtain ⟨k, hk, hTk⟩ := exists_mem_memT (hEK T hT)
    obtain ⟨g, hg, hkg⟩ := exists_mem_of_forall₂_right hA k hk
    exact ⟨g, (hmem g).1 hg, rep_of_tblEq hkg hTk⟩
  let S : Set (Equiv.Perm (Fin n)) := {g | ∃ T ∈ E, Rep n T g}
  have hSmul : ∀ {g g' : Equiv.Perm (Fin n)}, g ∈ S → g' ∈ S → g * g' ∈ S := by
    rintro g g' ⟨T, hT, hTg⟩ ⟨T', hT', hTg'⟩
    obtain ⟨T'', hT'', heq⟩ := exists_mem_memT ((hEcl T hT).2 T' hT')
    exact ⟨T'', hT'', rep_of_tblEq (Rep.compT hTg hTg') (tblEq_symm' heq)⟩
  have hSinv : ∀ {g : Equiv.Perm (Fin n)}, g ∈ S → g⁻¹ ∈ S := by
    rintro g ⟨T, hT, hTg⟩
    obtain ⟨hio, hmem'⟩ := (hEcl T hT).1
    obtain ⟨T', hT', heq⟩ := exists_mem_memT hmem'
    exact ⟨T', hT', rep_of_tblEq (Rep.inv_of_invOK hTg hio) (tblEq_symm' heq)⟩
  have hS1 : (1 : Equiv.Perm (Fin n)) ∈ S := by
    obtain ⟨T, hT, heq⟩ := exists_mem_memT hid
    exact ⟨T, hT, rep_of_tblEq (Rep.idT hn) (tblEq_symm' heq)⟩
  let F : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := S
      mul_mem' := fun ha hb => hSmul ha hb
      one_mem' := hS1
      inv_mem' := fun ha => hSinv ha }
  have hFS : ∀ g, g ∈ F ↔ ∃ T ∈ E, Rep n T g := fun g => Iff.rfl
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨T, hT, hTg⟩ := (hFS g).1 hg
    obtain ⟨g', hg', hTg'⟩ := hErep T hT
    rw [rep_unique hTg hTg']
    exact hg'
  · intro q hq e he
    obtain ⟨Tq, hTq, hTqq⟩ := hKrep q hq
    obtain ⟨T, hT, hTe⟩ := (hFS e).1 he
    obtain ⟨hqi, hqe⟩ := hnorm Tq hTq
    obtain ⟨T', hT', heq⟩ := exists_mem_memT (hqe T hT)
    have hrep := Rep.compT (Rep.compT hTqq hTe) (Rep.inv_of_invOK hTqq hqi)
    exact (hFS _).2 ⟨T', hT', rep_of_tblEq hrep (tblEq_symm' heq)⟩
  · intro e he
    obtain ⟨T, hT, hTe⟩ := (hFS e).1 he
    have h4 := hpow T hT
    have hrep := Rep.powT hn hTe 4
    have h1 : Rep n (powT n 4 T) (1 : Equiv.Perm (Fin n)) := rep_of_tblEq (Rep.idT hn) h4
    exact rep_unique hrep h1
  · intro q hq hqc
    obtain ⟨Tq, hTq, hTqq⟩ := hKrep q hq
    have hc := hcent Tq hTq
    by_cases hall : (E.all fun e => commT n Tq e) = true
    · rw [hall] at hc
      obtain ⟨T', hT', heq⟩ := exists_mem_memT (by simpa using hc)
      exact (hFS q).2 ⟨T', hT', rep_of_tblEq hTqq (tblEq_symm' heq)⟩
    · exfalso
      apply hall
      refine List.all_eq_true.2 fun T hT => ?_
      obtain ⟨g, hg, hTg⟩ := hErep T hT
      have hgF : g ∈ F := (hFS g).2 ⟨T, hT, hTg⟩
      exact (commT_iff hTqq hTg).2 (hqc g hgF)

end Spec

section NoComponent

theorem noComponent_of_normal_selfcentralizing {M : Type*} [Group M] [Finite M] {K F : Subgroup M}
    (hFK : F ≤ K) (hn : ∀ q ∈ K, ∀ e ∈ F, q * e * q⁻¹ ∈ F) (hp : ∀ e ∈ F, e ^ 4 = 1)
    (hc : ∀ q ∈ K, (∀ e ∈ F, q * e = e * q) → q ∈ F) (B : Subgroup ↥K) :
    ¬ CFSG.IsComponent B := by
  intro hB
  have hUn : (F.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFK]
    intro e q he hq
    exact hn q hq e he
  have hUp : IsPGroup 2 ↥(F.subgroupOf K) := fun x => ⟨2, by
    apply Subtype.ext
    apply Subtype.ext
    have := hp _ x.2
    simpa using this⟩
  have hUs : Group.IsSolvable ↥(F.subgroupOf K) := by
    have : Group.IsNilpotent ↥(F.subgroupOf K) := hUp.isNilpotent
    infer_instance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hUs hUn.isSubnormal).1 B hB
  have hBF : ∀ b : ↥B, (((b : ↥K)) : M) ∈ F := by
    intro b
    apply hc _ (b : ↥K).2
    intro e he
    have hmem : ⁅(b : ↥K), (⟨e, hFK he⟩ : ↥K)⁆ ∈ ⁅B, F.subgroupOf K⁆ :=
      Subgroup.commutator_mem_commutator b.2 (Subgroup.mem_subgroupOf.mpr he)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  have hBp : IsPGroup 2 ↥B := fun x => ⟨2, by
    apply Subtype.ext
    apply Subtype.ext
    have := hp _ (hBF x)
    simpa using this⟩
  have hBs : Group.IsSolvable ↥B := by
    have : Group.IsNilpotent ↥B := hBp.isNilpotent
    infer_instance
  have : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
  have : Group.IsPerfect ↥B := hB.1.1
  exact Group.IsPerfect.not_isSolvable ↥B hBs

end NoComponent

section Orders

theorem not_hasKComponent_of_dvd {K : Type*} [Group K] [Finite K] {N : ℕ} (hN : Nat.card K ∣ N)
    (h168 : ¬ 168 ∣ N) (h360 : ¬ 360 ∣ N)
    (hp : ∀ p : ℕ, 17 ≤ p → ¬ p * (p * p - 1) ∣ 2 * N) : ¬ HasKComponent K := by
  rintro ⟨B, -, hKB⟩
  have hd : Nat.card ↥B ∣ N := (Subgroup.card_subgroup_dvd_card B).trans hN
  rcases hKB with h | h | ⟨p, hFM, h7, hpB⟩
  · rw [h] at hd
    exact h168 hd
  · rw [h] at hd
    exact h360 hd
  · exact hp p (seventeen_le_of_isFermatOrMersenne hFM h7) (by
      rw [hpB]
      exact Nat.mul_dvd_mul_left 2 hd)

theorem big_p_not_dvd {N : ℕ} (hN : N ≤ 7680) (hN0 : 0 < N)
    (hsmall : ∀ p : ℕ, 17 ≤ p → p ≤ 25 → ¬ p * (p * p - 1) ∣ 2 * N) :
    ∀ p : ℕ, 17 ≤ p → ¬ p * (p * p - 1) ∣ 2 * N := by
  intro p hp
  by_cases hp25 : p ≤ 25
  · exact hsmall p hp hp25
  · intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    have h26 : 26 * (26 * 26 - 1) ≤ p * (p * p - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.mul_le_mul (by omega) (by omega)) 1)
    omega

end Orders

section Cover

@[expose] def NoK {M : Type*} [Group M] (K : Subgroup M) : Prop := ¬ HasKComponent ↥K

theorem NoK.map_conj {M : Type*} [Group M] {K : Subgroup M} (h : NoK K) (s : M) :
    NoK (K.map (MulAut.conj s).toMonoidHom) := fun hk =>
  h (hk.of_mulEquiv (K.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).symm)

theorem centralizer_noK_of_reps {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup ∧ NoK d.2) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      NoK (centralizerIn Q.originalSubgroup u) := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard, hKP⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  rw [centralizerIn_conj _ hc, hcent]
  exact hKP.map_conj c

theorem outer_noK_of_witness {M : Type*} [Group M] (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N)
    (hw : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → NoK (centralizerIn N u))
    (α : MulAut N) (hα2 : α * α = 1) (hα : α ∉ inner N) : ¬ HasKComponent ↥(fixSub α) := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hmap := map_fixSub_conjOn N α u hαg
  intro hk
  exact hw u hu ho (hk.of_mulEquiv ((Subgroup.equivMapOfInjective (fixSub α) N.subtype
    N.subtype_injective).trans (MulEquiv.subgroupCongr hmap)))

end Cover

end CFSG.QuasithinUnique.Id2519.MathNoLayer
