module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def tyFLin (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .A r q => r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card - 1
    | _ => False

@[expose] def tyFUni (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .twistedA r q => r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card + 1
    | _ => False

theorem tyFLin_or_tyFUni {p : ℕ} {i : TauCeti.CFSGIndex} (h : tyF p i) :
    tyFLin p i ∨ tyFUni p i := by
  rcases i with _ | _ | ⟨⟨l, hl⟩⟩ | _
  · exact (h : False).elim
  · exact (h : False).elim
  · cases l <;> first | exact Or.inl h | exact Or.inr h
  · exact (h : False).elim

theorem catalogIs_tyF {X : Type} [Group X] {p : ℕ} (h : catalogIs X (tyF p)) :
    catalogIs X (tyFLin p) ∨ catalogIs X (tyFUni p) := by
  obtain ⟨i, hi, he⟩ := h
  exact (tyFLin_or_tyFUni hi).imp (fun h => ⟨i, h, he⟩) fun h => ⟨i, h, he⟩

@[expose] def QSFamF5U : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL p S B T x D K → p = 5 → catalogIs (PSimple p K) (tyFUni p) → QSConcl p S B D K

@[expose] def QSFamF3 : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL p S B T x D K → p = 3 → catalogIs (PSimple p K) (tyF p) → QSConcl p S B D K

namespace SF

open CFSG.StandardType

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem pow_mul_card_le_of_torusLift {p r : ℕ} (hp : p.Prime) {K D : Subgroup Ω}
    (hK : commutator ↥K = ⊤) {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hT : GGTorusLift p r R) (hD : IsElemAbelian p D)
    (hDC : D ≤ Subgroup.centralizer (K : Set Ω)) :
    p ^ r * Nat.card D ≤ p ^ GLATwoLocalRank p Ω := by
  have hcomm : ∀ d ∈ D, ∀ k ∈ K, k * d = d * k := fun d hd k hk =>
    Subgroup.mem_centralizer_iff.1 (hDC hd) k hk
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, hEker⟩ := hT K (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hK
  rw [ker_ggQuotHom] at hEker
  have hdisj : Disjoint (E.map K.subtype) D := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ hD
    have hec : e ∈ E ⊓ Subgroup.center ↥K := ⟨he, Subgroup.mem_center_iff.2 fun l =>
      Subtype.ext (hcomm _ hD l l.2)⟩
    rw [hEker, Subgroup.mem_bot] at hec
    rw [hec, map_one]
  have hDN : D ≤ Subgroup.normalizer ((E.map K.subtype : Subgroup Ω) : Set Ω) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => by
      obtain ⟨e, -, rfl⟩ := hg
      exact hcomm d hd e e.2)
  have hcard : Nat.card (E.map K.subtype ⊔ D : Subgroup Ω) = p ^ r * Nat.card D := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hDN hdisj,
      Subgroup.card_map_of_injective K.subtype_injective, hEcard]
  have hel : IsElemAbelian p (E.map K.subtype ⊔ D) := by
    refine IsElemAbelian.sup_of_commute (hE.map K.subtype) hD ?_
    rintro _ ⟨e, -, rfl⟩ d hd
    exact hcomm d hd e e.2
  have hUne : U.map K.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
    exact hU
  have hle : E.map K.subtype ⊔ D ≤
      Subgroup.normalizer ((U.map K.subtype : Subgroup Ω) : Set Ω) := by
    refine sup_le ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)) fun d hd => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => by
      obtain ⟨u, -, rfl⟩ := hg
      exact hcomm d hd u u.2)
  have h1 := card_le_pow_glaTwoLocalRank hp hel hUne (hU2.map _) hle
  rwa [hcard] at h1

theorem pow_add_two_le_card_of_torusLift {p : ℕ} {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL p S B T x D K) {R : Type} [Group R]
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) {r : ℕ} (hT : GGTorusLift p r R) :
    p ^ (r + 2) ≤ Nat.card B := by
  obtain ⟨-, hDel, hDcard, -, -, hKcomp, hDK⟩ := h.cfg.std
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hDC : D ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [hDK]
    exact inf_le_right
  have h1 := pow_mul_card_le_of_torusLift h.cfg.prime hKq.1 θ hT hDel hDC
  rw [hDcard, ← pow_add] at h1
  exact h1.trans h.cfg.rank

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
