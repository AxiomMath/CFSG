module

public import CFSG.LocalAnalysis.QuasithinUnique.ComponentEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocal
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Certificate113
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.ComponentClassification OuterAutomorphisms

namespace ComponentEmbedding

theorem statedClassicalModel_psl_two_of_four_le (G : Type) [Group G] (p k : ℕ) [Fact p.Prime]
    (h4 : 4 ≤ p ^ k)
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p k := by
  have hp : p.Prime := Fact.out
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h4
  refine ⟨⟨hp, Nat.one_le_iff_ne_zero.mpr hk, le_rfl, ?_, ?_⟩,
    GaloisField p k, inferInstance, inferInstance, GaloisField.card p k hk,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField p k))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem outer_solvable_of_fusionIsBenderGroup {X : Type} [Group X]
    (h : CFSG.Open.fusionIsBenderGroup X) : Group.IsSolvable (Outer X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact (LocalAnalysis.ComponentInitial.UnitaryHigher.linear_two_classical_model_schreier
      (statedClassicalModel_psl_two_of_four_le X 2 f h4 e)).2
  ·
    have hc : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
      rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, Nat.mul_comm]
    let eC : CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) (GaloisField 2 (2 * f)) (2 ^ f)) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
      MulEquiv.refl _
    have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f :=
      ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible f hf, GaloisField 2 (2 * f),
        inferInstance, inferInstance, hc,
        ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm).trans eC⟩⟩
    exact (LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier hmodel).2
  ·
    have hmodel : CFSG.Blueprint.SuzukiModel X 2 (2 * a + 1) :=
      ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
        GaloisField.card 2 (2 * a + 1) (by omega),
        ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSzCanonicalEquivNative a).symm).trans
          (MulEquiv.subgroupCongr
            (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1)))).symm⟩⟩
    exact (LocalAnalysis.ComponentInitial.Suzuki_model_Schreier X 2 (2 * a + 1) hmodel).2

theorem outer_center_quotient_solvable {X : Type*} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) [Group.IsSolvable (Outer X)] :
    Group.IsSolvable (Outer (X ⧸ Subgroup.center X)) := by
  have hcb : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  let e : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hcb.symm)
  exact solvable_of_equiv e

end ComponentEmbedding

theorem componentSchreier_of_localComponentRecognition
    (hrec : LocalComponentRecognition) :
    ComponentSchreier := by
  intro G _ _ T M U z hd v hv hv1 _ K hK
  have hUp : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hd.elem.2 x x.2)⟩
  have hUC : U ≤ Subgroup.centralizer ({v} : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hd.elem.1.is_comm.comm ⟨a, ha⟩ ⟨v, hv⟩)
  by_cases hM : Subgroup.centralizer ({v} : Set G) ≤ M
  · exfalso
    have hchar : CharTwo (Subgroup.centralizer ({v} : Set G)) := by
      have hvM : v ∈ M := hd.setting.le (hd.le_T hv)
      have hX : Subgroup.zpowers v ≤ M := Subgroup.zpowers_le.mpr hvM
      have hXp : IsPGroup 2 (Subgroup.zpowers v) := hUp.to_le (Subgroup.zpowers_le.mpr hv)
      have h := hd.setting.charTwo.inf_centralizer hX hXp
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm] at h
      rwa [inf_eq_left.mpr hM] at h
    have hlayer := CFSG.layer_eq_bot_of_isCharacteristicP (Subgroup.centralizer ({v} : Set G)) 2
      (EscapingLocal.isCharacteristicP_of_charTwo hchar)
    have h1 : K.subgroupOf (Subgroup.centralizer ({v} : Set G)) ≤
        CFSG.layer (Subgroup.centralizer ({v} : Set G)) := le_sSup hK.2
    rw [hlayer, le_bot_iff] at h1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hK.2.1) h1
  · obtain ⟨S, hS, hUS⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUC hUp
    obtain ⟨hsimple, hnonab, hbender, -⟩ := hrec G T M U z hd v hv hv1 hM S hS hUS K hK
    have : Group.IsSolvable (Outer K) :=
      ComponentEmbedding.outer_solvable_of_fusionIsBenderGroup hbender
    exact ComponentEmbedding.outer_center_quotient_solvable hnonab

theorem componentEmbeddingUnderInvolution_of_localComponentRecognition
    (hrec : LocalComponentRecognition) : ComponentEmbeddingUnderInvolution :=
  componentEmbeddingUnderInvolution_of_schreier (componentSchreier_of_localComponentRecognition hrec)

end CFSG.QuasithinUnique
