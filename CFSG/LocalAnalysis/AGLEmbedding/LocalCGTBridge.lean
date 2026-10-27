module

public import CFSG.CGT.PushingUp.CampbellPair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridgeAux
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace LocalCGT

open CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem kProper_of_isKGroup {X : Type} [Group X] (h : CFSG.Open.IsKGroup X) :
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog X :=
  CFSG.KCore.KGroupNonab.kProperNonab h

theorem isCharacteristicP_of_charTwo {X : Subgroup G} (h : CharTwo X) :
    CFSG.IsCharacteristicP 2 ↥X := CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.mp h

theorem isSylowOf_of_isSylowTwoOf {T X : Subgroup G} (h : IsSylowTwoOf T X) :
    IsSylowOf 2 T X :=
  h

theorem open_isSubnormal_of_subgroupOf {K X : Subgroup G} (hKX : K ≤ X)
    (h : (K.subgroupOf X).IsSubnormal) : CFSG.Open.IsSubnormal K X :=
  (CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 h

variable [Finite G]

omit [Finite G] in
theorem ne_bot_of_isSylowTwoOf {X T : Subgroup G} (hchar : CharTwo X) (hT : IsSylowTwoOf T X)
    (hX : X ≠ ⊥) : T ≠ ⊥ := by
  rintro rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx⟩ := hT
  rw [Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
  have hP : IsPGroup 2 (pCoreOf 2 X) := by
    have h := CGT.PushingUpLit.isPGroup_oTwoIn X
    rwa [← NoXBlock.blockQ_eq_oTwoIn] at h
  have hPX : pCoreOf 2 X ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rcases hP.card_eq_or_dvd with h1 | h2
  · apply hX
    rw [eq_bot_iff]
    intro x hx
    have hbot : pCoreOf 2 X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hx' : x ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      rw [hbot]
      exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
        rw [hy, one_mul, mul_one]⟩
    have := hchar hx'
    rwa [hbot] at this
  · exact hidx (h2.trans (Subgroup.card_dvd_of_le hPX))

theorem centralizer_inf_le_cgsIn {X T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    Subgroup.centralizer (omegaOneCenterIn T : Set G) ⊓ X ≤ cgsIn X T := by
  refine le_trans ?_ (le_iSup_of_le (omegaOneCenterIn T)
    (le_iSup_of_le (CGT.PushingUp.omegaOneCenterIn_le T)
      (le_iSup_of_le (CGT.PushingUp.omegaOneCenterIn_ne_bot hT hT1)
        (le_iSup_of_le (CGT.PushingUp.characteristic_omegaOneCenterIn T) le_rfl))))
  rw [inf_comm]
  exact inf_le_inf_left X (Subgroup.centralizer_le_normalizer _)

theorem normalizer_inf_le_cgsIn {X T : Subgroup G} (B : Subgroup G) (hB : B ≠ ⊥)
    (hBS : B ≤ pushingUpS T) (hBc : (B.subgroupOf (pushingUpS T)).Characteristic) :
    Subgroup.normalizer (B : Set G) ⊓ X ≤ cgsIn X T := by
  have hST := CGT.PushingUp.pushingUpS_le T
  have hBT : (B.subgroupOf T).Characteristic :=
    CGT.PushingUp.characteristic_trans hBS hST hBc (CGT.PushingUp.characteristic_pushingUpS T)
  rw [inf_comm]
  exact le_iSup_of_le B (le_iSup_of_le (hBS.trans hST) (le_iSup_of_le hB
    (le_iSup_of_le hBT le_rfl)))

end LocalCGT

theorem aschbacherLocalCGTBlock_of_factorization
    (h : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization) : AschbacherLocalCGTBlock := by
  intro G _ _ X T hK hchar hT hne
  have hXM : ¬ X ≤ cgsIn X T := fun hle => hne (le_antisymm (cgsIn_le X T) hle)
  have hX : X ≠ ⊥ := by
    rintro rfl
    exact hne (le_antisymm (cgsIn_le ⊥ T) bot_le)
  have hT1 : T ≠ ⊥ := LocalCGT.ne_bot_of_isSylowTwoOf hchar hT hX
  obtain ⟨Y, ⟨hYX, hYs, hYx⟩, hYM⟩ := h.relative (LocalCGT.kProper_of_isKGroup hK)
    (LocalCGT.isCharacteristicP_of_charTwo hchar) (LocalCGT.isSylowOf_of_isSylowTwoOf hT)
    (LocalCGT.centralizer_inf_le_cgsIn hT.2.1 hT1) LocalCGT.normalizer_inf_le_cgsIn hXM
  exact ⟨Y, hYX, LocalCGT.open_isSubnormal_of_subgroupOf hYX hYs,
    LocalCGT.inClassXBlock_of_inClassX hYx, hYM⟩

end CFSG.AGLEmbedding
