module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

structure ExamConfig {G : Type} [Group G] (K B B' P R : Subgroup G) (m : ℕ) : Prop where
  two_le : 2 ≤ m
  quasisimple : CFSG.IsQuasisimple ↥K
  list : CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K)
  card_pCore : Nat.card (pCoreOf 2 K) ≤ 2
  le_K : B ≤ K
  le_K' : B' ≤ K
  short : IsShort2 B
  short' : IsShort2 B'
  lin2 : IsLin2Type B m
  lin2' : IsLin2Type B' m
  pCore : pCoreOf 2 B = blockU B
  pCore' : pCoreOf 2 B' = blockU B'
  card_Z : Nat.card (blockZ B) = 2 ^ m
  card_Z' : Nat.card (blockZ B') = 2 ^ m
  sylowP : IsSylowTwoOf P K
  R_le_P : R ≤ P
  sylowB : IsSylowTwoOf R B
  sylowB' : IsSylowTwoOf R B'
  R_eq : R = blockU B ⊔ blockU B'
  U_ne : blockU B ≠ blockU B'
  elem_le : ∀ E : Subgroup G, E ≤ R → IsElemAbelian 2 E → E ≤ blockU B ∨ E ≤ blockU B'
  strong : ∀ i ∈ R, i ^ 2 = 1 → ∀ g ∈ K, g⁻¹ * i * g ∈ P → g⁻¹ * i * g ∈ R
  card_R : Nat.card R = 2 ^ (4 * m)
  card_U : Nat.card (blockU B) = 2 ^ (3 * m)
  card_U' : Nat.card (blockU B') = 2 ^ (3 * m)
  center_inf_R : ∀ z ∈ Subgroup.center ↥K, (z : G) ∈ R → z = 1

@[expose] def Lemma2_4_23_five_examK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B B' P R : Subgroup G) (m : ℕ),
    ExamConfig K B B' P R m →
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
      Nonempty (↥K ≃* StatedProj (StatedSp 2 F))

end CFSG.QuasithinUnique.Lin2
