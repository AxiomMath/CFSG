module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.TwoThree

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {G : Type} [Group G]

structure A5Step1 (T M H S L : Subgroup G) : Prop where
  index_two : S.relIndex T = 2
  join_eq : H = L ⊔ baum S
  P_le : borelP M L ≤ S
  q8 : IsQ8Square (borelP M L)
  S_eq : S = borelP M L ⊔ baum S
  frattini_le : frattiniOf S ≤ borelP M L
  Z_card : Nat.card (centerOf (borelP M L)) = 2
  Z_eq : centerOf (borelP M L) = frattiniOf S ⊓ centerOf S
  Z_le : centerOf (borelP M L) ≤ centerOf T

structure A5Step2 (T M H S L : Subgroup G) : Prop extends A5Step1 T M H S L where
  M1_cent : T ⊔ borelK M L ≤ Subgroup.centralizer (centerOf (borelP M L) : Set G)
  PTC_norm : T ⊔ borelK M L ≤
    Subgroup.normalizer ((borelP M L ⊔ blockTC T S L : Subgroup G) : Set G)
  ZTC_eq : centerOf (borelP M L ⊔ blockTC T S L) = centerOf (borelP M L) ⊔ blockTC T S L
  TC_card : Nat.card (blockTC T S L) ≤ 2
  TC_comm : ∀ x ∈ T, x ∉ S → Nat.card (blockTC T S L) = 2 →
    ⁅Subgroup.zpowers x, blockTC T S L⁆ = centerOf (borelP M L)
  O2_cent : pCoreOf 2 (T ⊔ borelK M L) ≤
    Subgroup.centralizer ((centerOf (borelP M L) ⊔ blockTC T S L : Subgroup G) : Set G)
  H_cent : H ≤ Subgroup.centralizer (blockTC T S L : Set G)

structure A5Step3 (T M H S L : Subgroup G) : Prop extends A5Step2 T M H S L where
  o4 : ActsAsO4Plus (T ⊔ borelK M L) (borelP M L ⊔ blockTC T S L)
    (centerOf (borelP M L) ⊔ blockTC T S L)
  irred : ∀ W : Subgroup G, centerOf (borelP M L) ⊔ blockTC T S L ≤ W →
    W ≤ borelP M L ⊔ blockTC T S L → T ⊔ borelK M L ≤ Subgroup.normalizer (W : Set G) →
    W = centerOf (borelP M L) ⊔ blockTC T S L ∨ W = borelP M L ⊔ blockTC T S L
  U_not_le : ¬ blockU L ≤ pCoreOf 2 (T ⊔ borelK M L)

structure A5Step5 (T M H S L : Subgroup G) : Prop extends A5Step3 T M H S L where
  TC_one : blockTC T S L = ⊥
  Q_eq : pCoreOf 2 H = blockU L
  CU_eq : Subgroup.centralizer (blockU L : Set G) = blockU L
  CL_eq : Subgroup.centralizer (L : Set G) = ⊥
  L_normal : Subgroup.normalizer (blockU L : Set G) ≤ Subgroup.normalizer (L : Set G)

structure A5Step6 (T M H S L : Subgroup G) : Prop extends A5Step5 T M H S L where
  M_eq : M = T ⊔ borelK M L
  M_cent : M = Subgroup.centralizer (centerOf (borelP M L) : Set G)
  P_core : pCoreOf 2 M = borelP M L
  M_card : Nat.card M = 2 ^ 8 * 3 ^ 2
  M_solvable : Group.IsSolvable ↥M
  exists_u : ∃ u ∈ centerOf (baum S), u ∉ centerOf (borelP M L)

structure A5Step7 (T M H S L : Subgroup G) (z u : G) : Prop extends A5Step6 T M H S L where
  H_eq : H = Subgroup.normalizer (blockU L : Set G)
  z_gen : centerOf (borelP M L) = Subgroup.zpowers z
  u_mem : u ∈ centerOf (baum S)
  u_not : u ∉ centerOf (borelP M L)
  u_U : u ∈ blockU L
  s_exists : ∃ s ∈ S, s ∉ baum S ∧ z = u * (s⁻¹ * u * s)
  Hu : Nonempty (↥(H ⊓ centralizerElem u) ≃* DihedralGroup 4 × Equiv.Perm (Fin 4))
  Su : S ⊓ centralizerElem u = baum S
  R_index : (baum S).relIndex S = 2
  CU_card : Nat.card ↥(blockU L ⊓ Subgroup.centralizer
    (pResidualOf 2 (H ⊓ centralizerElem u) : Set G)) = 4
  CU_conj : ∀ v ∈ blockU L ⊓ Subgroup.centralizer
      (pResidualOf 2 (H ⊓ centralizerElem u) : Set G),
    v ≠ 1 → v ≠ u → ∃ l ∈ L, v = l⁻¹ * z * l
  ZR_eq : centerOf (baum S) = Subgroup.zpowers u ⊔ Subgroup.zpowers z
  ZR_norm : T ≤ Subgroup.normalizer (centerOf (baum S) : Set G)
  x_exists : ∃ x ∈ T, x ∉ S ∧ x ∈ centralizerElem u
  Tu_eq : T ⊓ centralizerElem u = M ⊓ centralizerElem u
  Tu_index : (T ⊓ centralizerElem u).relIndex T = 2
  Tu_sylow : IsSylowTwoOf (T ⊓ centralizerElem u) (centralizerElem u)
  u_not_conj : ∀ g : G, g⁻¹ * z * g ≠ u
  Gu_gamma2 : IsGamma2 M (centralizerElem u)

structure A5Step9 (T M H S L : Subgroup G) (z u : G) (K : Subgroup G) : Prop
    extends A5Step7 T M H S L z u where
  K_comp : IsComponentIn K (centralizerElem u)
  K_norm : centralizerElem u ≤ Subgroup.normalizer (K : Set G)
  RK_sylow : IsSylowTwoOf (baum S ⊓ K) K
  B_eq : centralizerElem u ⊓ Subgroup.centralizer (K : Set G) =
    baum S ⊓ Subgroup.centralizer (K : Set G)
  S6 : ∃ e : ↥K ≃* alternatingGroup (Fin 6),
    (∃ v ∈ baum S, v ∈ blockU L ∧ v ∉ Subgroup.zpowers u ∧
      ∃ τ : Equiv.Perm (Fin 6), τ.IsSwap ∧ InducesPerm e v τ) ∧
    ∀ r ∈ baum S, ∃ σ : Equiv.Perm (Fin 6), InducesPerm e r σ

structure A5Step10 (T M H S L : Subgroup G) (z u : G) (K : Subgroup G) : Prop
    extends A5Step9 T M H S L z u K where
  u_mem_P : u ∈ borelP M L
  IS_norm : M ≤ Subgroup.normalizer ((pResidualOf 2 M ⊔ S : Subgroup G) : Set G)
  IS_inf : T ⊓ (pResidualOf 2 M ⊔ S) = S
  trans_P : ∀ v ∈ borelP M L, ∀ w ∈ borelP M L, v ∉ centerOf (borelP M L) →
    w ∉ centerOf (borelP M L) → v ^ 2 = 1 → w ^ 2 = 1 → ∃ m ∈ M, m⁻¹ * v * m = w
  sl23_core : ∀ (Y : Subgroup G) (c : G), IsTwoThree Y c → Y ≤ M → c ∈ M →
    Y ≤ pCoreOf 2 M
  dichotomy : ∀ i ∈ M, i ∉ pResidualOf 2 M ⊔ S → i ^ 2 = 1 →
    (∃ (Y : Subgroup G) (c : G), IsTwoThree Y c ∧ Y ≤ Subgroup.centralizer ({i} : Set G) ∧
      c ∈ Subgroup.centralizer ({i} : Set G) ∧ z ∈ Y) ∨
    ∃ m ∈ M, m⁻¹ * i * m ∈ centralizerElem u
  j_exists : ∃ j ∈ T, j ∉ S ∧ j ^ 2 = z

@[expose] def Lemma2_4_29_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step1 T M H S L

@[expose] def Lemma2_4_29_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step1 T M H S L → A5Step2 T M H S L

@[expose] def Lemma2_4_29_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step2 T M H S L → A5Step3 T M H S L

@[expose] def Lemma2_4_29_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step3 T M H S L → blockTC T S L = ⊥

@[expose] def Lemma2_4_29_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step3 T M H S L → blockTC T S L = ⊥ → A5Step5 T M H S L

@[expose] def Lemma2_4_29_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step5 T M H S L → A5Step6 T M H S L

@[expose] def Lemma2_4_29_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    A5Step6 T M H S L → ∀ z u : G, centerOf (borelP M L) = Subgroup.zpowers z →
      u ∈ centerOf (baum S) → u ∉ centerOf (borelP M L) → A5Step7 T M H S L z u

@[expose] def Lemma2_4_29_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    ∀ z u : G, A5Step7 T M H S L z u → ¬ CharTwo (centralizerElem u)

@[expose] def Lemma2_4_29_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    ∀ z u : G, A5Step7 T M H S L z u → ¬ CharTwo (centralizerElem u) →
      ∃ K : Subgroup G, A5Step9 T M H S L z u K

@[expose] def Lemma2_4_29_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    ∀ (z u : G) (K : Subgroup G), A5Step9 T M H S L z u K → A5Step10 T M H S L z u K

@[expose] def Lemma2_4_29_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    ∀ (z u : G) (K : Subgroup G), A5Step10 T M H S L z u K → False

@[expose] def Lemma2_4_25_Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ t ∈ S, conjR L t ≠ L → s2Q1 S L ⊓ conjR (s2Q1 S L) t ≤ pCoreOf 2 H

@[expose] def Lemma2_4_25_0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∃ x : G, x ∈ T ∧ x ∈ Subgroup.normalizer (S : Set G) ∧ ¬ conjR (blockU L) x ≤ s2Q1 S L

structure A5s2A (T M H S L : Subgroup G) (x : G) : Prop where
  frat_x : conjR (frattiniOf (s2I S L)) x = frattiniOf (s2I S L)
  x_SI : x ∈ Subgroup.normalizer (s2SI S L : Set G)
  x_phi : x ∈ Subgroup.normalizer (s2Phi S L : Set G)
  phi_ne : s2Phi S L ≠ ⊥
  o3_cent : pElementsGen 3 (M ⊓ conjJoin S L) ≤ Subgroup.centralizer (s2Phi S L : Set G)
  SI_frat : s2SI S L = S ⊓ Subgroup.normalizer (frattiniOf (s2I S L) : Set G)
  SI_phi : s2SI S L = S ⊓ Subgroup.normalizer (s2Phi S L : Set G)
  SI_index : (s2SI S L).relIndex S = 2
  SI_conf : IsConfining M (s2SI S L)
  SI_pair : IsWitnessPair M (s2SI S L) (H ⊓ Subgroup.normalizer (s2Phi S L : Set G))
  GI_gamma : IsGamma M (Subgroup.normalizer (s2Phi S L : Set G))

structure A5s2B (T M H S L : Subgroup G) (x : G) : Prop extends A5s2A T M H S L x where
  Ux_inf : conjR (blockU L) x ⊓ pCoreOf 2 (Subgroup.normalizer (s2Phi S L : Set G)) = ⊥
  LSI_gamma : IsGamma M (L ⊔ s2SI S L)
  star : ∀ H₁ : Subgroup G, CharTwo H₁ → L ⊔ s2SI S L ≤ H₁ →
    H₁ ≤ Subgroup.normalizer (s2Phi S L : Set G) →
    (∃ S₁ : Subgroup G, IsSylowTwoOf S₁ H₁ ∧ s2SI S L ≤ S₁ ∧ H₁ = L ⊔ S₁) →
    quasithinIsCComponent L H₁

structure A5s2C (T M H S L : Subgroup G) (x : G) (K : Subgroup G) : Prop
    extends A5s2B T M H S L x where
  K_comp : IsComponentIn K (Subgroup.normalizer (s2Phi S L : Set G))
  L_le : L ≤ K
  K_list : Kc3Group (↥K ⧸ Subgroup.center ↥K)
  K_center : IsPGroup 2 ↥(Subgroup.center ↥K)
  local_all : ∀ T_I : Subgroup G, IsSylowTwoOf T_I (Subgroup.normalizer (s2Phi S L : Set G)) →
    s2SI S L ≤ T_I →
    T_I ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ X S₁ : Subgroup G, CharTwo X → L ⊔ s2SI S L ≤ X → X ≤ K ⊔ T_I → IsSylowTwoOf S₁ X →
        s2SI S L ≤ S₁ → quasithinIsLocal S₁ L

@[expose] def Lemma2_4_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L = L

@[expose] def Lemma2_4_25_A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ x : G, x ∈ T → x ∈ Subgroup.normalizer (S : Set G) →
      ¬ conjR (blockU L) x ≤ s2Q1 S L → A5s2A T M H S L x

@[expose] def Lemma2_4_25_B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ x : G, x ∈ T → x ∈ Subgroup.normalizer (S : Set G) →
      ¬ conjR (blockU L) x ≤ s2Q1 S L → A5s2A T M H S L x → A5s2B T M H S L x

@[expose] def Lemma2_4_25_C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ x : G, x ∈ T → x ∈ Subgroup.normalizer (S : Set G) →
      ¬ conjR (blockU L) x ≤ s2Q1 S L → A5s2B T M H S L x →
        ∃ K : Subgroup G, A5s2C T M H S L x K

@[expose] def Lemma2_4_25_D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ (x : G) (K : Subgroup G), A5s2C T M H S L x K → False

end CFSG.QuasithinUnique.A5
