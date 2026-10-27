module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95AssemblyComponent
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Vocab

@[expose] def InChevTwo (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧ IsChevTwo (K ⧸ Subgroup.center K)

@[expose] def InAlt (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin n))

@[expose] def IsHatSix (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))

@[expose] def IsRootFour {n : ℕ} (V : Subgroup (alternatingGroup (Fin n))) : Prop :=
  Nat.card V = 4 ∧ (∀ v ∈ V, v ^ 2 = 1) ∧
    Nat.card {i : Fin n // ¬ ∀ v ∈ V, (v : Equiv.Perm (Fin n)) i = i} = 4

@[expose] def InducesOn {A K : Type*} [Group A] [Group K] (e : (A ⧸ Subgroup.center A) ≃* K) (φ : MulAut A)
    (σ : MulAut K) : Prop :=
  ∀ a : A, e (QuotientGroup.mk (φ a)) = σ (e (QuotientGroup.mk a))

@[expose] def ActsLikeCQ {Y : Type*} [Group Y] {K : Type*} [Group K] (W A : Subgroup Y)
    (e : (↥A ⧸ Subgroup.center ↥A) ≃* K) (S : Subgroup (MulAut K)) : Prop :=
  (∀ φ ∈ inducedAutGroup W A, ∃ σ ∈ S, InducesOn e φ σ) ∧
    (∀ σ ∈ S, ∃ φ ∈ inducedAutGroup W A, InducesOn e φ σ)

@[expose] def ActsLikeTranspositionCQ {Y : Type*} [Group Y] (W A : Subgroup Y) (n : ℕ)
    (e : (↥A ⧸ Subgroup.center ↥A) ≃* ↥(alternatingGroup (Fin n))) : Prop :=
  Nat.card (inducedAutGroup W A) = 2 ∧ ∃ τ : Equiv.Perm (Fin n), τ.IsSwap ∧
    ActsLikeCQ W A e (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ))

@[expose] def ActsLikeRootFourCQ {Y : Type*} [Group Y] (W A : Subgroup Y) (n : ℕ)
    (e : (↥A ⧸ Subgroup.center ↥A) ≃* ↥(alternatingGroup (Fin n))) : Prop :=
  ∃ V : Subgroup ↥(alternatingGroup (Fin n)), IsRootFour V ∧
    ActsLikeCQ W A e (V.map (MulAut.conj : ↥(alternatingGroup (Fin n)) →* _))

@[expose] def ActsLikeSubRootFourCQ {Y : Type*} [Group Y] (W A : Subgroup Y) (n : ℕ)
    (e : (↥A ⧸ Subgroup.center ↥A) ≃* ↥(alternatingGroup (Fin n))) : Prop :=
  ∃ V₄ V : Subgroup ↥(alternatingGroup (Fin n)), IsRootFour V₄ ∧ V ≤ V₄ ∧
    ActsLikeCQ W A e (V.map (MulAut.conj : ↥(alternatingGroup (Fin n)) →* _))

@[expose] def NoInnerInduced {Y : Type*} [Group Y] (W A : Subgroup Y) : Prop :=
  inducedAutGroup W A ⊓ (MulAut.conj : ↥A →* MulAut ↥A).range = ⊥

@[expose] def ConjActsAs {X K' : Type*} [Group X] [Group K'] (x : X) (K : Subgroup X)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* K') (c : K') : Prop :=
  ∀ k k' : ↥K, (k' : X) = x * k * x⁻¹ → e (QuotientGroup.mk k') = c * e (QuotientGroup.mk k) * c⁻¹

end Vocab

section Family

variable {X : Type*} [Group X]

structure SignalizerFamily (p : ℕ) (D : Subgroup X) (Sd : X → Subgroup X) : Prop where
  elemAbelian : IsElemAbelian p D
  le_pCore : ∀ d ∈ D, d ≠ 1 → Sd d ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set X))
  inv_D : ∀ d ∈ D, d ≠ 1 → ∀ e ∈ D, e ∈ Subgroup.normalizer (Sd d : Set X)

@[expose] def sigmaFam (D : Subgroup X) (Sd : X → Subgroup X) : Subgroup X :=
  ⨆ (d : X) (_ : d ∈ D) (_ : d ≠ 1), Sd d

@[expose] def SignalizerFamily.CInvariant (D : Subgroup X) (Sd : X → Subgroup X) : Prop :=
  ∀ d ∈ D, d ≠ 1 → ∀ c ∈ Subgroup.centralizer ({d} : Set X), c ∈ Subgroup.normalizer (Sd d : Set X)

end Family

@[expose] def AltNotChevTwo : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≠ 5 → n ≠ 6 → n ≠ 8 → ¬ IsChevTwo (alternatingGroup (Fin n))

@[expose] def HatSevenOddInverts : Prop :=
  ∀ (Y : Type) [Group Y], IsHatSeven Y →
    ∀ e : (Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin 7)),
      ∀ (φ : MulAut Y) (σ : Equiv.Perm (Fin 7)), σ.sign = -1 →
        InducesOn e φ (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ) →
          ∀ z ∈ Subgroup.center Y, φ z = z⁻¹

@[expose] def AltSixSevenCentre : Prop :=
  ∀ n : ℕ, (n = 6 ∨ n = 7) → ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) → Nat.card (Subgroup.center Y) ∣ 6

@[expose] def OmegaCentreTrivial : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    Subgroup.center ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) = ⊥ ∧
      Subgroup.center ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) = ⊥

@[expose] def ActsAsTransvectionAt {Y : Type*} [Group Y] (ε : Bool) (n : ℕ) (T K : Subgroup Y) : Prop :=
  match ε with
  | true => ∃ e : ↥K ≃* ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))),
      Nat.card (inducedAutGroup T K) = 2 ∧
        ActsLikeTransvection (StatedQuadPlus (n + 1) (ZMod 2)) T K e
  | false => ∃ e : ↥K ≃* ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)),
      Nat.card (inducedAutGroup T K) = 2 ∧
        ActsLikeTransvection (StatedQuadMinus (n + 1) (ZMod 2) 1 1) T K e

@[expose] def Input19_20_2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
      ∀ (D : Subgroup X) (Sd : X → Subgroup X), SignalizerFamily p D Sd →
        IsPGroup 2 (inducedAutGroup (sigmaFam D Sd) K) ∧
          sigmaFam D Sd ≤ Subgroup.normalizer (K : Set X) ∧ NoInnerInduced (sigmaFam D Sd) K

@[expose] def Input19_20_3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
      ∀ (D : Subgroup X) (Sd : X → Subgroup X), SignalizerFamily p D Sd →
        ∀ (n : ℕ) (ε : Bool), 1 ≤ n → IsOmegaTwo ε (n + 1) ↥K →
          ¬ sigmaFam D Sd ≤ Subgroup.centralizer (K : Set X) →
            ActsAsTransvectionAt ε n (sigmaFam D Sd) K ∧ HasFixedPointFreeOrder ε n p

@[expose] def Input19_21_1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → GLAPPrimeCore p ↥K = ⊥ →
      ∀ e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7)),
        ∀ x : X, orderOf x = 3 → ∀ T : Subgroup X,
          T ≤ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) →
          ¬ T ≤ Subgroup.centralizer (K : Set X) →
            x ∈ Subgroup.normalizer (K : Set X) ∧ T ≤ Subgroup.normalizer (K : Set X) ∧
              (∃ c : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle ∧
                  ConjActsAs x K e c) ∧
              IsRootFour (((pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X))).subgroupOf K).map
                (QuotientGroup.mk' (Subgroup.center ↥K)) |>.map e.toMonoidHom) ∧
              inducedAutGroup T K ≤
                ((pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X))).subgroupOf K).map
                  (MulAut.conj : ↥K →* MulAut ↥K)

@[expose] def Input19_21_2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → GLAPPrimeCore p ↥K = ⊥ → InAlt ↥K →
      ∀ (D : Subgroup X) (Sd : X → Subgroup X), SignalizerFamily p D Sd →
        SignalizerFamily.CInvariant D Sd →
        ∀ So : Subgroup X, So ≤ pCoreOf 2 (sigmaFam D Sd) →
          (∀ e ∈ D, e ∈ Subgroup.normalizer (So : Set X)) →
            So ≤ Subgroup.centralizer (K : Set X) ∨
            ActsAsTransposition p So K ∨
            (∃ (k : ℕ) (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin (k * p + 4)))),
              ActsLikeSubRootFourCQ So K (k * p + 4) e) ∨
            (Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) ∧ p = 5 ∧
              Nat.card (inducedAutGroup So K) = 2 ∧
              Nonempty (↥(inducedAutGroup (K ⊔ So) K) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29))

section Input28

variable {X : Type} [Group X]

abbrev bar (W : Subgroup X) [W.Normal] (Y : Subgroup X) : Subgroup (X ⧸ W) :=
  Y.map (QuotientGroup.mk' W)

@[expose] def toBar (W K : Subgroup X) [W.Normal] : ↥K →* ↥(bar W K) :=
  ((QuotientGroup.mk' W).comp K.subtype).codRestrict (bar W K) fun k => ⟨k, k.2, rfl⟩

@[expose] def IsTwoPrimeCompOf (K : Subgroup X) : Prop :=
  IsSubnormal K ⊤ ∧ ⁅K, K⁆ = K ∧
    IsComponentOf (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) ⊤

@[expose] def Hyp28One (W K S : Subgroup X) [W.Normal] : Prop :=
  InChevTwo ↥(bar W K) ∧ ¬ InAlt ↥(bar W K) ∧ NoInnerInduced (bar W S) (bar W K)

@[expose] def Hyp28Two (W K S : Subgroup X) [W.Normal] : Prop :=
  InAlt ↥(bar W K) ∧ ¬ Nonempty (↥(bar W K) ≃* alternatingGroup (Fin 6)) ∧ ¬ IsHatSix ↥(bar W K) ∧
    ¬ IsHatSeven ↥(bar W K) ∧
    ∃ (n : ℕ) (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))),
      ActsLikeTranspositionCQ (bar W S) (bar W K) n e

@[expose] def Hyp28Three (W K S : Subgroup X) [W.Normal] : Prop :=
  InAlt ↥(bar W K) ∧ ¬ InChevTwo ↥(bar W K) ∧
    ∃ (n : ℕ) (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))),
      ActsLikeSubRootFourCQ (bar W S) (bar W K) n e

@[expose] def Hyp28Four (W K S : Subgroup X) [W.Normal] : Prop :=
  (Nonempty (↥(bar W K) ≃* alternatingGroup (Fin 6)) ∨ IsHatSix ↥(bar W K)) ∧
    Nat.card (inducedAutGroup (bar W S) (bar W K)) = 2 ∧
    Nonempty (↥(inducedAutGroup (bar W K ⊔ bar W S) (bar W K)) ≃*
      ↥CFSG.QuasithinUnique.A6Models.pgl29)

@[expose] def Concl28aWith {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (W K S : Subgroup X) [W.Normal] : Prop :=
  ∃ e : ↥(bar W K) ≃* ↥(StatedOmega Q),
    Nat.card (inducedAutGroup (bar W S) (bar W K)) = 2 ∧
    ActsLikeTransvection Q (bar W S) (bar W K) e ∧
    IsGLBlock (⊤ : Subgroup X) K ∧
    ∀ V U : Subgroup X, IsNoncentralChiefFactor K (pCoreOf 2 K) V U →
      ChiefFactorIso K U V (e.toMonoidHom.comp (toBar W K))
        (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v)

@[expose] def Concl28a (W K S : Subgroup X) [W.Normal] : Prop :=
  Hyp28One W K S ∧ ∃ n : ℕ, 2 ≤ n ∧
    (Concl28aWith (StatedQuadPlus (n + 1) (ZMod 2)) W K S ∨
      Concl28aWith (StatedQuadMinus (n + 1) (ZMod 2) 1 1) W K S)

@[expose] def Concl28b (W K S : Subgroup X) [W.Normal] : Prop :=
  Hyp28Two W K S ∧
    ∃ (n : ℕ) (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))),
      5 ≤ n ∧ ActsLikeTranspositionCQ (bar W S) (bar W K) n e ∧ IsGLBlock (⊤ : Subgroup X) K ∧
        ∀ V U : Subgroup X, IsNoncentralChiefFactor K (pCoreOf 2 K) V U →
          ChiefFactorIso K U V
            ((e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(bar W K)))).comp (toBar W K))
            (fun σ x => altHeartAct n (σ : Equiv.Perm (Fin n)) x)

@[expose] def Concl28c (W K S : Subgroup X) [W.Normal] : Prop :=
  ∃ e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7)),
    ActsLikeRootFourCQ (bar W S) (bar W K) 7 e ∧
      (Nat.card ↥(bar W S ⊓ bar W K) = 4 →
        IsGLBlock (⊤ : Subgroup X) K ∧ Nonempty (↥(bar W K) ≃* ↥(alternatingGroup (Fin 7))) ∧
          ∀ V U : Subgroup X, IsNoncentralChiefFactor K (pCoreOf 2 K) V U →
            Nat.card U = 16 * Nat.card V)

@[expose] def Concl28d (K S : Subgroup X) : Prop :=
  ∃ So : Subgroup X, So ≠ ⊥ ∧ IsCharIn So S ∧ K ≤ Subgroup.normalizer (So : Set X)

@[expose] def Input28_10 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (W : Subgroup X) [W.Normal] (K S : Subgroup X),
    IsPGroup 2 W → Subgroup.centralizer (W : Set X) ≤ W →
    IsTwoPrimeCompOf K → CFSG.pCore 2 ↥(bar W K) = ⊥ →
    IsPGroup 2 S → S ≤ Subgroup.normalizer (K : Set X) → W ≤ S →
      (Hyp28One W K S ∨ Hyp28Two W K S ∨ Hyp28Three W K S ∨ Hyp28Four W K S) →
        (Concl28a W K S ∨ Concl28b W K S ∨ Concl28c W K S ∨ Concl28d K S)

end Input28

section Gamma7

variable {X : Type} [Group X]

@[expose] def rootOf (K : Subgroup X) (x : X) : Subgroup X :=
  pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X))

@[expose] def imgA7 (K R : Subgroup X) (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) :
    Subgroup ↥(alternatingGroup (Fin 7)) :=
  ((R.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))).map e.toMonoidHom

@[expose] def A7Fact1 : Prop :=
  ∀ c : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle →
    IsRootFour (pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))))

@[expose] def A7Fact2 : Prop :=
  ∀ c : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle →
    ∃ Q : Subgroup ↥(alternatingGroup (Fin 7)), IsPGroup 3 Q ∧ Nat.card Q = 9 ∧
      Q ≤ Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7))) ∧
      ∀ x ∈ pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))), x ≠ 1 →
        ⁅Subgroup.zpowers x, Q⁆ =
          pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7))))

@[expose] def A7Fact3 : Prop :=
  ∀ c c' : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle →
    (c' : Equiv.Perm (Fin 7)).IsThreeCycle → c * c' = c' * c →
      c' ∈ Subgroup.zpowers c ∨
        Disjoint (c : Equiv.Perm (Fin 7)).support (c' : Equiv.Perm (Fin 7)).support

@[expose] def A7Fact4 : Prop :=
  ∀ c c' : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle →
    (c' : Equiv.Perm (Fin 7)).IsThreeCycle →
      Disjoint (c : Equiv.Perm (Fin 7)).support (c' : Equiv.Perm (Fin 7)).support →
        pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) ⊔
          pCoreOf 2 (Subgroup.centralizer ({c'} : Set ↥(alternatingGroup (Fin 7)))) = ⊤

@[expose] def A7Facts : Prop := A7Fact1 ∧ A7Fact2 ∧ A7Fact3 ∧ A7Fact4

structure Gamma7Data (K : Subgroup X) (D : Subgroup X) (Hf : X → Subgroup X) : Prop where
  comp : IsComponentOf K ⊤
  o3 : GLAPPrimeCore 3 ↥K = ⊥
  fam : SignalizerFamily 3 D Hf
  cinv : SignalizerFamily.CInvariant D Hf
  hatb : IsHatSeven ↥K → ∀ d ∈ D, d ≠ 1 → d ∈ Subgroup.normalizer (K : Set X) → rootOf K d ≤ Hf d

variable [Finite X]

@[expose] def sigma0 (K D : Subgroup X) (Hf : X → Subgroup X) : Subgroup X :=
  ⨆ (d : X) (_ : d ∈ D) (_ : d ≠ 1), Hf d ⊓ K

@[expose] def Gamma7Concl (K : Subgroup X) (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7)))
    (D : Subgroup X) (Hf : X → Subgroup X) : Prop :=
  sigmaFam D Hf ≤ Subgroup.normalizer (K : Set X) ∧
    ∃ R : Subgroup X, R ≤ K ∧ IsRootFour (imgA7 K R e) ∧ pCoreOf 2 (sigmaFam D Hf) ⊓ K = R ∧
      pCoreOf 2 (sigmaFam D Hf) ≤ R ⊔ Subgroup.centralizer (K : Set X)

end Gamma7

section Setting

variable {G : Type} [Group G] [Finite G]

structure IvSetting (m p : ℕ) (M D L : Subgroup G) : Prop where
  standing : GLStanding G m p
  hyp : Prop95Hyp p M D
  hQ : ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M
  hL : GLAPComponent p M L
  hn : barX p M (gammaD D) ≤ Subgroup.normalizer
    ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
  hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
    ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))

variable {m p : ℕ} {M D L : Subgroup G}

theorem tl_eq_bar (M Y : Subgroup G) : tl M Y = bar (CFSG.pCore 2 ↥M) (Y.subgroupOf M) := rfl

@[expose] def toTl (M L : Subgroup G) (hLM : L ≤ M) : ↥L →* ↥(tl M L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)).codRestrict (tl M L)
    fun ℓ => ⟨Subgroup.inclusion hLM ℓ, ℓ.2, rfl⟩

theorem map_projQ_tl (h : IvSetting m p M D L) (Y : Subgroup G) :
    (tl M Y).map (projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)) =
      barX p M Y := by
  unfold tl barX
  rw [Subgroup.map_map]
  congr 1

@[expose] noncomputable def psiL (h : IvSetting m p M D L) : ↥(tl M L) →* ↥(barX p M L) :=
  ((projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)).comp
    (tl M L).subtype).codRestrict (barX p M L) fun x => by
      have := map_projQ_tl h L
      rw [← this]
      exact ⟨x, x.2, rfl⟩

@[expose] def NotCovered (M D L : Subgroup G) : Prop :=
  ∀ T₀ : Subgroup G, T₀ ≠ ⊥ → (IsCharIn T₀ (gammaD D) ∨ IsCharIn T₀ (sigmaOf D)) →
    ¬ tl M L ≤ tl M (Subgroup.normalizer (T₀ : Set G))

@[expose] def Hfam (M D : Subgroup G) : Mt M → Subgroup (Mt M) := fun x =>
  ⨆ (d : G) (hdM : d ∈ M) (_ : d ∈ D) (_ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩ = x),
    tl M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))

@[expose] def Hbar (p : ℕ) (M D : Subgroup G) :
    (↥M ⧸ GLAPPrimeCore p ↥M) → Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) := fun x =>
  ⨆ (d : G) (hdM : d ∈ M) (_ : d ∈ D) (_ : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ = x),
    barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))

@[expose] def Prop95IvChevCov : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M →
      ∀ L : Subgroup G, GLAPComponent p M L →
        barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        NotCovered M D L →
        FFChevConclusion (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) →
        (¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) →
        IsGLBlock M L ∧ Prop95Beta p M D L

@[expose] def Prop95IvAltCov : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M →
      ∀ L : Subgroup G, GLAPComponent p M L →
        barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        NotCovered M D L →
        (∃ n : ℕ, 5 ≤ n ∧ Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) →
        IsGLBlock M L ∧ (Prop95Alpha p M D L ∨ Prop95Gamma p M D L)

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
