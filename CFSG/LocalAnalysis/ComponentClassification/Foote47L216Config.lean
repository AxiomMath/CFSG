module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P2

public section

namespace CFSG.ComponentClassification.Foote47L216

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Foote47

variable {G : Type} [Group G]

@[expose] def K (a : G) : Subgroup G :=
  solomonKStarOf (Subgroup.centralizer ({a} : Set G))

@[expose] def Lgen (E : Subgroup G) : Subgroup G :=
  ⨆ a ∈ E, ⨆ (_ : a ≠ 1), K a

@[expose] def Y (M : Subgroup G) (a : G) : Subgroup G :=
  oddResidualIn (M ⊓ Subgroup.centralizer ({a} : Set G))

@[expose] def ActualClass (M : Subgroup G) : Prop :=
  ∃ (v : G) (X E : Subgroup G),
    orderOf v = 2 ∧ IsTwoComponentAt v X ∧ X ∈ solomonKStar G ∧
    Blueprint.LieModel (↥X ⧸ Open.fusionZStar ↥X) .PSL 2 2 4 ∧
    E ≤ coreActionKernel X ∧ (∀ e ∈ E, e ^ 2 = 1) ∧ Nat.card E = 8 ∧
    M = Lgen E

variable [Finite G]

@[expose] def YSupplier (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (M : Subgroup G) (a : G), ActualClass M → orderOf a = 2 →
    a ∈ coreActionKernel M →
    Y M a ≤ M ⊓ K a ∧ Y M a ⊔ oddCoreIn M = M ∧ Y M a ⊔ oddCoreIn (K a) = K a

structure ActualViol (M : Subgroup G) (t : G) : Prop where
  hM : ActualClass M
  ht : orderOf t = 2
  htC : t ∈ coreActionKernel M
  hno : NoEight (coreActionKernel M ⊓ centralizer ({t} : Set G))

structure ActualConf (M T S P : Subgroup G) (t z : G) : Prop where
  hv : ActualViol M t
  hSN : IsSylowOf 2 S (normalizer (M : Set G))
  hSz : IsSylowOf 2 S (centralizer ({z} : Set G))
  hT : T = S ⊓ coreActionKernel M
  hTsyl : IsSylowOf 2 T (coreActionKernel M)
  htT : t ∈ T
  hd : ∃ Q0 : Subgroup G, TwoData T t z Q0
  hP : P = S ⊓ centralizer ({t} : Set G)
  hPsyl : IsSylowOf 2 P (centralizer ({t} : Set G))
  hQX : IsSylowOf 2 (T ⊓ centralizer ({t} : Set G))
    (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel (K z))
  hQF : T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel (K t)
  hFK : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel (K t) ≤
    coreActionKernel (K z)
  hQP : P ⊓ coreActionKernel (K t) = T ⊓ centralizer ({t} : Set G)

theorem centralizer_le_normalizer_K (a : G) :
    centralizer ({a} : Set G) ≤ normalizer (K a : Set G) :=
  Sol76.le_normalizer_solomonKStarOf (centralizer ({a} : Set G))

theorem coreActionKernel_inf_centralizer_le (hY : YSupplier G)
    {M : Subgroup G} {a : G} (hM : ActualClass M) (ha : orderOf a = 2)
    (haC : a ∈ coreActionKernel M) :
    coreActionKernel M ⊓ centralizer ({a} : Set G) ≤ coreActionKernel (K a) := by
  intro x hx
  have hxM : x ∈ coreActionKernel M := (mem_inf.mp hx).1
  have hxa : x ∈ centralizer ({a} : Set G) := (mem_inf.mp hx).2
  have hxNM : x ∈ normalizer (M : Set G) := hxM.1
  have hxNCa : x ∈ normalizer (centralizer ({a} : Set G) : Set G) := le_normalizer hxa
  have hxNY : x ∈ normalizer (Y M a : Set G) :=
    mem_normalizer_oddResidualIn (mem_normalizer_inf' hxNM hxNCa)
  have hYspec := hY M a hM ha haC
  have hxCY : x ∈ coreActionKernel (Y M a) :=
    mem_coreActionKernel_of_le (hYspec.1.trans inf_le_left) hxNY hxM
  have hxNKa : x ∈ normalizer (K a : Set G) := centralizer_le_normalizer_K a hxa
  exact mem_coreActionKernel_of_sup (hYspec.1.trans inf_le_right) hYspec.2.2 hxNKa hxCY

end CFSG.ComponentClassification.Foote47L216
