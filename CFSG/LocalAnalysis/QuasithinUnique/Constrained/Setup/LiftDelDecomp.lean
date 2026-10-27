module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDecompDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSetting

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family

section Setting

variable {G : Type} [Group G]

structure DelCtx (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F] (r : ℕ)
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  setting : EvenSL2Setting (⊤ : Subgroup G) R M V n F
  n_eq : n = 2
  charTwo : CharTwo (⊤ : Subgroup G)
  noChar : ∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
    ¬ (⊤ : Subgroup G) ≤ Subgroup.normalizer (Rc : Set G)
  deleted : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V
  comps : IsCompList (autOn (⊤ : Subgroup G) V) r Lc

theorem DelCtx.hX {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : DelCtx R M V n F r Lc) :
    (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
  ctx.setting.reduced.2.1

end Setting

section Baumann

variable {G : Type} [Group G]

structure DeletedBaumannCore (R V : Subgroup G) : Prop where
  baum_eq : autOn (baum R) V = autOn (thompsonJ R) V
  pCore_le : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G)) ≤ baum R
  normal : (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).Normal
  V_le_S : V ≤ baum R
  E_split : omegaOneCenterOf (thompsonJ R) =
    (omegaOneCenterOf (thompsonJ R) ⊓
        Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)) ⊔
      (V ⊓ Subgroup.centralizer (thompsonJ R : Set G))
  A_le_E : V ⊓ Subgroup.centralizer (thompsonJ R : Set G) ≤ omegaOneCenterOf (thompsonJ R)
  V_span : (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
      Campbell.cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V
  closure : (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
      Campbell.cj (omegaOneCenterOf (thompsonJ R)) l) =
    ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ ⊔
      (omegaOneCenterOf (thompsonJ R) ⊓
        Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G))
  J_C : ⁅thompsonJ R, V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)⁆ = ⊥
  CS_eq : baum R ⊓ Subgroup.centralizer (V : Set G) =
    pCoreOf 2 (⊤ : Subgroup G) ⊓ (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)
  CS_sylow : IsSylowTwoOf (baum R ⊓ Subgroup.centralizer (V : Set G))
    ((oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G))

end Baumann

section BaumannProp

@[expose] def DelBaumannProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), DelCtx R M V n F r Lc → DeletedBaumannCore R V

end BaumannProp

section Local

variable {G : Type} [Group G]

structure DelBase (R V : Subgroup G) : Prop where
  base : BaseData R V
  Q_eq : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) =
    baum R ⊓ Subgroup.centralizer (V : Set G)

structure DelSeed (R V : Subgroup G) (Li Fs : Subgroup (MulAut V)) : Prop where
  le : Fs ≤ Li
  card : Nat.card Fs = 3
  normalized : autOn (baum R) V ≤ Subgroup.normalizer (Fs : Set (MulAut V))

@[expose] noncomputable def delH0 (R V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) (Fs : Subgroup (MulAut V)) :
    Subgroup G :=
  (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ⊓ rhoPreimage V ⊤ hX (Fs ⊔ autOn (baum R) V)

structure DelH0 (R M V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) (Fs : Subgroup (MulAut V)) :
    Prop where
  sylow : IsSylowTwoOf (baum R) (delH0 R V hX Fs)
  not_le_M : ¬ delH0 R V hX Fs ≤ M

structure DelMinPImage (R V : Subgroup G) (Fs : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  image : autOn P V = Fs ⊔ autOn (baum R) V

structure DelW (R M V : Subgroup G) (Fs : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  W_le_S : modComm V Fs ≤ baum R
  card : Nat.card (modComm V Fs) = 4
  reduced : IsTwoReducedIn P (modComm V Fs)
  setting : ∃ (ϱ : ↥P →* Campbell.Gamma (ZMod 2))
      (ψ : ↥((modComm V Fs).subgroupOf P) →* Multiplicative (Fin 2 → ZMod 2)),
    Campbell.IsNatQuotSetting ((baum R).subgroupOf P) (M.subgroupOf P)
      ((modComm V Fs).subgroupOf P) ϱ ψ
  thompson_ne : ⁅thompsonJ (baum R), modComm V Fs⁆ ≠ ⊥

structure DelResidual (R V : Subgroup G) (Fs : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  P_eq : P = oddOrderSubgroup P ⊔ baum R
  perfect : ⁅oddOrderSubgroup P, thompsonJ R⁆ = oddOrderSubgroup P
  image : autOn (oddOrderSubgroup P) V = Fs
  fixed : modComm V Fs ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G) = ⊥
  gen : oddOrderSubgroup P ⊔ R = ⊤

structure DelAdapter (V : Subgroup G) (Fs : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  chi0 : IsChi0Block P (oddOrderSubgroup P)
  alt3 : IsAltType (oddOrderSubgroup P) 3
  iso : Nonempty (↥(oddOrderSubgroup P) ≃* alternatingGroup (Fin 4))
  centralizer : P ⊓ Subgroup.centralizer (modComm V Fs : Set G) = pCoreOf 2 P
  core : pCoreOf 2 (oddOrderSubgroup P) = modComm V Fs ∧
    ⁅pCoreOf 2 P, oddOrderSubgroup P⁆ = modComm V Fs

structure DelLocal (R M V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) (i : Fin r) (Fs : Subgroup (MulAut V))
    (P : Subgroup G) : Prop where
  base : DelBase R V
  seed : DelSeed R V (Lc i) Fs
  H0 : DelH0 R M V hX Fs
  minimal : IsMinimalOver (baum R) (delH0 R V hX Fs) M P
  basic : MinPBasic R M P
  image : DelMinPImage R V Fs P
  W : DelW R M V Fs P
  res : DelResidual R V Fs P
  ad : DelAdapter V Fs P
  q : QData R V Fs P

end Local

section LocalProps

@[expose] def DelBaseProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), DelCtx R M V n F r Lc →
    DeletedBaumannCore R V → DelBase R V

@[expose] def DelSeedProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), DelCtx R M V n F r Lc → ∀ i : Fin r,
    ∃ Fs : Subgroup (MulAut V), DelSeed R V (Lc i) Fs

@[expose] def DelH0Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)), DeletedBaumannCore R V → DelBase R V → DelSeed R V (Lc i) Fs →
    DelH0 R M V ctx.hX Fs

@[expose] def DelMinPBasicProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V → DelBase R V →
    DelSeed R V (Lc i) Fs → DelH0 R M V ctx.hX Fs →
    IsMinimalOver (baum R) (delH0 R V ctx.hX Fs) M P → MinPBasic R M P

@[expose] def DelMinPImageProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V → DelBase R V →
    DelSeed R V (Lc i) Fs → DelH0 R M V ctx.hX Fs →
    IsMinimalOver (baum R) (delH0 R V ctx.hX Fs) M P → MinPBasic R M P →
    DelMinPImage R V Fs P

@[expose] def DelWProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V → DelBase R V →
    DelSeed R V (Lc i) Fs → DelH0 R M V ctx.hX Fs →
    IsMinimalOver (baum R) (delH0 R V ctx.hX Fs) M P → MinPBasic R M P →
    DelMinPImage R V Fs P → DelW R M V Fs P

@[expose] def DelResidualProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V → DelBase R V →
    DelSeed R V (Lc i) Fs → DelH0 R M V ctx.hX Fs →
    IsMinimalOver (baum R) (delH0 R V ctx.hX Fs) M P → MinPBasic R M P →
    DelMinPImage R V Fs P → DelW R M V Fs P → DelResidual R V Fs P

@[expose] def DelAdapterProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V → DelBase R V →
    DelSeed R V (Lc i) Fs → DelH0 R M V ctx.hX Fs →
    IsMinimalOver (baum R) (delH0 R V ctx.hX Fs) M P → MinPBasic R M P →
    DelMinPImage R V Fs P → DelW R M V Fs P → DelResidual R V Fs P → DelAdapter V Fs P

@[expose] def DelQProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V → DelBase R V →
    DelSeed R V (Lc i) Fs → DelH0 R M V ctx.hX Fs →
    IsMinimalOver (baum R) (delH0 R V ctx.hX Fs) M P → MinPBasic R M P →
    DelMinPImage R V Fs P → DelW R M V Fs P → DelResidual R V Fs P → DelAdapter V Fs P →
    QData R V Fs P

end LocalProps

section Core

variable {G : Type} [Group G]

structure DelCore (R M V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) (i : Fin r) (Fs : Subgroup (MulAut V))
    (P : Subgroup G) : Prop where
  loc : DelLocal R M V hX Lc i Fs P
  gen : GenData R P
  sum : SumData R V Lc Fs P
  ker : KernelData R V

@[expose] def DelCoreAll (R M V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {r : ℕ}
    (Lc : Fin r → Subgroup (MulAut V)) : Prop :=
  ∀ i : Fin r, ∃ (Fs : Subgroup (MulAut V)) (P : Subgroup G), DelCore R M V hX Lc i Fs P

end Core

section CoreProps

@[expose] def DelGenProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V →
    DelLocal R M V ctx.hX Lc i Fs P → GenData R P

@[expose] def DelSumProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V →
    DelLocal R M V ctx.hX Lc i Fs P → GenData R P → SumData R V Lc Fs P

@[expose] def DelKernelProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    (Fs : Subgroup (MulAut V)) (P : Subgroup G), DeletedBaumannCore R V →
    DelLocal R M V ctx.hX Lc i Fs P → GenData R P → SumData R V Lc Fs P → KernelData R V

end CoreProps

section Blocks

variable {G : Type} [Group G]

structure DelBlockImage (R V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {r : ℕ}
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  normal_B : ∀ i,
    ((blockOf (⊤ : Subgroup G) R V hX (Lc i)).subgroupOf
      (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal
  image : ∀ i, autOn (blockOf (⊤ : Subgroup G) R V hX (Lc i)) V = Lc i
  injective : Function.Injective fun i => blockOf (⊤ : Subgroup G) R V hX (Lc i)
  permuted : ∀ t ∈ R, ∀ i, ∃ j,
    (blockOf (⊤ : Subgroup G) R V hX (Lc i)).map (MulAut.conj t).toMonoidHom =
      blockOf (⊤ : Subgroup G) R V hX (Lc j)
  transitive : ∀ i j, ∃ t ∈ R,
    (blockOf (⊤ : Subgroup G) R V hX (Lc i)).map (MulAut.conj t).toMonoidHom =
      blockOf (⊤ : Subgroup G) R V hX (Lc j)
  core : ∀ i, pCoreOf 2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)) =
    blockOf (⊤ : Subgroup G) R V hX (Lc i) ⊓
      pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)
  perfect_self : ∀ i, ⁅blockOf (⊤ : Subgroup G) R V hX (Lc i),
    blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ = blockOf (⊤ : Subgroup G) R V hX (Lc i)

structure DelBlockCore (R V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {r : ℕ}
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  coreComm : ∀ i,
    ⁅pCoreOf 2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)),
        blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ = modComm V (Lc i) ∧
      ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
        blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ = modComm V (Lc i)
  fixed : ∀ i, modComm V (Lc i) ⊓
    Subgroup.centralizer (blockOf (⊤ : Subgroup G) R V hX (Lc i) : Set G) = ⊥

structure DelBlockType (R V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {r : ℕ}
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  chi0 : ∀ i, IsChi0Block (⊤ : Subgroup G) (blockOf (⊤ : Subgroup G) R V hX (Lc i))
  alt : ∀ i, IsAltType (blockOf (⊤ : Subgroup G) R V hX (Lc i)) 5
  cComp : ∀ i, quasithinIsCComponent (blockOf (⊤ : Subgroup G) R V hX (Lc i)) (⊤ : Subgroup G)

structure DelBlockGen (R V : Subgroup G)
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {r : ℕ}
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  gen : ∀ i, (⊤ : Subgroup G) = blockOf (⊤ : Subgroup G) R V hX (Lc i) ⊔ R
  perfect : ∀ i, ⁅blockOf (⊤ : Subgroup G) R V hX (Lc i), thompsonJ R⁆ =
    blockOf (⊤ : Subgroup G) R V hX (Lc i)

end Blocks

section BlockProps

@[expose] def DelBlockImageProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc),
    DeletedBaumannCore R V → DelCoreAll R M V ctx.hX Lc → DelBlockImage R V ctx.hX Lc

@[expose] def DelBlockCoreProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc),
    DeletedBaumannCore R V → DelCoreAll R M V ctx.hX Lc → DelBlockImage R V ctx.hX Lc →
    DelBlockCore R V ctx.hX Lc

@[expose] def DelBlockTypeProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc),
    DeletedBaumannCore R V → DelCoreAll R M V ctx.hX Lc → DelBlockImage R V ctx.hX Lc →
    DelBlockCore R V ctx.hX Lc → DelBlockType R V ctx.hX Lc

@[expose] def DelBlockGenProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc),
    DeletedBaumannCore R V → DelCoreAll R M V ctx.hX Lc → DelBlockImage R V ctx.hX Lc →
    DelBlockGen R V ctx.hX Lc

@[expose] def DelBlockCommuteProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : DelCtx R M V n F r Lc),
    DeletedBaumannCore R V → DelCoreAll R M V ctx.hX Lc → DelBlockImage R V ctx.hX Lc →
    DelBlockCore R V ctx.hX Lc → BlockPartC (⊤ : Subgroup G) R V ctx.hX r Lc

end BlockProps

section Assembly

theorem delCoreAll_of_props (h0 : DelBaumannProp) (h1 : DelBaseProp) (h2 : DelSeedProp)
    (h3 : DelH0Prop) (h4 : DelMinPBasicProp) (h5 : DelMinPImageProp) (h6 : DelWProp)
    (h7 : DelResidualProp) (h8 : DelAdapterProp) (h9 : DelQProp) (h10 : DelGenProp)
    (h11 : DelSumProp) (h12 : DelKernelProp)
    {G : Type} [Group G] [Finite G] {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : DelCtx R M V n F r Lc) :
    DelCoreAll R M V ctx.hX Lc := by
  intro i
  have hcore : DeletedBaumannCore R V := h0 G R M V n F r Lc ctx
  have hbase : DelBase R V := h1 G R M V n F r Lc ctx hcore
  obtain ⟨Fs, hseed⟩ := h2 G R M V n F r Lc ctx i
  have hH0 : DelH0 R M V ctx.hX Fs := h3 G R M V n F r Lc ctx i Fs hcore hbase hseed
  obtain ⟨P, hmin⟩ := exists_isMinimalOver (S := baum R) (T := delH0 R V ctx.hX Fs) (M := M)
    hH0.sylow.1 hH0.not_le_M
  have hbasic := h4 G R M V n F r Lc ctx i Fs P hcore hbase hseed hH0 hmin
  have himage := h5 G R M V n F r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic
  have hW := h6 G R M V n F r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage
  have hres := h7 G R M V n F r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage hW
  have had := h8 G R M V n F r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage hW hres
  have hq := h9 G R M V n F r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage hW hres had
  have hloc : DelLocal R M V ctx.hX Lc i Fs P :=
    ⟨hbase, hseed, hH0, hmin, hbasic, himage, hW, hres, had, hq⟩
  have hgen := h10 G R M V n F r Lc ctx i Fs P hcore hloc
  have hsum := h11 G R M V n F r Lc ctx i Fs P hcore hloc hgen
  have hker := h12 G R M V n F r Lc ctx i Fs P hcore hloc hgen hsum
  exact ⟨Fs, P, hloc, hgen, hsum, hker⟩

theorem deleted_canonical_top_of_decomp
    (h0 : DelBaumannProp) (h1 : DelBaseProp)
    (h2 : DelSeedProp) (h3 : DelH0Prop) (h4 : DelMinPBasicProp) (h5 : DelMinPImageProp)
    (h6 : DelWProp) (h7 : DelResidualProp) (h8 : DelAdapterProp) (h9 : DelQProp)
    (h10 : DelGenProp) (h11 : DelSumProp) (h12 : DelKernelProp) (h13 : DelBlockImageProp)
    (h14 : DelBlockCoreProp) (h15 : DelBlockTypeProp) (h16 : DelBlockGenProp)
    (h17 : DelBlockCommuteProp) : DeletedCanonicalAlt5BlocksTop := by
  intro G _ _ R M V n F _ hS hchar hno hn hdel r Lc hLc
  have ctx : DelCtx R M V n F r Lc := ⟨hS, hn, hchar, hno, hdel, hLc⟩
  have hbridge := even_SL2_original_bridge hS hLc
  have hr : 0 < r := hbridge.r_pos
  have hcore : DeletedBaumannCore R V := h0 G R M V n F r Lc ctx
  have hall : DelCoreAll R M V ctx.hX Lc :=
    delCoreAll_of_props h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 ctx
  have hImage := h13 G R M V n F r Lc ctx hcore hall
  have hCore := h14 G R M V n F r Lc ctx hcore hall hImage
  have hType := h15 G R M V n F r Lc ctx hcore hall hImage hCore
  have hGen := h16 G R M V n F r Lc ctx hcore hall hImage
  have hC := h17 G R M V n F r Lc ctx hcore hall hImage hCore
  obtain ⟨Fs, P, hcore0⟩ := hall ⟨0, hr⟩
  have hA : BlockPartA (⊤ : Subgroup G) R V ctx.hX r Lc :=
    ⟨hImage.injective, hImage.normal_B, hImage.permuted, hImage.transitive, hType.chi0,
      hGen.gen, hGen.perfect, hImage.image, hCore.coreComm⟩
  have hD : BlockPartD (⊤ : Subgroup G) R V r Lc :=
    ⟨hcore.normal.subgroupOf _, hcore0.ker.kernel, hcore0.sum.commutator, hbridge.r_pow,
      hbridge.rank⟩
  exact EvenSL2BlockOutput.of_parts hA hType.cComp hC hD (fun h => absurd h hdel)
    (fun _ => ⟨hn, hType.alt⟩)

theorem deleted_canonical_of_decomp
    (hT : BlockTransferProp) (h0 : DelBaumannProp)
    (h1 : DelBaseProp) (h2 : DelSeedProp) (h3 : DelH0Prop) (h4 : DelMinPBasicProp)
    (h5 : DelMinPImageProp) (h6 : DelWProp) (h7 : DelResidualProp) (h8 : DelAdapterProp)
    (h9 : DelQProp) (h10 : DelGenProp) (h11 : DelSumProp) (h12 : DelKernelProp)
    (h13 : DelBlockImageProp) (h14 : DelBlockCoreProp) (h15 : DelBlockTypeProp)
    (h16 : DelBlockGenProp) (h17 : DelBlockCommuteProp) : DeletedCanonicalAlt5Blocks :=
  hT.2 (deleted_canonical_top_of_decomp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    h17)

end Assembly

end CFSG.QuasithinUnique.Setup.Lift
