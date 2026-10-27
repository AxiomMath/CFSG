module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDecompDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNormalLS

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family

section Setting

variable {G : Type} [Group G]

structure NatCtx (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F] (r : ℕ)
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  setting : EvenSL2Setting (⊤ : Subgroup G) R M V n F
  charTwo : CharTwo (⊤ : Subgroup G)
  noChar : ∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
    ¬ (⊤ : Subgroup G) ≤ Subgroup.normalizer (Rc : Set G)
  natural : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V
  comps : IsCompList (autOn (⊤ : Subgroup G) V) r Lc

theorem NatCtx.hX {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : NatCtx R M V n F r Lc) :
    (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
  ctx.setting.reduced.2.1

end Setting

section Local

variable {G : Type} [Group G]

structure NatYData (R M V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (D : Subgroup (MulAut V)) : Prop where
  le_L : oddOrderSubgroup (rhoPreimage V ⊤ hX D) ≤ oddOrderSubgroup (⊤ : Subgroup G)
  image : autOn (oddOrderSubgroup (rhoPreimage V ⊤ hX D)) V = D
  normalized : baum R ≤ Subgroup.normalizer (oddOrderSubgroup (rhoPreimage V ⊤ hX D) : Set G)
  not_le_M : ¬ oddOrderSubgroup (rhoPreimage V ⊤ hX D) ≤ M

structure NatMinPImage (R V : Subgroup G) (D : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  image : autOn P V = D ⊔ autOn (baum R) V
  I_le_S : modComm V D ≤ baum R
  I_reduced : IsTwoReducedIn P (modComm V D)

structure NatMinPK (V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (D : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  image : autOn (oddOrderSubgroup P) V = D
  fixed : modComm V D ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G) =
    modComm V D ⊓ Subgroup.centralizer (rhoPreimage V ⊤ hX D : Set G)

structure NatMinPCampbell (R M V : Subgroup G) (F : Type) [Field F] (D : Subgroup (MulAut V))
    (P : Subgroup G) : Prop where
  setting : ∃ (ϱ : ↥P →* Campbell.Gamma F)
      (ψ : ↥((modComm V D).subgroupOf P) →* Multiplicative (Fin 2 → F)),
    Campbell.IsNatQuotSetting ((baum R).subgroupOf P) (M.subgroupOf P)
      ((modComm V D).subgroupOf P) ϱ ψ
  thompson_ne : ⁅thompsonJ (baum R), modComm V D⁆ ≠ ⊥

structure NatLocal (R M V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (F : Type) [Field F] {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) (i : Fin r)
    (P : Subgroup G) : Prop where
  base : BaseData R V
  Y : NatYData R M V hX (Lc i)
  minimal : IsMinimalOver (baum R)
    (oddOrderSubgroup (rhoPreimage V ⊤ hX (Lc i)) ⊔ baum R) M P
  basic : MinPBasic R M P
  image : NatMinPImage R V (Lc i) P
  K : NatMinPK V hX (Lc i) P
  campbell : NatMinPCampbell R M V F (Lc i) P

end Local

section LocalProps

@[expose] def NatVleSProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), NatCtx R M V n F r Lc → V ≤ baum R

@[expose] def NatBaseProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), NatCtx R M V n F r Lc → V ≤ baum R →
    BaseData R V

@[expose] def NatYProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r),
    NatYData R M V ctx.hX (Lc i)

@[expose] def NatMinPBasicProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), BaseData R V → NatYData R M V ctx.hX (Lc i) →
    IsMinimalOver (baum R) (oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R) M P →
    MinPBasic R M P

@[expose] def NatMinPImageProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), BaseData R V → NatYData R M V ctx.hX (Lc i) →
    IsMinimalOver (baum R) (oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R) M P →
    MinPBasic R M P → NatMinPImage R V (Lc i) P

@[expose] def NatMinPKProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), BaseData R V → NatYData R M V ctx.hX (Lc i) →
    IsMinimalOver (baum R) (oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R) M P →
    MinPBasic R M P → NatMinPImage R V (Lc i) P → NatMinPK V ctx.hX (Lc i) P

@[expose] def NatMinPCampbellProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), BaseData R V → NatYData R M V ctx.hX (Lc i) →
    IsMinimalOver (baum R) (oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R) M P →
    MinPBasic R M P → NatMinPImage R V (Lc i) P → NatMinPK V ctx.hX (Lc i) P →
    NatMinPCampbell R M V F (Lc i) P

end LocalProps

section Core

variable {G : Type} [Group G]

structure NatResidual (R P : Subgroup G) : Prop where
  P_eq : P = oddOrderSubgroup P ⊔ baum R
  perfect : ⁅oddOrderSubgroup P, thompsonJ R⁆ = oddOrderSubgroup P

structure NatAdapter (V : Subgroup G) (n : ℕ) (D : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  chi0 : IsChi0Block P (oddOrderSubgroup P)
  lin : IsLin2Type (oddOrderSubgroup P) n
  coreComm : ⁅pCoreOf 2 (oddOrderSubgroup P), oddOrderSubgroup P⁆ = modComm V D
  centralizer : P ⊓ Subgroup.centralizer (modComm V D : Set G) = pCoreOf 2 P

structure NatCore (R M V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (n : ℕ) (F : Type) [Field F] {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) (i : Fin r)
    (P : Subgroup G) : Prop where
  loc : NatLocal R M V hX F Lc i P
  res : NatResidual R P
  ad : NatAdapter V n (Lc i) P
  q : QData R V (Lc i) P
  gen : GenData R P
  sum : SumData R V Lc (Lc i) P
  ker : KernelData R V

end Core

section CoreProps

@[expose] def NatResidualProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatLocal R M V ctx.hX F Lc i P → NatResidual R P

@[expose] def NatAdapterProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatLocal R M V ctx.hX F Lc i P → NatResidual R P →
    NatAdapter V n (Lc i) P

@[expose] def NatQProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatLocal R M V ctx.hX F Lc i P → NatResidual R P →
    NatAdapter V n (Lc i) P → QData R V (Lc i) P

@[expose] def NatGenProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatLocal R M V ctx.hX F Lc i P → NatResidual R P →
    NatAdapter V n (Lc i) P → QData R V (Lc i) P → GenData R P

@[expose] def NatSumProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatLocal R M V ctx.hX F Lc i P → NatResidual R P →
    NatAdapter V n (Lc i) P → QData R V (Lc i) P → GenData R P → SumData R V Lc (Lc i) P

@[expose] def NatKernelProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatLocal R M V ctx.hX F Lc i P → GenData R P → SumData R V Lc (Lc i) P →
    KernelData R V

end CoreProps

section Blocks

variable {G : Type} [Group G]

structure NatCanonical (R V : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  ident : ∀ t ∈ R, ∀ i,
    autOn ((oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom) V = Lc i →
      blockOf (⊤ : Subgroup G) R V hX (Lc i) = (oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom
  surj : ∀ i, ∃ t ∈ R,
    autOn ((oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom) V = Lc i

end Blocks

section BlockProps

@[expose] def NatCanonicalProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatCore R M V ctx.hX n F Lc i P → NatCanonical R V ctx.hX Lc P

@[expose] def NatBlockTransportProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatCore R M V ctx.hX n F Lc i P → NatCanonical R V ctx.hX Lc P →
    BlockPartA (⊤ : Subgroup G) R V ctx.hX r Lc ∧
      ∀ j, IsLin2Type (blockOf (⊤ : Subgroup G) R V ctx.hX (Lc j)) n

@[expose] def NatCCompProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatCore R M V ctx.hX n F Lc i P → NatCanonical R V ctx.hX Lc P →
    BlockPartA (⊤ : Subgroup G) R V ctx.hX r Lc →
    ∀ j, quasithinIsCComponent (blockOf (⊤ : Subgroup G) R V ctx.hX (Lc j)) (⊤ : Subgroup G)

@[expose] def NatCommuteProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) (ctx : NatCtx R M V n F r Lc) (i : Fin r)
    (P : Subgroup G), NatCore R M V ctx.hX n F Lc i P → NatCanonical R V ctx.hX Lc P →
    BlockPartA (⊤ : Subgroup G) R V ctx.hX r Lc →
    (∀ j, quasithinIsCComponent (blockOf (⊤ : Subgroup G) R V ctx.hX (Lc j)) (⊤ : Subgroup G)) →
    BlockPartC (⊤ : Subgroup G) R V ctx.hX r Lc

end BlockProps

section Assembly

theorem natLocal_of_props (h1 : NatVleSProp) (h2 : NatBaseProp) (h3 : NatYProp)
    (h4 : NatMinPBasicProp) (h5 : NatMinPImageProp) (h6 : NatMinPKProp) (h7 : NatMinPCampbellProp)
    {G : Type} [Group G] [Finite G] {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : NatCtx R M V n F r Lc) (i : Fin r) :
    ∃ P : Subgroup G, NatLocal R M V ctx.hX F Lc i P := by
  have hV : V ≤ baum R := h1 G R M V n F r Lc ctx
  have hbase : BaseData R V := h2 G R M V n F r Lc ctx hV
  have hY : NatYData R M V ctx.hX (Lc i) := h3 G R M V n F r Lc ctx i
  obtain ⟨P, hmin⟩ := exists_isMinimalOver (S := baum R)
    (T := oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R) (M := M) le_sup_right
    (fun h => hY.not_le_M (le_sup_left.trans h))
  have hbasic := h4 G R M V n F r Lc ctx i P hbase hY hmin
  have himage := h5 G R M V n F r Lc ctx i P hbase hY hmin hbasic
  have hK := h6 G R M V n F r Lc ctx i P hbase hY hmin hbasic himage
  have hcamp := h7 G R M V n F r Lc ctx i P hbase hY hmin hbasic himage hK
  exact ⟨P, ⟨hbase, hY, hmin, hbasic, himage, hK, hcamp⟩⟩

theorem natural_canonical_top_of_decomp
    (h1 : NatVleSProp) (h2 : NatBaseProp) (h3 : NatYProp)
    (h4 : NatMinPBasicProp) (h5 : NatMinPImageProp) (h6 : NatMinPKProp)
    (h7 : NatMinPCampbellProp) (h8 : NatResidualProp) (h9 : NatAdapterProp) (h10 : NatQProp)
    (h11 : NatGenProp) (h12 : NatSumProp) (h13 : NatKernelProp) (h14 : NatCanonicalProp)
    (h15 : NatBlockTransportProp) (h16 : NatCCompProp) (h17 : NatCommuteProp) :
    NaturalCanonicalLin2BlocksTop := by
  intro G _ _ R M V n F _ hS hchar hno hle r Lc hLc
  have ctx : NatCtx R M V n F r Lc := ⟨hS, hchar, hno, hle, hLc⟩
  have hbridge := even_SL2_original_bridge hS hLc
  have hr : 0 < r := hbridge.r_pos
  let i : Fin r := ⟨0, hr⟩
  obtain ⟨P, hloc⟩ := natLocal_of_props h1 h2 h3 h4 h5 h6 h7 ctx i
  have hres := h8 G R M V n F r Lc ctx i P hloc
  have had := h9 G R M V n F r Lc ctx i P hloc hres
  have hq := h10 G R M V n F r Lc ctx i P hloc hres had
  have hgen := h11 G R M V n F r Lc ctx i P hloc hres had hq
  have hsum := h12 G R M V n F r Lc ctx i P hloc hres had hq hgen
  have hker := h13 G R M V n F r Lc ctx i P hloc hgen hsum
  have hcore : NatCore R M V ctx.hX n F Lc i P := ⟨hloc, hres, had, hq, hgen, hsum, hker⟩
  have hcan := h14 G R M V n F r Lc ctx i P hcore
  obtain ⟨hA, hlin⟩ := h15 G R M V n F r Lc ctx i P hcore hcan
  have hB := h16 G R M V n F r Lc ctx i P hcore hcan hA
  have hC := h17 G R M V n F r Lc ctx i P hcore hcan hA hB
  have hD : BlockPartD (⊤ : Subgroup G) R V r Lc :=
    ⟨(normal_L_sup_baum hS).subgroupOf _, hker.kernel, hsum.commutator, hbridge.r_pow, hbridge.rank⟩
  exact EvenSL2BlockOutput.of_parts hA hB hC hD (fun _ => hlin)
    (fun h => absurd hle h)

theorem natural_canonical_of_decomp
    (hT : BlockTransferProp) (h1 : NatVleSProp)
    (h2 : NatBaseProp) (h3 : NatYProp) (h4 : NatMinPBasicProp) (h5 : NatMinPImageProp)
    (h6 : NatMinPKProp) (h7 : NatMinPCampbellProp) (h8 : NatResidualProp) (h9 : NatAdapterProp)
    (h10 : NatQProp) (h11 : NatGenProp) (h12 : NatSumProp) (h13 : NatKernelProp)
    (h14 : NatCanonicalProp) (h15 : NatBlockTransportProp) (h16 : NatCCompProp)
    (h17 : NatCommuteProp) : NaturalCanonicalLin2Blocks :=
  hT.1 (natural_canonical_top_of_decomp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17)

end Assembly

end CFSG.QuasithinUnique.Setup.Lift
