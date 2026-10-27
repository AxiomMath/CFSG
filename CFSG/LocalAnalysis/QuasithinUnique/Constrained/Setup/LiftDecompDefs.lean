module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopBlocks

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family

section Minimal

variable {G : Type} [Group G]

structure IsMinimalOver (S T M P : Subgroup G) : Prop where
  S_le : S ≤ P
  le : P ≤ T
  not_le : ¬ P ≤ M
  minimal : ∀ P' : Subgroup G, S ≤ P' → P' ≤ P → ¬ P' ≤ M → P' = P

theorem exists_isMinimalOver [Finite G] {S T M : Subgroup G} (hST : S ≤ T) (hT : ¬ T ≤ M) :
    ∃ P, IsMinimalOver S T M P := by
  classical
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  obtain ⟨P, ⟨hSP, hPT, hPM⟩, hmin⟩ :=
    wellFounded_lt.has_min {P : Subgroup G | S ≤ P ∧ P ≤ T ∧ ¬ P ≤ M} ⟨T, hST, le_rfl, hT⟩
  refine ⟨P, hSP, hPT, hPM, fun P' hSP' hP'P hP'M => ?_⟩
  by_contra hne
  exact hmin P' ⟨hSP', hP'P.trans hPT, hP'M⟩ (lt_of_le_of_ne hP'P hne)

end Minimal

section Shared

variable {G : Type} [Group G]

structure BaseData (R V : Subgroup G) : Prop where
  S_char : ((baum R).subgroupOf R).Characteristic
  J_S : thompsonJ (baum R) = thompsonJ R
  E_S : omegaOneCenterOf (thompsonJ (baum R)) = omegaOneCenterOf (thompsonJ R)
  B_S : baum (baum R) = baum R
  charTwo : CharTwo (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)
  Q_le_S : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ baum R
  V_le_Q : V ≤ pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)

structure MinPBasic (R M P : Subgroup G) : Prop where
  lt : baum R < P
  sylow : IsSylowTwoOf (baum R) P
  not_normal : ¬ ((baum R).subgroupOf P).Normal
  max : ∀ Y : Subgroup G, baum R ≤ Y → Y < P → Y ≤ M
  gen : P ⊔ R = ⊤
  noChar : ∀ C : Subgroup G, C ≤ baum R → C ≠ ⊥ → (C.subgroupOf (baum R)).Characteristic →
    ¬ P ≤ Subgroup.normalizer (C : Set G)
  charTwo : CharTwo P

structure QData (R V : Subgroup G) (D : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  comm : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R), oddOrderSubgroup P⁆ =
    modComm V D
  central : modComm V D ≤
    omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R))
  normalizes : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤
    Subgroup.normalizer (oddOrderSubgroup P : Set G)

structure GenData (R P : Subgroup G) : Prop where
  gen : oddOrderSubgroup (⊤ : Subgroup G) = conjJoin R (oddOrderSubgroup P)
  ne_bot : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
    oddOrderSubgroup (⊤ : Subgroup G)⁆ ≠ ⊥
  elem : IsElemAbelian 2 (⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
    oddOrderSubgroup (⊤ : Subgroup G)⁆ : Subgroup G)
  normal : (⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
    oddOrderSubgroup (⊤ : Subgroup G)⁆ : Subgroup G).Normal
  central : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
    oddOrderSubgroup (⊤ : Subgroup G)⁆ ≤
    omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R))

structure SumData (R V : Subgroup G) {r : ℕ} (Lc : Fin r → Subgroup (MulAut V))
    (D : Subgroup (MulAut V)) (P : Subgroup G) : Prop where
  conj_normalizes : ∀ t ∈ R,
    pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤
      Subgroup.normalizer (((oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G)
  conj_comm : ∀ t ∈ R,
    ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
        (oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom⁆ =
      (modComm V D).map (MulAut.conj t).toMonoidHom ∧
    ⁅pCoreOf 2 ((oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom),
        (oddOrderSubgroup P).map (MulAut.conj t).toMonoidHom⁆ =
      (modComm V D).map (MulAut.conj t).toMonoidHom
  commutator : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
      oddOrderSubgroup (⊤ : Subgroup G)⁆ = ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ ∧
    ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ = ⨆ j, modComm V (Lc j) ∧
    (⨆ j, modComm V (Lc j)) ≤
      omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R))

structure KernelData (R V : Subgroup G) : Prop where
  kernel : (⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (⊤ : Subgroup G) ∧
    (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)

end Shared

section Parts

variable {G : Type} [Group G]

structure BlockPartA (X R V : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G)) (r : ℕ)
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  injective : Function.Injective fun i => blockOf X R V hX (Lc i)
  normal_B : ∀ i,
    ((blockOf X R V hX (Lc i)).subgroupOf (oddOrderSubgroup X ⊔ baum R)).Normal
  permuted : ∀ t ∈ R, ∀ i, ∃ j,
    (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom = blockOf X R V hX (Lc j)
  transitive : ∀ i j, ∃ t ∈ R,
    (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom = blockOf X R V hX (Lc j)
  chi0 : ∀ i, IsChi0Block X (blockOf X R V hX (Lc i))
  gen : ∀ i, X = blockOf X R V hX (Lc i) ⊔ R
  perfect : ∀ i, ⁅blockOf X R V hX (Lc i), thompsonJ R⁆ = blockOf X R V hX (Lc i)
  image : ∀ i, autOn (blockOf X R V hX (Lc i)) V = Lc i
  coreComm : ∀ i,
    ⁅pCoreOf 2 (blockOf X R V hX (Lc i)), blockOf X R V hX (Lc i)⁆ = modComm V (Lc i) ∧
      ⁅pCoreOf 2 (oddOrderSubgroup X ⊔ baum R), blockOf X R V hX (Lc i)⁆ = modComm V (Lc i)

structure BlockPartC (X R V : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G)) (r : ℕ)
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  commute : ∀ i j, i ≠ j →
    ⁅blockOf X R V hX (Lc i), blockOf X R V hX (Lc j)⁆ = ⊥
  product : oddOrderSubgroup X = ⨆ i, blockOf X R V hX (Lc i) ∧
    ∀ i, blockOf X R V hX (Lc i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), blockOf X R V hX (Lc j)) ≤
      centerIn (blockOf X R V hX (Lc i))

structure BlockPartD (X R V : Subgroup G) (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  normal_LS : ((oddOrderSubgroup X ⊔ baum R).subgroupOf X).Normal
  kernel : X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X ∧
    (oddOrderSubgroup X ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (oddOrderSubgroup X ⊔ baum R)
  commutator : ⁅pCoreOf 2 (oddOrderSubgroup X ⊔ baum R), oddOrderSubgroup X⁆ =
      ⁅V, oddOrderSubgroup X⁆ ∧
    ⁅V, oddOrderSubgroup X⁆ = ⨆ i, modComm V (Lc i) ∧
    (⨆ i, modComm V (Lc i)) ≤ omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup X ⊔ baum R))
  rank : (∃ k : ℕ, r = 2 ^ k) ∧ r ≤ CFSG.pRank 3 X

theorem EvenSL2BlockOutput.of_parts {X R V : Subgroup G}
    {hX : X ≤ Subgroup.normalizer (V : Set G)} {n r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hA : BlockPartA X R V hX r Lc)
    (hB : ∀ i, quasithinIsCComponent (blockOf X R V hX (Lc i)) X)
    (hC : BlockPartC X R V hX r Lc) (hD : BlockPartD X R V r Lc)
    (hlin : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
      ∀ i, IsLin2Type (blockOf X R V hX (Lc i)) n)
    (halt : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
      n = 2 ∧ ∀ i, IsAltType (blockOf X R V hX (Lc i)) 5) :
    EvenSL2BlockOutput X R V hX n r Lc :=
  ⟨hA.injective, hD.normal_LS, hA.normal_B, hA.permuted, hA.transitive, hB, hA.chi0, hA.gen,
    hA.perfect, hA.image, hA.coreComm, hC.commute, hC.product, hD.kernel, hD.commutator, hlin,
    halt, hD.rank⟩

end Parts

section Top

@[expose] def NaturalCanonicalLin2BlocksTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F), CharTwo (⊤ : Subgroup G) →
    (∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ (⊤ : Subgroup G) ≤ Subgroup.normalizer (Rc : Set G)) →
    autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V →
    ∀ (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), IsCompList (autOn (⊤ : Subgroup G) V) r Lc →
      EvenSL2BlockOutput (⊤ : Subgroup G) R V hS.reduced.2.1 n r Lc

@[expose] def DeletedCanonicalAlt5BlocksTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F), CharTwo (⊤ : Subgroup G) →
    (∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ (⊤ : Subgroup G) ≤ Subgroup.normalizer (Rc : Set G)) → n = 2 →
    ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V →
    ∀ (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), IsCompList (autOn (⊤ : Subgroup G) V) r Lc →
      EvenSL2BlockOutput (⊤ : Subgroup G) R V hS.reduced.2.1 n r Lc

@[expose] def BlockTransferProp : Prop :=
  (NaturalCanonicalLin2BlocksTop → NaturalCanonicalLin2Blocks) ∧
    (DeletedCanonicalAlt5BlocksTop → DeletedCanonicalAlt5Blocks)

end Top

end CFSG.QuasithinUnique.Setup.Lift
