module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G]

@[expose] def modComm (V : Subgroup G) (A : Subgroup (MulAut V)) : Subgroup G :=
  Subgroup.closure {g | ∃ a ∈ A, ∃ v : V, g = ((a v : V) : G) * ((v : V) : G)⁻¹}

structure IsCompList {A : Type} [Group A] (H : Subgroup A) (r : ℕ) (L : Fin r → Subgroup A) :
    Prop where
  injective : Function.Injective L
  isComp : ∀ i, IsComp (L i) H
  complete : ∀ D : Subgroup A, IsComp D H → ∃ i, L i = D

structure EvenSL2Setting (X R M V : Subgroup G) (n : ℕ) (F : Type) [Field F] : Prop where
  two_le : 2 ≤ n
  card_eq : Nat.card F = 2 ^ n
  sylow : IsSylowTwoOf R X
  not_normal : ¬ (R.subgroupOf X).Normal
  max : R ≤ M ∧ M < X ∧ ∀ Y : Subgroup G, R ≤ Y → Y < X → Y ≤ M
  reduced : IsTwoReducedIn X V
  thompson_ne : ⁅thompsonJ R, V⁆ ≠ ⊥
  nonsolvable : ¬ Group.IsSolvable (autOn X V)
  component : ∃ D : Subgroup (MulAut V), IsComp D (autOn X V) ∧
    Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] noncomputable def blockOf (X R V : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (D : Subgroup (MulAut V)) : Subgroup G :=
  oddOrderSubgroup ((oddOrderSubgroup X ⊔ baum R) ⊓ rhoPreimage V X hX D)

structure EvenSL2BlockOutput (X R V : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (n r : ℕ) (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  injective : Function.Injective fun i => blockOf X R V hX (Lc i)
  normal_LS : ((oddOrderSubgroup X ⊔ baum R).subgroupOf X).Normal
  normal_B : ∀ i,
    ((blockOf X R V hX (Lc i)).subgroupOf (oddOrderSubgroup X ⊔ baum R)).Normal
  permuted : ∀ t ∈ R, ∀ i, ∃ j,
    (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom = blockOf X R V hX (Lc j)
  transitive : ∀ i j, ∃ t ∈ R,
    (blockOf X R V hX (Lc i)).map (MulAut.conj t).toMonoidHom = blockOf X R V hX (Lc j)
  cComp : ∀ i, quasithinIsCComponent (blockOf X R V hX (Lc i)) X
  chi0 : ∀ i, IsChi0Block X (blockOf X R V hX (Lc i))
  gen : ∀ i, X = blockOf X R V hX (Lc i) ⊔ R
  perfect : ∀ i, ⁅blockOf X R V hX (Lc i), thompsonJ R⁆ = blockOf X R V hX (Lc i)
  image : ∀ i, autOn (blockOf X R V hX (Lc i)) V = Lc i
  coreComm : ∀ i,
    ⁅pCoreOf 2 (blockOf X R V hX (Lc i)), blockOf X R V hX (Lc i)⁆ = modComm V (Lc i) ∧
      ⁅pCoreOf 2 (oddOrderSubgroup X ⊔ baum R), blockOf X R V hX (Lc i)⁆ = modComm V (Lc i)
  commute : ∀ i j, i ≠ j →
    ⁅blockOf X R V hX (Lc i), blockOf X R V hX (Lc j)⁆ = ⊥
  product : oddOrderSubgroup X = ⨆ i, blockOf X R V hX (Lc i) ∧
    ∀ i, blockOf X R V hX (Lc i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), blockOf X R V hX (Lc j)) ≤
      centerIn (blockOf X R V hX (Lc i))
  kernel : X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X ∧
    (oddOrderSubgroup X ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (oddOrderSubgroup X ⊔ baum R)
  commutator : ⁅pCoreOf 2 (oddOrderSubgroup X ⊔ baum R), oddOrderSubgroup X⁆ =
      ⁅V, oddOrderSubgroup X⁆ ∧
    ⁅V, oddOrderSubgroup X⁆ = ⨆ i, modComm V (Lc i) ∧
    (⨆ i, modComm V (Lc i)) ≤ omegaOneCenterOf (pCoreOf 2 (oddOrderSubgroup X ⊔ baum R))
  type_lin : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
    ∀ i, IsLin2Type (blockOf X R V hX (Lc i)) n
  type_alt : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
    n = 2 ∧ ∀ i, IsAltType (blockOf X R V hX (Lc i)) 5
  rank : (∃ k : ℕ, r = 2 ^ k) ∧ r ≤ CFSG.pRank 3 X

@[expose] def EvenSL2ActualBlockProduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (hS : EvenSL2Setting X R M V n F), CharTwo X →
    (∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ X ≤ Subgroup.normalizer (Rc : Set G)) →
    ∀ (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), IsCompList (autOn X V) r Lc →
      EvenSL2BlockOutput X R V hS.reduced.2.1 n r Lc

end CFSG.QuasithinUnique.Setup.Lift
