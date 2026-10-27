module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs
public import CFSG.GH74.GLS.Stage12.Interface

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

@[expose] def IsRigidOfType (Lh : Type) [Group Lh] (z : G) (K : Subgroup G) : Prop :=
  IsPRigid 2 z K ∧ Nonempty (HatT K ≃* Lh)

@[expose] def RigidSet (Lh : Type) [Group Lh] (z : G) : Set (Subgroup G) :=
  {K | IsRigidOfType Lh z K}

@[expose] def Kz (Lh : Type) [Group Lh] (z : G) : Subgroup G := sSup (RigidSet Lh z)

@[expose] def NormsAll (Lh : Type) [Group Lh] (z t : G) : Prop :=
  ∀ K ∈ RigidSet Lh z, t ∈ normalizer (K : Set G)

@[expose] def IsFourTransp (X : Type) [Group X] (n : ℕ) (x : X) : Prop :=
  ∃ e : (X ⧸ center X) ≃* alternatingGroup (Fin n),
    ((e (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType =
      Multiset.replicate 4 2

end Notation

structure Hyp9 (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] : Prop where
  std : Std0 G
  cover : ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt Lh n
  pair : ∃ (x : G) (L : Subgroup G), IsTwoTerminal x L ∧ Nonempty (HatT L ≃* Lh)

structure Good92 (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (K : Subgroup G) :
    Prop where
  z_ord : orderOf z = 2
  t_ord : orderOf t = 2
  t_cen : t ∈ centralizer ({z} : Set G)
  K_rigid : IsRigidOfType Lh z K
  z_mem : z ∈ K
  t_conj : ∃ g : G, g⁻¹ * t * g ∈ zStar (Kz Lh z)
  comm_eq : ⁅K, zpowers t⁆ = K
  comm_nle : ¬ ⁅K, zpowers t⁆ ≤ pPrimeCoreOf 2 K

@[expose] def PrefT (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) : Prop :=
  (∃ (t' : G) (K' : Subgroup G), Good92 G Lh z t' K' ∧ NormsAll Lh z t') → NormsAll Lh z t

structure Std9 (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G) :
    Prop extends Hyp9 G Lh, Good92 G Lh z t K where
  pref : PrefT G Lh z t
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))
  t_mem : t ∈ S
  t_ext : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({t} : Set G))
    (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))

end CFSG.GH74.GLS.Stage1.Thm4
