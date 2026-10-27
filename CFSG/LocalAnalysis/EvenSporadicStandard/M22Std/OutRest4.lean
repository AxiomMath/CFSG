module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest3

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

structure OuterSituation (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G)
    (T₁ : Subgroup (centralizer ({z} : Set G))) (F : Subgroup (L ⧸ center L))
    (tb : L ⧸ center L) (Q : Sylow 2 G) (x : G) (L1 : Subgroup G) : Prop where
  data : OutData L z t T₁ F tb
  std : StdHyp G L
  sporadic : IsSporadic L .M22
  cyclic : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  rel : (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2
  T_le : (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) ≤ (Q : Subgroup G)
  x_mem : x ∈ (Q : Subgroup G)
  x_not_mem : x ∉ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G)
  x_norm : x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G)
  x_z : x * z * x⁻¹ = z * t
  x_t : x * t * x⁻¹ = t
  t_central : ∀ q ∈ (Q : Subgroup G), q * t = t * q
  Q_inf : (Q : Subgroup G) ⊓ centralizer ({z} : Set G) =
    (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G)
  z_comm : z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype
  one : OutOne L z (liftSub F)
  outer_inv : ∃ y ∈ centralizer ({z} : Set G), y ∉ L ⊔ zpowers z ∧ y * y = 1
  complement : ∃ A : Subgroup G, L ≤ A ∧ A ≤ centralizer ({z} : Set G) ∧ z ∉ A ∧
    A ⊔ zpowers z = centralizer ({z} : Set G) ∧ (L.subgroupOf A).index = 2
  transitive : ∀ f ∈ liftSub F, ∃ c : G, (∀ y, y ∈ liftSub F ⊔ zpowers z ↔
    c * y * c⁻¹ ∈ liftSub F ⊔ zpowers z) ∧ c * z * c⁻¹ = z * f
  card_K : Nat.card (Ksub z (liftSub F)) = 512
  center_K : ∀ k ∈ Ksub z (liftSub F),
    (∀ k' ∈ Ksub z (liftSub F), k * k' = k' * k) ↔ k ∈ liftSub F
  z_not_sq : ∀ g : G, g * g ≠ z
  K : KStructure z (liftSub F) L1

@[expose] def Fin77aOuterXbar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (z t : G)
    (T₁ : Subgroup (centralizer ({z} : Set G))) (F : Subgroup (L ⧸ center L))
    (tb : L ⧸ center L) (Q : Sylow 2 G) (x : G) (L1 : Subgroup G),
    OuterSituation G L z t T₁ F tb Q x L1 →
    ∃ hz : z ∈ normalizer (L1 : Set G), Nonempty (centralizer
      ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1)) ≃*
        Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))

@[expose] def Fin77aOuterRest₄ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (z t : G)
    (T₁ : Subgroup (centralizer ({z} : Set G))) (F : Subgroup (L ⧸ center L))
    (tb : L ⧸ center L) (Q : Sylow 2 G) (x : G) (L1 : Subgroup G),
    OuterSituation G L z t T₁ F tb Q x L1 →
    (∃ hz : z ∈ normalizer (L1 : Set G), Nonempty (centralizer
      ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1)) ≃*
        Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))) → False

theorem fin77aOuterRest₃_of_split (hX : Fin77aOuterXbar) (hR : Fin77aOuterRest₄) :
    Fin77aOuterRest₃ := by
  intro G _ _ _ L z t T₁ F tb Q x L1 hD hS hL hcyc hrel hTQ hxQ hxT hxN hxz hxt htQ hQ hzc hO hy hA
    htr hcard hcen hsq hK
  have hsit : OuterSituation G L z t T₁ F tb Q x L1 :=
    ⟨hD, hS, hL, hcyc, hrel, hTQ, hxQ, hxT, hxN, hxz, hxt, htQ, hQ, hzc, hO, hy, hA, htr, hcard,
      hcen, hsq, hK⟩
  exact hR G L z t T₁ F tb Q x L1 hsit (hX G L z t T₁ F tb Q x L1 hsit)

end CFSG.EvenSporadicStandard.M22Std
