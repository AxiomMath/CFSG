module

public import CFSG.GH74.GLS.Types
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG CFSG.Blueprint

theorem zpow_eq_one_or_self {M : Type*} [Group M] {z : M} (hz2 : z ^ 2 = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [hz2]
  · right
    rw [zpow_add, zpow_mul]
    simp [hz2]

structure Hyp (G : Type) [Group G] [Finite G] : Prop where
  isSimple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Catalog G
  evenType : GLS.IsEvenType G
  quasithin : Assembly.evenRank G ≤ 2
  notEvenChar : ¬ Assembly.Quasithin.quasithinEvenCharacteristic G

variable {G : Type} [Group G]

theorem Hyp.e1 [Finite G] (h : Hyp G) :
    ∀ x : G, orderOf x = 2 → pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥ :=
  h.evenType.2.1

structure Pair (T : Sylow 2 G) (z : G) (L : Subgroup G) : Prop where
  orderOf_eq : orderOf z = 2
  mem_sylow : z ∈ (T : Subgroup G)
  central : ∀ t ∈ (T : Subgroup G), t * z = z * t
  isComp : GLS.IsCompIn (centralizer ({z} : Set G)) L

@[expose] def omegaOne (R : Subgroup G) : Subgroup G :=
  closure {x : G | x ∈ R ∧ x ^ 2 = 1}

@[expose] def InDelta (K K' : Subgroup G) : Prop :=
  (∃ g : G, K' = K.map (MulAut.conj g).toMonoidHom) ∧ K' ≠ K ∧
    Even (Nat.card ↥(K' ⊓ normalizer (K : Set G)))

@[expose] def InDelta0 (K L K' : Subgroup G) : Prop :=
  InDelta K K' ∧ ∀ R : Subgroup G, QuasithinUnique.IsSylowTwoOf R (K' ⊓ normalizer (K : Set G)) →
    omegaOne R ≤ K ⊔ L

@[expose] def IsBenderComp (L : Subgroup G) : Prop :=
  Open.fusionIsBenderGroup (↥L ⧸ center ↥L)

@[expose] def JankoLocal (z : G) (L : Subgroup G) : Prop :=
  z ∉ L ∧ Nonempty (↥L ≃* alternatingGroup (Fin 5)) ∧
    centralizer ({z} : Set G) = zpowers z ⊔ L

end CFSG.GH74.AS16
