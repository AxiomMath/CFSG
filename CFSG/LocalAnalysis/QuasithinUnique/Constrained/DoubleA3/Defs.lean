module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def conjClass (z : G) : Set G := {y | ∃ g : G, y = g⁻¹ * z * g}

@[expose] def layerOf (X : Subgroup G) : Subgroup G := sSup {K | IsComponentIn K X}

@[expose] def genFittingOf (X : Subgroup G) : Subgroup G := CFSG.Open.quasithinGenFitting X

@[expose] def frattiniOf (X : Subgroup G) : Subgroup G := (frattini X).map X.subtype

@[expose] def blockTC (T S L : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer (conjJoin S L : Set G)

@[expose] def blockU2 (L : Subgroup G) (s : G) : Subgroup G := conjR (blockU L) s

@[expose] def centralizerElem (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

@[expose] def sOne (S : Subgroup G) (x : G) : Subgroup G := baum S ⊔ Subgroup.zpowers x

@[expose] def InducesPerm {K : Subgroup G} (e : K ≃* alternatingGroup (Fin 6)) (g : G)
    (σ : Equiv.Perm (Fin 6)) : Prop :=
  ∀ k k' : K, (k' : G) = g⁻¹ * (k : G) * g →
    ((e k' : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      σ⁻¹ * ((e k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * σ

structure A3A3 {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (s : G) : Prop where
  cs : ConstrainedSetting G T M H S L
  a3 : IsAltType L 3
  s_mem : s ∈ S
  s_ne : conjR L s ≠ L
  join : conjJoin S L = L ⊔ conjR L s
  comm : ⁅L, conjR L s⁆ = ⊥

structure A3A3x {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) : Prop
    extends A3A3 T M H S L s where
  x_mem : x ∈ T
  x_not_mem : x ∉ S
  x_good : ¬ conjR (blockU L) x ≤ Subgroup.centralizer (blockU L : Set G)
  x_good₂ : ¬ conjR (blockU2 L s) x ≤ Subgroup.centralizer (blockU2 L s : Set G)
  z₁_gen : Subgroup.zpowers z₁ = blockU L ⊓ Subgroup.centralizer (baum S : Set G)
  z₁_ne : z₁ ≠ 1
  z₂_def : z₂ = s⁻¹ * z₁ * s
  x_comm₁ : x * z₁ = z₁ * x
  x_comm₂ : x * z₂ = z₂ * x

structure A3A3K {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G)
    (K : Subgroup G) : Prop extends A3A3x T M H S L s x z₁ z₂ where
  K_comp : IsComponentIn K (centralizerElem z₂)
  K_norm : centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G)
  K_comm : ⁅K, Subgroup.zpowers (z₁ * z₂)⁆ = K
  L_le_K : L ≤ K
  L_faithful : L ⊓ Subgroup.centralizer (K : Set G) = ⊥
  K_iso : Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥K ≃* PSL(2, ZMod 7))

end CFSG.QuasithinUnique.DoubleA3
