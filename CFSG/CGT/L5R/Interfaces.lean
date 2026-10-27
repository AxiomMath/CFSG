module

public import CFSG.CGT.M24S.Type4
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.CGT.L5R.RelData
public import CFSG.CGT.M24R.Interfaces

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable CFSG.CGT.M24R

structure L52CtxHyp {G : Type} [Group G] (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  card16 : Nat.card T = 16
  inf_bot : T ⊓ T₁ = ⊥
  conj : ∃ s : G, T₁ = conjSubgroup s T
  norm1 : Nat.card (normIn T T₁) = 8
  norm2 : Nat.card (normIn T₁ T) = 8
  cent_le : ∀ d ∈ T, d ≠ 1 →
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)
  cent_eq : Subgroup.centralizer (T : Set G) = T
  trans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
    ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y
  quot : Nonempty (NQuot T ≃* alternatingGroup (Fin 8))
  compl : ∃ L : Subgroup G, L ⊓ T = ⊥ ∧ T ⊔ L = Subgroup.normalizer (T : Set G)
  noType4 : ¬ CFSG.CGT.M24S.HasType4 T

structure T1ConfigL {G : Type} [Group G] (T T₁ : Subgroup G) where
  ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G))
  map_t : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
    T.subgroupOf (Subgroup.normalizer (T : Set G))
  g : G
  conj_g : conjSubgroup g T = T₁
  rel : ∀ r ∈ thetaRelsL, evalW (genTuple8 ψ g) r = 1

@[expose] def T1ConfigL.gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1ConfigL T T₁) :
    Fin 11 → G :=
  genTuple8 c.ψ c.g

@[expose] def N8StatementL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), L52CtxHyp T T₁ →
    ∃ ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G)),
      Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G))

@[expose] def L2StatementL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), L52CtxHyp T T₁ →
    Nonempty (T1ConfigL T T₁)

@[expose] def R3StatementL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), L52CtxHyp T T₁ →
    ∀ c : T1ConfigL T T₁, ∀ r ∈ ruRelL, evalW c.gens r = 1

@[expose] def R5Statement : Prop :=
  ∀ (H : Type) [Group H] (e : Fin 11 → H), (∀ r ∈ l52Rels, evalW e r = 1) →
    Subgroup.closure (Set.range e) ≠ ⊥ →
      ∃ φ : ↥(Subgroup.closure (Set.range e)) ≃* CFSG.GroupTheory.GL52.G52,
        ∀ i, ((φ ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : CFSG.GroupTheory.GL52.G52) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) = l52M i

end CFSG.CGT.L5R
