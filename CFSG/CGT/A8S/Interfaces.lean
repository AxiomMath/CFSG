module

public import CFSG.CGT.A8S.Stmt
public import CFSG.Certificates.CosetTablePresented
public import CFSG.CGT.A8S.RelData

public section

namespace CFSG.CGT.A8S

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable

@[expose] def tGenA8 (j : Fin 3) : PG 5 relsN0A8 :=
  PresentedGroup.of ⟨2 + j.val, by omega⟩

@[expose] def genTupleA8 {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) : Fin 6 → G :=
  fun i => if h : i.val < 5 then
    ((ψ (PresentedGroup.of ⟨i.val, h⟩) : ↥(Subgroup.normalizer (T : Set G))) : G) else g

structure T1ConfigA8 {G : Type} [Group G] (T T₁ : Subgroup G) where
  ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G))
  map_t : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGenA8)) =
    T.subgroupOf (Subgroup.normalizer (T : Set G))
  g : G
  conj_g : conjSubgroup g T = T₁
  rel : ∀ r ∈ thetaRelsA8, evalA8 (genTupleA8 ψ g) r = 1

@[expose] def T1ConfigA8.gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1ConfigA8 T T₁) :
    Fin 6 → G :=
  genTupleA8 c.ψ c.g

@[expose] def N0StatementA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), A8CtxHyp T T₁ →
    ∃ ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G)),
      Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGenA8)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G))

@[expose] def L2StatementA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), A8CtxHyp T T₁ →
    Nonempty (T1ConfigA8 T T₁)

@[expose] def R3StatementA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), A8CtxHyp T T₁ →
    ∀ c : T1ConfigA8 T T₁, ∀ r ∈ ruRelA8, evalA8 c.gens r = 1

@[expose] def R5StatementA8 : Prop :=
  ∀ (H : Type) [Group H] (e : Fin 6 → H), (∀ r ∈ a8Rels, evalA8 e r = 1) →
    Subgroup.closure (Set.range e) ≠ ⊥ →
      ∃ φ : ↥(Subgroup.closure (Set.range e)) ≃* alternatingGroup (Fin 8),
        ∀ i, ((φ ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : alternatingGroup (Fin 8)) :
          Equiv.Perm (Fin 8)) = a8Perm i

end CFSG.CGT.A8S
