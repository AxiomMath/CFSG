module

public import CFSG.CGT.Timmesfeld75.Sec5OutBar
public import CFSG.CGT.M24R.RelData
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable

structure M24CtxHyp {G : Type} [Group G] (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  card16 : Nat.card T = 16
  inf_bot : T ⊓ T₁ = ⊥
  conj : ∃ s : G, T₁ = conjSubgroup s T
  norm1 : Nat.card (normIn T T₁) = 4
  norm2 : Nat.card (normIn T₁ T) = 4
  cent_le : ∀ d ∈ T, d ≠ 1 →
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)
  cent_eq : Subgroup.centralizer (T : Set G) = T
  trans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
    ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y
  quot : Nonempty (NQuot T ≃* alternatingGroup (Fin 8))
  compl : ∃ L : Subgroup G, L ⊓ T = ⊥ ∧ T ⊔ L = Subgroup.normalizer (T : Set G)

@[expose] def tGen8 (j : Fin 4) : PG 10 relsN8Ten :=
  PresentedGroup.of ⟨6 + j.val, by omega⟩

@[expose] def genTuple8 {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) : Fin 11 → G :=
  fun i => if h : i.val < 10 then
    ((ψ (PresentedGroup.of ⟨i.val, h⟩) : ↥(Subgroup.normalizer (T : Set G))) : G) else g

structure T1Config8 {G : Type} [Group G] (T T₁ : Subgroup G) where
  ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G))
  map_t : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
    T.subgroupOf (Subgroup.normalizer (T : Set G))
  g : G
  conj_g : conjSubgroup g T = T₁
  rel : ∀ r ∈ thetaRels8, evalW (genTuple8 ψ g) r = 1

@[expose] def T1Config8.gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config8 T T₁) :
    Fin 11 → G :=
  genTuple8 c.ψ c.g

@[expose] def N8Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), M24CtxHyp T T₁ →
    ∃ ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G)),
      Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G))

@[expose] def L2Statement8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), M24CtxHyp T T₁ →
    Nonempty (T1Config8 T T₁)

@[expose] def R3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), M24CtxHyp T T₁ →
    ∀ c : T1Config8 T T₁, ∀ r ∈ ruRel, evalW c.gens r = 1

@[expose] def R24Statement : Prop :=
  ∀ (H : Type) [Group H] (e : Fin 11 → H), (∀ r ∈ m24Rels, evalW e r = 1) →
    Subgroup.closure (Set.range e) ≠ ⊥ →
      Nonempty (Subgroup.closure (Set.range e) ≃* CFSG.Blueprint.NativeSporadic.M24)

end CFSG.CGT.M24R
