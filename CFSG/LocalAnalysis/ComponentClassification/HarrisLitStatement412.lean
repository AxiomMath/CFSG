module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42

variable {X : Type} [Group X]

structure IsLemma412 (L : Subgroup X) (p f : ℕ) (β : X) (tb : MBar β) : Prop where
  layerIn_centralizer : GSThmB.layerIn (centralizer ({tb} : Set (MBar β))) = KBar L β
  layerIn_layer_centralizer :
    GSThmB.layerIn (layer (MBar β) ⊓ centralizer ({tb} : Set (MBar β))) = KBar L β
  betaBar_mem : betaBar β ∈ centralizer (KBar L β : Set (MBar β)) ∧ betaBar β ∈ center (MBar β)
  sylow_centralizer : ∀ R : Subgroup (MBar β),
    IsSylowOf 2 R (centralizer (KBar L β : Set (MBar β))) →
      Nat.card R = 4 ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n)
  lemma46c : IsLemma46c L β
  layer_eq_commutator : layer (MBar β) = ⁅layer (MBar β), zpowers tb⁆
  lemma46d : IsLemma46d p f L β tb
  oddCore_KBar : pPrimeCore 2 ↥(KBar L β) = ⊥
  commutator_conj_ne_bot : ∀ g : MBar β,
    ⁅KBar L β, (KBar L β).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥
  pCore_sup_le : pCore 2 (MBar β) ⊔ zpowers tb ≤ centralizer (KBar L β : Set (MBar β))
  pCore_inf_centralizer : pCore 2 (MBar β) ⊓ centralizer {tb} = zpowers (betaBar β)
  pCore_eq : pCore 2 (MBar β) = solvableRadical (MBar β) ∧
    solvableRadical (MBar β) = centralizer (layer (MBar β) : Set (MBar β))
  pCore_shape : IsCyclic ↥(pCore 2 (MBar β)) ∨
    ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(pCore 2 (MBar β)) ≃* DihedralGroup (2 ^ k))
  pCore_sup_shape : Nat.card ↥(pCore 2 (MBar β) ⊔ zpowers tb) = 4 ∨
    (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥(pCore 2 (MBar β) ⊔ zpowers tb) ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧
        Nonempty (↥(pCore 2 (MBar β) ⊔ zpowers tb) ≃* CFSG.Open.SemidihedralGroup n)
  oddGenerated_le :
    closure {x : MBar β | Odd (orderOf x)} ≤ centralizer (pCore 2 (MBar β) : Set (MBar β))
  KBar_lt_layer : KBar L β < layer (MBar β)
  of_semidihedral : (∃ n : ℕ, 4 ≤ n ∧
      Nonempty (↥(pCore 2 (MBar β) ⊔ zpowers tb) ≃* CFSG.Open.SemidihedralGroup n)) →
    IsCyclic ↥(pCore 2 (MBar β)) ∧
      IsSylowOf 2 (pCore 2 (MBar β) ⊔ zpowers tb) (centralizer (KBar L β : Set (MBar β)))
  of_dihedral : (∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(pCore 2 (MBar β)) ≃* DihedralGroup (2 ^ k))) →
    IsSylowOf 2 (pCore 2 (MBar β) ⊔ zpowers tb) (centralizer (KBar L β : Set (MBar β)))

@[expose] def Harris412Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ)
      (hs : Setting46e t L p f S w z V i j),
        IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)

end CFSG.ComponentClassification.HarrisLit
