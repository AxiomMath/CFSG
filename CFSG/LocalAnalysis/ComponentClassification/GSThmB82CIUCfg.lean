module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def IsL4U4Mod4 (Y : Type) [Group Y] (p f : ℕ) : Prop :=
  Blueprint.LieModel Y .PSL 4 p f ∧ p ^ f % 4 = 3 ∨ Blueprint.LieModel Y .PSU 4 p f ∧ p ^ f % 4 = 1

@[expose] def QPUJ6Config (M : Type) [Group M] [Finite M] (p f : ℕ) : Prop :=
  IsQuasisimple M ∧ IsPGroup 2 (center M) ∧ p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ ¬ (p = 3 ∧ f = 1) ∧
    ∃ (E : Subgroup (MulAut M)) (L : Subgroup M) (t : M) (J J₀ : Subgroup M),
      IsPGroup 2 E ∧ L ≤ QPUJ.autFixed E ∧ IsPComponent 2 (L.subgroupOf (QPUJ.autFixed E)) ∧
      L ≠ ⊤ ∧ IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f ∧
      t ∈ L ∧ t * t = 1 ∧ t ∉ center M ∧
      J ≤ centralizer ({t} : Set M) ∧ IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M))) ∧
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f) ∧
      J₀ ≤ L ∧ J₀ ≤ J ∧ J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J

@[expose] def CFQPUJ6Statement : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), QPUJ6Config M p f →
    ¬ Blueprint.Catalog (M ⧸ center M)

@[expose] def CFQPUJ6Exc : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), QPUJ6Config M p f →
    ¬ Blueprint.ExceptionalRep (M ⧸ center M)

@[expose] def CFQPUJ6Alt : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), QPUJ6Config M p f →
    ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((M ⧸ center M) ≃* alternatingGroup (Fin n))

@[expose] def CFQPUJ6Classical : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), QPUJ6Config M p f →
    ¬ ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n f'' : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel (M ⧸ center M) t n p f''

@[expose] def CFQPUJ6CrossChar : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), QPUJ6Config M p f →
    ¬ ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n r f'' : ℕ), r ≠ p ∧
      Assembly.LowTwoRank.StatedClassicalModel (M ⧸ center M) t n r f''

@[expose] def CFQPUJ6Spor : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), QPUJ6Config M p f →
    ¬ Blueprint.NativeSporadic.SporadicRep (M ⧸ center M)

theorem cfQPUJ6Statement_of_rows (hE : CFQPUJ6Exc) (hA : CFQPUJ6Alt) (hC : CFQPUJ6Classical)
    (hX : CFQPUJ6CrossChar) (hS : CFQPUJ6Spor) : CFQPUJ6Statement := by
  intro M _ _ p f hc hcat
  rcases hcat with ⟨r, -, ⟨e⟩⟩ | hal | ⟨t, n, r, f'', hmod⟩ | hexc | hspor
  · obtain ⟨-, -, u, v, huv⟩ := hc.1
    apply huv
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact hA M p f hc hal
  · by_cases hr : r = p
    · subst hr
      exact hC M r f hc ⟨t, n, f'', hmod⟩
    · exact hX M p f hc ⟨t, n, r, f'', hr, hmod⟩
  · exact hE M p f hc hexc
  · exact hS M p f hc hspor

end CFSG.ComponentClassification.GSThmB
