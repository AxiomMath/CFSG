module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace QPUJ

@[expose] def autFixed {M : Type*} [Group M] (E : Subgroup (MulAut M)) : Subgroup M where
  carrier := {m | ∀ e ∈ E, e m = m}
  one_mem' := fun e _ => map_one e
  mul_mem' := fun ha hb e he => by rw [map_mul, ha e he, hb e he]
  inv_mem' := fun ha e he => by rw [map_inv, ha e he]

theorem mem_autFixed {M : Type*} [Group M] {E : Subgroup (MulAut M)} {m : M} :
    m ∈ autFixed E ↔ ∀ e ∈ E, e m = m :=
  Iff.rfl

end QPUJ

@[expose] def QPUJConfig (M : Type) [Group M] [Finite M] (p' f' p f : ℕ) : Prop :=
  IsQuasisimple M ∧ IsPGroup 2 (center M) ∧ p'.Prime ∧ p' ≠ 2 ∧ 1 ≤ f' ∧ 5 ≤ p' ^ f' ∧
    p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ p = p' ∧ f = f' ∧
    ∃ (E : Subgroup (MulAut M)) (L : Subgroup M) (t : M) (J J₀ : Subgroup M),
      IsPGroup 2 E ∧ L ≤ QPUJ.autFixed E ∧ IsPComponent 2 (L.subgroupOf (QPUJ.autFixed E)) ∧
      L ≠ ⊤ ∧ Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f' ∧
      t ∈ L ∧ t * t = 1 ∧ t ∉ center M ∧
      J ≤ centralizer ({t} : Set M) ∧ IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M))) ∧
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f ∧
      J₀ ≤ L ∧ J₀ ≤ J ∧ J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J

@[expose] def CFQPUJStatement71 : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ Blueprint.Catalog (M ⧸ center M)

@[expose] def CFQPUJExc : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ Blueprint.ExceptionalRep (M ⧸ center M)

@[expose] def CFQPUJAlt : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((M ⧸ center M) ≃* alternatingGroup (Fin n))

@[expose] def CFQPUJClassical : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n f'' : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel (M ⧸ center M) t n p' f''

@[expose] def CFQPUJCrossChar : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n r f'' : ℕ), r ≠ p' ∧
      Assembly.LowTwoRank.StatedClassicalModel (M ⧸ center M) t n r f''

@[expose] def CFQPUJSpor : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ Blueprint.NativeSporadic.SporadicRep (M ⧸ center M)

theorem cfQPUJStatement71_of_rows (hE : CFQPUJExc) (hA : CFQPUJAlt) (hC : CFQPUJClassical)
    (hX : CFQPUJCrossChar) (hS : CFQPUJSpor) : CFQPUJStatement71 := by
  intro M _ _ p' f' p f hc hcat
  rcases hcat with ⟨r, -, ⟨e⟩⟩ | hal | ⟨t, n, r, f'', hmod⟩ | hexc | hspor
  · obtain ⟨-, -, u, v, huv⟩ := hc.1
    apply huv
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact hA M p' f' p f hc hal
  · by_cases hr : r = p'
    · subst hr
      exact hC M r f' p f hc ⟨t, n, f'', hmod⟩
    · exact hX M p' f' p f hc ⟨t, n, r, f'', hr, hmod⟩
  · exact hE M p' f' p f hc hexc
  · exact hS M p' f' p f hc hspor

end CFSG.ComponentClassification.GSThmB
