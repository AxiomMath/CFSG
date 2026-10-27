module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.CTP.StrongPLinear

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP

structure ModuleSpec (X : Type) [Group X] (p : ℕ) where
  n : ℕ
  m : ℕ
  a : Fin n → X
  g : Fin m → X
  M : Fin m → Matrix (Fin n) (Fin n) (ZMod p)
  comm : ∀ i j, a i * a j = a j * a i
  pow : ∀ i, a i ^ p = 1
  indep : ∀ c : Fin n → ZMod p,
    ((List.finRange n).map fun k => a k ^ (c k).val).prod = 1 → c = 0
  act : ∀ j i, g j * a i * (g j)⁻¹ = ((List.finRange n).map fun k => a k ^ (M j k i).val).prod

namespace ModuleSpec

variable {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p)

@[expose] def span : Subgroup X := Subgroup.closure (Set.range D.a)

@[expose] def NoFun : Prop :=
  ∀ v : Fin D.n → ZMod p, (∀ j, Matrix.vecMul v (D.M j) = v) → v = 0

@[expose] def NoAlt : Prop :=
  ∀ B : Matrix (Fin D.n) (Fin D.n) (ZMod p), B.transpose = -B →
    (∀ j, (D.M j).transpose * B * D.M j = B) → B = 0

@[expose] def Nondeg : Prop :=
  ∀ B : Matrix (Fin D.n) (Fin D.n) (ZMod p), B.transpose = -B →
    (∀ j, (D.M j).transpose * B * D.M j = B) → B ≠ 0 → IsUnit B.det

@[expose] def map {Y : Type} [Group Y] (f : X →* Y) (hf : Function.Injective f) :
    ModuleSpec Y p where
  n := D.n
  m := D.m
  a i := f (D.a i)
  g j := f (D.g j)
  M := D.M
  comm i j := by rw [← map_mul, ← map_mul, D.comm]
  pow i := by rw [← map_pow, D.pow, map_one]
  indep c hc := D.indep c (hf (by simpa [map_list_prod, List.map_map, Function.comp_def] using hc))
  act j i := by
    simp only [← map_inv, ← map_mul, D.act, map_list_prod, List.map_map, Function.comp_def,
      map_pow]

theorem map_span {Y : Type} [Group Y] (f : X →* Y) (hf : Function.Injective f) :
    (D.map f hf).span = D.span.map f := by
  simp only [span, map, MonoidHom.map_closure, ← Set.range_comp, Function.comp_def]

end ModuleSpec

@[expose] def ModuleDatum (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ D : ModuleSpec X p, p ≤ D.n ∧ D.NoAlt ∧ D.NoFun ∧
    ∃ P : Sylow p X, (P : Subgroup X) ≤ Subgroup.normalizer (D.span : Set X)

@[expose] def AbelianSylowDatum (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ D : ModuleSpec X p, D.n ≤ 4 ∧ D.NoFun ∧ D.Nondeg ∧ ¬ p ∣ D.span.index

@[expose] def RankLiftDatum (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ (r : ℕ) (D : Fin r → ModuleSpec X p) (P : Subgroup X), IsPGroup p P ∧
    (∀ i, (D i).span ≤ P) ∧
    (∀ i, (3 ≤ (D i).n ∧ (D i).NoAlt) ∨ (2 ≤ (D i).n ∧ (D i).NoAlt ∧ (D i).NoFun)) ∧
    Subgroup.closure (⋃ i, Set.range (D i).g) = ⊤

@[expose] def SporadicSmallData (X : Type) [Group X] : Prop :=
  Nat.card (Outer X) ≤ 2 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X)

@[expose] def SporadicAlphaData (X : Type) [Group X] : Prop :=
  Nat.card (Outer X) ≤ 2 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
    (¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X)) ∨
      ModuleDatum X p ∨ AbelianSylowDatum X p ∨ RankLiftDatum X p

@[expose] def CoverModuleLemma : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X : Type) [Group X] (π : K →* X),
    Function.Surjective π → π.ker = Subgroup.center K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ModuleDatum X p → ∀ T : Sylow p K, ∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧
      (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) ∧ Open.IsElemAbelian p A ∧
      p ^ (p + 1) ≤ Nat.card A

@[expose] def CoverAbelianSylowLemma : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X : Type) [Group X] (π : K →* X),
    Function.Surjective π → π.ker = Subgroup.center K → Group.IsPerfect K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) →
    IsCyclic (Subgroup.center K) → AbelianSylowDatum X p →
    ∀ T : Sylow p K, (∀ t ∈ (T : Subgroup K), t ^ p = 1) ∧ Open.pRank p (T : Subgroup K) ≤ 3

@[expose] def CoverRankLiftLemma : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (X : Type) [Group X] [Nontrivial X] (π : K →* X),
    Function.Surjective π → π.ker = Subgroup.center K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    RankLiftDatum X p →
    ∀ T : Sylow p K, Open.GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K)

end CFSG.AGLEmbedding
