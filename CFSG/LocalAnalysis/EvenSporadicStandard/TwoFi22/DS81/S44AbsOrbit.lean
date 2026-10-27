module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Spec
public import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Abs

open Subgroup MulAction

variable {V : Type} [CommGroup V] {X M : Subgroup (MulAut V)} {t : V} {O : Fin 5 → Set V}

theorem mem_orbit_iff_exists {v w : V} : w ∈ orbit X v ↔ ∃ g ∈ X, g v = w := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem apply_mem_orbit {g : MulAut V} (hg : g ∈ X) {v w : V} (h : w ∈ orbit X v) :
    g w ∈ orbit X v := by
  obtain ⟨k, hk, rfl⟩ := mem_orbit_iff_exists.1 h
  exact mem_orbit_iff_exists.2 ⟨g * k, X.mul_mem hg hk, rfl⟩

theorem mem_orbit_of_apply {g : MulAut V} (hg : g ∈ X) {v w : V} (h : g w ∈ orbit X v) :
    w ∈ orbit X v := by
  simpa using apply_mem_orbit (X.inv_mem hg) h

theorem one_notMem_orbit {v : V} (hv : v ≠ 1) : (1 : V) ∉ orbit X v := by
  intro h
  obtain ⟨g, -, hg⟩ := mem_orbit_iff_exists.1 h
  exact hv (g.injective (by rw [hg, map_one]))

theorem subset_of_mem {Z : Set V} (hZ : ∀ m ∈ M, ∀ z ∈ Z, m z ∈ Z) (hO : OrbitData M t O)
    {i : Fin 5} {z : V} (hz : z ∈ O i) (hzZ : z ∈ Z) : O i ⊆ Z := by
  obtain ⟨x, hx⟩ := hO.isOrbit i
  rw [hx] at hz ⊢
  rw [← MulAction.orbit_eq_iff.2 hz]
  rintro w ⟨⟨m, hm⟩, rfl⟩
  exact hZ m hm z hzZ

theorem orbit_invariant (hMX : M ≤ X) (v : V) :
    ∀ m ∈ M, ∀ z ∈ orbit X v, m z ∈ orbit X v :=
  fun _ hm _ hz => apply_mem_orbit (hMX hm) hz

theorem card_eq_mul [Finite V] :
    Nat.card X = (orbit X t).ncard * Nat.card ↥(X ⊓ stabilizer (MulAut V) t) := by
  have : Nat.card (stabilizer X t) = Nat.card ↥(X ⊓ stabilizer (MulAut V) t) :=
    Nat.card_congr
      { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← this, ← MulAction.index_stabilizer X t, mul_comm, Subgroup.card_mul_index]

theorem ncard_eq_sum [Finite V] (hO : OrbitData M t O) {Z : Set V}
    (hZ : ∀ m ∈ M, ∀ z ∈ Z, m z ∈ Z) (h1 : (1 : V) ∉ Z) (ht : t ∉ Z) (p : Fin 5 → Prop)
    [DecidablePred p] (hp : ∀ i, p i ↔ O i ⊆ Z) :
    Z.ncard = ∑ i, if p i then ![22, 22, 231, 231, 1540] i else 0 := by
  have hcov : Z = ⋃ i, (O i ∩ Z) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      have hz1 : z ≠ 1 := fun h => h1 (h ▸ hz)
      have hzt : z ≠ t := fun h => ht (h ▸ hz)
      rcases hO.cover z hz1 with h | ⟨i, hi⟩
      · exact absurd h hzt
      · exact ⟨i, hi, hz⟩
    · rintro ⟨i, -, hz⟩
      exact hz
  have hdisj : Pairwise (Function.onFun Disjoint fun i => O i ∩ Z) := fun i j hij =>
    (hO.disjoint i j hij).mono Set.inter_subset_left Set.inter_subset_left
  calc Z.ncard = (⋃ i, (O i ∩ Z)).ncard := congrArg Set.ncard hcov
    _ = ∑ᶠ i, (O i ∩ Z).ncard := Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) hdisj
    _ = ∑ i, (O i ∩ Z).ncard := finsum_eq_sum_of_fintype _
    _ = _ := Finset.sum_congr rfl fun i _ => by
        by_cases hi : p i
        · rw [ite_eq_left hi, Set.inter_eq_left.2 ((hp i).1 hi), hO.ncard i]
        · rw [ite_eq_right hi]
          have : O i ∩ Z = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨hzO, hzZ⟩
            exact hi ((hp i).2 (subset_of_mem hZ hO hzO hzZ))
          rw [this, Set.ncard_empty]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Abs
