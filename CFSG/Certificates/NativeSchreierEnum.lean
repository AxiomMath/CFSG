module

public import CFSG.Certificates.SchreierTransversalProduct
public import Certificates.Data.CFSGNative.Schreier.Enum3
public import CFSG.Certificates.NativeValidSchreier

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem prod_ofFn_eq_of_one {G : Type*} [Monoid G] {m k : ℕ} (hk : k ≤ m) (f : Fin m → G)
    (h1 : ∀ i : Fin m, k ≤ i.val → f i = 1) :
    (List.ofFn f).prod = (List.ofFn fun i : Fin k => f (Fin.castLE hk i)).prod := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [List.ofFn_add, List.prod_append]
  have : (List.ofFn fun j : Fin r => f (Fin.natAdd k j)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact h1 _ (by simp)
  rw [this, mul_one]

namespace ChainArrays

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem orbitPoints_spec {i : ℕ} (hi : i < Q.baseCount) {x : Fin n}
    (hx : x ∈ Q.orbitPoints ⟨i, hi⟩) :
    (lev n S base i).pos[(x : ℕ)]! < (lev n S base i).pts.size ∧
      levPts Q S base i (lev n S base i).pos[(x : ℕ)]! = x ∧
      (Q.transversal? ⟨i, hi⟩ x).getD 1 = levT n S base i (lev n S base i).pos[(x : ℕ)]! := by
  have hk : (lev n S base i).pos[(x : ℕ)]! < (lev n S base i).pts.size := by
    by_contra hk
    have hnone := hA.transversal_eq_none hF hi hk
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? x).isSome = true at hx
    rw [hnone] at hx
    simp at hx
  have hpts : levPts Q S base i (lev n S base i).pos[(x : ℕ)]! = x := by
    apply Fin.ext
    rw [hA.levPts_val hF hi hk, (hA.levelFacts hF hi).pts_pos _ x.2 hk]
  refine ⟨hk, hpts, ?_⟩
  have ht := hA.transversal_of_lt hF hi hk
  rw [hpts] at ht
  change ((Q.orbitSearch ⟨i, hi⟩).transversal? x).getD 1 = _
  rw [ht, Option.getD_some]

theorem levT_mem {i : ℕ} (hi : i < Q.baseCount) {k : ℕ} (hk : k < (lev n S base i).pts.size) :
    levT n S base i k ∈ Q.levelSubgroup i := by
  have ht := hA.transversal_of_lt hF hi hk
  have hx : levPts Q S base i k ∈ Q.orbitPoints ⟨i, hi⟩ := by
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).isSome = true
    rw [ht]
    rfl
  have h := (Q.transversal_getD_spec ⟨i, hi⟩ _ hx).2.1
  change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).getD 1 ∈ _ at h
  rwa [ht, Option.getD_some] at h

theorem levT_zero {i : ℕ} (hi : i < Q.baseCount) : levT n S base i 0 = 1 :=
  eq_of_eqA (hA.rep_levT hF hi (hA.levelFacts hF hi).pos) rep_idA
    (hA.levelFacts hF hi).tr_zero

theorem prod3_apply (h3 : 3 ≤ Q.baseCount) {a b c : ℕ} (ha : a < (lev n S base 0).pts.size)
    (hb : b < (lev n S base 1).pts.size) (hc : c < (lev n S base 2).pts.size) (p : Fin n) :
    ((levT n S base 0 a * levT n S base 1 b * levT n S base 2 c) p : ℕ) =
      tr3 (rawLevels n S base) a b c p := by
  have e : tr3 (rawLevels n S base) a b c p = ((lev n S base 0).tr[a]!)[
      ((lev n S base 1).tr[b]!)[((lev n S base 2).tr[c]!)[(p : ℕ)]!]!]! := rfl
  rw [e, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, (hA.rep_levT hF (by omega) hc) p,
    (hA.rep_levT hF (by omega) hb) (levT n S base 2 c p),
    (hA.rep_levT hF (by omega) ha) (levT n S base 1 b (levT n S base 2 c p))]

end Facts

theorem exists_prod3 (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) (h3 : 3 ≤ Q.baseCount)
    (h1 : ∀ i, 3 ≤ i → i < Q.baseCount → (lev n S base i).pts.size = 1)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) :
    ∃ a < (lev n S base 0).pts.size, ∃ b < (lev n S base 1).pts.size,
      ∃ c < (lev n S base 2).pts.size,
        levT n S base 0 a * levT n S base 1 b * levT n S base 2 c = g := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  obtain ⟨-, Φ, hΦ, hbij, -⟩ := Q.schreier_transversal_product_bijection hQ
  obtain ⟨y, hy⟩ := hbij.2 ⟨g, hg⟩
  have hg' : g = (List.ofFn fun i => Q.orbitTransversal i (y i)).prod := by
    rw [← hΦ y, hy]
  have hT : ∀ i : Fin Q.baseCount, Q.orbitTransversal i (y i) =
      levT n S base i (lev n S base i).pos[((y i : Fin n) : ℕ)]! := fun i =>
    (hA.orbitPoints_spec hF i.2 (y i).2).2.2
  have hK : ∀ i : Fin Q.baseCount,
      (lev n S base i).pos[((y i : Fin n) : ℕ)]! < (lev n S base i).pts.size := fun i =>
    (hA.orbitPoints_spec hF i.2 (y i).2).1
  have h1' : ∀ i : Fin Q.baseCount, 3 ≤ i.val → Q.orbitTransversal i (y i) = 1 := by
    intro i hi
    have hk := hK i
    rw [h1 i hi i.2] at hk
    rw [hT i, show (lev n S base i).pos[((y i : Fin n) : ℕ)]! = 0 by omega]
    exact hA.levT_zero hF i.2
  rw [prod_ofFn_eq_of_one h3 (fun i => Q.orbitTransversal i (y i)) h1'] at hg'
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, hT] at hg'
  refine ⟨_, hK ⟨0, by omega⟩, _, hK ⟨1, by omega⟩, _, hK ⟨2, by omega⟩, ?_⟩
  rw [hg', mul_assoc]
  rfl

end ChainArrays

end CFSG.Certificates
