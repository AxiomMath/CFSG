module

public import CFSG.GH74.BNPair.Chambers
public import CFSG.GH74.BNPair.Dihedral

public noncomputable section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)} {a b : WeylGroup B N} {n : ℕ}

structure Rank2 (B N : Subgroup X) [(cartan B N).Normal] (S : Finset (WeylGroup B N))
    (a b : WeylGroup B N) (n : ℕ) : Prop where
  tits : IsTitsSystem B N S
  gens : (S : Set (WeylGroup B N)) = {a, b}
  dih : IsDihedralGen a b n

@[expose] def gen {W : Type*} (a b : W) (i : Bool) : W :=
  cond i a b

section Vertices

variable (B N a b)

@[expose] def pgen (i : Bool) : Subgroup X :=
  parabolic B N {gen a b i}

@[expose] def vtx (i : Bool) (x : X) : rankTwoVertices B N a b :=
  ⟨((pgen B N a b i : Subgroup X) : Set X) * {x}, by
    cases i
    · exact Or.inr ⟨x, rfl⟩
    · exact Or.inl ⟨x, rfl⟩⟩

variable {B N a b}

theorem mem_vtx {i : Bool} {x z : X} :
    z ∈ ((vtx B N a b i x : rankTwoVertices B N a b) : Set X) ↔ z * x⁻¹ ∈ pgen B N a b i := by
  show z ∈ ((pgen B N a b i : Subgroup X) : Set X) * {x} ↔ _
  rw [Set.mem_mul]
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, y, rfl, rfl⟩
    simpa using hp
  · intro h
    exact ⟨z * x⁻¹, h, x, rfl, by simp⟩

theorem mem_self_vtx {i : Bool} {x : X} :
    x ∈ ((vtx B N a b i x : rankTwoVertices B N a b) : Set X) :=
  mem_vtx.2 (by simp)

theorem vtx_eq_vtx {i : Bool} {x z : X} (h : z * x⁻¹ ∈ pgen B N a b i) :
    vtx B N a b i z = vtx B N a b i x := by
  refine Subtype.ext (Set.ext fun u => ?_)
  show u ∈ ((vtx B N a b i z : rankTwoVertices B N a b) : Set X) ↔
    u ∈ ((vtx B N a b i x : rankTwoVertices B N a b) : Set X)
  rw [mem_vtx, mem_vtx]
  constructor
  · intro hu
    have := (pgen B N a b i).mul_mem hu h
    simpa [mul_assoc] using this
  · intro hu
    have := (pgen B N a b i).mul_mem hu ((pgen B N a b i).inv_mem h)
    simpa [mul_assoc] using this

theorem exists_vtx (v : rankTwoVertices B N a b) : ∃ (i : Bool) (x : X), v = vtx B N a b i x := by
  rcases v.2 with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨true, x, Subtype.ext hx⟩
  · exact ⟨false, x, Subtype.ext hx⟩

end Vertices

namespace Rank2

variable (R : Rank2 B N S a b n)
include R

theorem a_mem : a ∈ S := by
  have : a ∈ (S : Set (WeylGroup B N)) := by rw [R.gens]; exact Set.mem_insert _ _
  exact Finset.mem_coe.1 this

theorem b_mem : b ∈ S := by
  have : b ∈ (S : Set (WeylGroup B N)) := by rw [R.gens]; simp
  exact Finset.mem_coe.1 this

theorem gen_mem (i : Bool) : gen a b i ∈ S := by
  cases i
  · exact R.b_mem
  · exact R.a_mem

theorem dih_gen (i : Bool) : IsDihedralGen (gen a b i) (gen a b (!i)) n := by
  cases i
  · exact R.dih.symm
  · exact R.dih

theorem gen_ne (i : Bool) : gen a b i ≠ gen a b (!i) := (R.dih_gen i).ne

theorem ell_altWord {i : ℕ} (hi : i ≤ n) :
    wordLength (S : Set (WeylGroup B N)) (altWord a b i) = i := by
  rw [R.gens]; exact R.dih.wordLength_altWord hi

theorem ell_altWord' {i : ℕ} (hi : i ≤ n) :
    wordLength (S : Set (WeylGroup B N)) (altWord b a i) = i := by
  rw [R.gens]; exact R.dih.wordLength_altWord' hi

theorem ell_alt (i : Bool) {j : ℕ} (hj : j ≤ n) :
    wordLength (S : Set (WeylGroup B N)) (altWord (gen a b i) (gen a b (!i)) j) = j := by
  cases i
  · exact R.ell_altWord' hj
  · exact R.ell_altWord hj

theorem ell_le (w : WeylGroup B N) : wordLength (S : Set (WeylGroup B N)) w ≤ n := by
  rw [R.gens]
  exact R.dih.wordLength_le w

theorem ell_gen_mul_longest {s : WeylGroup B N} (hs : s = a ∨ s = b) :
    wordLength (S : Set (WeylGroup B N)) (s * altWord a b n) + 1 = n := by
  rw [R.gens]
  exact R.dih.wordLength_gen_mul_longest hs

theorem pgen_inter (i : Bool) {x : X} (h1 : x ∈ pgen B N a b i) (h2 : x ∈ pgen B N a b (!i)) :
    x ∈ B := by
  rcases (mem_parabolic_single_iff R.tits (R.gen_mem i)).1 h1 with hB | hd1
  · exact hB
  rcases (mem_parabolic_single_iff R.tits (R.gen_mem (!i))).1 h2 with hB | hd2
  · exact hB
  exact absurd (R.tits.dc_injective (dc_eq_of_mem hd1 hd2)) (R.gen_ne i)

theorem B_le_pgen (i : Bool) {x : X} (hx : x ∈ B) : x ∈ pgen B N a b i :=
  (mem_parabolic_single_iff R.tits (R.gen_mem i)).2 (Or.inl hx)

theorem vtx_type_eq {i j : Bool} {x y : X} (h : vtx B N a b i x = vtx B N a b j y) : i = j := by
  by_contra hij
  have hj : j = !i := by cases i <;> cases j <;> simp_all
  subst hj
  have hx : x ∈ ((vtx B N a b (!i) y : rankTwoVertices B N a b) : Set X) := by
    rw [← h]; exact mem_self_vtx
  have h1 : vtx B N a b (!i) x = vtx B N a b (!i) y := vtx_eq_vtx (mem_vtx.1 hx)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (gen a b i)
  have hm1 : (m : X) ∈ dc B N (gen a b i) := hm ▸ coe_mem_dc m
  have hp1 : (m : X) ∈ pgen B N a b i :=
    (mem_parabolic_single_iff R.tits (R.gen_mem i)).2 (Or.inr hm1)
  have hp2 : (m : X) ∈ pgen B N a b (!i) := by
    have h3 : (m : X) * x ∈ ((vtx B N a b i x : rankTwoVertices B N a b) : Set X) :=
      mem_vtx.2 (by simpa using hp1)
    rw [h, ← h1] at h3
    simpa using mem_vtx.1 h3
  have hB := R.pgen_inter i hp1 hp2
  have h1' : dc B N (gen a b i) = dc B N 1 := dc_eq_of_mem hm1 (mem_dc_one.2 hB)
  exact R.tits.gen_ne_one (R.gen_mem i) (R.tits.dc_injective h1')

end Rank2

section Types

variable (B N a b)

@[expose] def vtype (v : rankTwoVertices B N a b) : Bool :=
  Classical.choose (exists_vtx v)

variable {B N a b}

end Types

namespace Rank2

variable (R : Rank2 B N S a b n)
include R

theorem vtype_vtx (i : Bool) (x : X) : vtype B N a b (vtx B N a b i x) = i := by
  obtain ⟨x', hx'⟩ := Classical.choose_spec (exists_vtx (vtx B N a b i x))
  exact (R.vtx_type_eq hx').symm

theorem eq_vtx_of_mem {v : rankTwoVertices B N a b} {z : X} (hz : z ∈ (v : Set X)) :
    v = vtx B N a b (vtype B N a b v) z := by
  obtain ⟨i, x, rfl⟩ := exists_vtx v
  rw [R.vtype_vtx]
  exact (vtx_eq_vtx (mem_vtx.1 hz)).symm

theorem vtype_ne_of_adj {u v : rankTwoVertices B N a b} (h : (buildingGraph B N a b).Adj u v) :
    vtype B N a b u ≠ vtype B N a b v := by
  obtain ⟨hne, z, hzu, hzv⟩ := h
  intro heq
  apply hne
  rw [R.eq_vtx_of_mem hzu, R.eq_vtx_of_mem hzv, heq]

theorem vtype_not_of_adj {u v : rankTwoVertices B N a b} (h : (buildingGraph B N a b).Adj u v) :
    vtype B N a b v = !vtype B N a b u := by
  have := R.vtype_ne_of_adj h
  cases hu : vtype B N a b u <;> cases hv : vtype B N a b v <;> simp_all

theorem eq_vtx_not_of_adj {u v : rankTwoVertices B N a b} (h : (buildingGraph B N a b).Adj u v)
    {z : X} (hzv : z ∈ (v : Set X)) : v = vtx B N a b (!vtype B N a b u) z := by
  rw [R.eq_vtx_of_mem hzv, R.vtype_not_of_adj h]

theorem chamber_unique {u v : rankTwoVertices B N a b} (h : (buildingGraph B N a b).Adj u v)
    {z z' : X} (hz : z ∈ (u : Set X)) (hz2 : z ∈ (v : Set X)) (hz' : z' ∈ (u : Set X))
    (hz2' : z' ∈ (v : Set X)) : z' * z⁻¹ ∈ B := by
  have e1 := R.eq_vtx_of_mem hz
  have e2 := R.eq_vtx_not_of_adj h hz2
  have h1 : z' * z⁻¹ ∈ pgen B N a b (vtype B N a b u) := by
    have : z' ∈ ((vtx B N a b (vtype B N a b u) z : rankTwoVertices B N a b) : Set X) := by
      rw [← e1]; exact hz'
    exact mem_vtx.1 this
  have h2 : z' * z⁻¹ ∈ pgen B N a b (!vtype B N a b u) := by
    have : z' ∈ ((vtx B N a b (!vtype B N a b u) z : rankTwoVertices B N a b) : Set X) := by
      rw [← e2]; exact hz2'
    exact mem_vtx.1 this
  exact R.pgen_inter _ h1 h2

theorem vtype_path {f : ℕ → rankTwoVertices B N a b} {k : ℕ}
    (hadj : ∀ i, i < k → (buildingGraph B N a b).Adj (f i) (f (i + 1))) :
    ∀ i, i ≤ k → vtype B N a b (f i) = (if Even i then vtype B N a b (f 0) else !vtype B N a b (f 0)) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := R.vtype_not_of_adj (hadj i (by omega))
    have h2 := ih (by omega)
    rw [h1, h2]
    by_cases he : Even i <;> simp [he, Nat.even_add_one]

theorem gallery (f : ℕ → rankTwoVertices B N a b) (k : ℕ) (hk : k ≤ n)
    (hadj : ∀ i, i < k → (buildingGraph B N a b).Adj (f i) (f (i + 1)))
    (hnb : ∀ i, i + 2 ≤ k → f i ≠ f (i + 2)) :
    ∀ j, j < k → ∀ x y : X, x ∈ (f 0 : Set X) → x ∈ (f 1 : Set X) →
      y ∈ (f j : Set X) → y ∈ (f (j + 1) : Set X) →
        WPos B N (altWord (gen a b (!vtype B N a b (f 0))) (gen a b (vtype B N a b (f 0))) j) x y := by
  intro j
  induction j with
  | zero =>
    intro hj x y hx0 hx1 hy0 hy1
    rw [altWord_zero]
    exact wpos_one_iff.2 (R.chamber_unique (hadj 0 hj) hx0 hx1 hy0 hy1)
  | succ j ih =>
    intro hj x y hx0 hx1 hy0 hy1
    obtain ⟨y', hy'0, hy'1⟩ := (hadj j (by omega)).2
    have hih := ih (by omega) x y' hx0 hx1 hy'0 hy'1
    have hyv : y * y'⁻¹ ∈ pgen B N a b (vtype B N a b (f (j + 1))) := by
      have e := R.eq_vtx_of_mem hy'1
      have : y ∈ ((vtx B N a b (vtype B N a b (f (j + 1))) y' : rankTwoVertices B N a b) :
          Set X) := by
        rw [← e]; exact hy0
      exact mem_vtx.1 this
    have hyB : y * y'⁻¹ ∉ B := by
      intro hB
      have e1 := R.eq_vtx_not_of_adj (hadj (j + 1) hj) hy1
      have e2 := R.eq_vtx_not_of_adj (hadj j (by omega)).symm hy'0
      have e3 : vtx B N a b (!vtype B N a b (f (j + 1))) y =
          vtx B N a b (!vtype B N a b (f (j + 1))) y' :=
        vtx_eq_vtx (R.B_le_pgen _ hB)
      exact hnb j (by omega) (e2.trans (e3.symm.trans e1.symm))
    have hs := R.gen_mem (vtype B N a b (f (j + 1)))
    have hpar := R.vtype_path hadj (j + 1) (by omega)
    have hlet : gen a b (vtype B N a b (f (j + 1))) *
        altWord (gen a b (!vtype B N a b (f 0))) (gen a b (vtype B N a b (f 0))) j =
        altWord (gen a b (!vtype B N a b (f 0))) (gen a b (vtype B N a b (f 0))) (j + 1) := by
      rw [altWord_succ_left, hpar]
      by_cases he : Even j <;> simp [he, Nat.even_add_one]
    have hlen : wordLength (S : Set (WeylGroup B N))
        (altWord (gen a b (!vtype B N a b (f 0))) (gen a b (vtype B N a b (f 0))) j) <
        wordLength (S : Set (WeylGroup B N))
        (gen a b (vtype B N a b (f (j + 1))) *
          altWord (gen a b (!vtype B N a b (f 0))) (gen a b (vtype B N a b (f 0))) j) := by
      rw [hlet]
      have h1 := R.ell_alt (!vtype B N a b (f 0)) (j := j) (by omega)
      have h2 := R.ell_alt (!vtype B N a b (f 0)) (j := j + 1) (by omega)
      rw [Bool.not_not] at h1 h2
      omega
    have h := WPos.step_up R.tits hs hlen hih hyv hyB
    rw [hlet] at h
    exact h

end Rank2

end CFSG.GH74.BNPair
