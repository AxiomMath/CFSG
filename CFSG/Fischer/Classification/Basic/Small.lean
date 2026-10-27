module

public import CFSG.Fischer.Uniq.Graph
public import CFSG.Fischer.Classification.Basic.Heisenberg

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

section Line

theorem Pair.line_ne (hP : Pair X E) {d e : X} (hd : d ∈ E) (he : e ∈ E)
    (hde : d * e ≠ e * d) : d ≠ e ∧ d * e * d ≠ d ∧ d * e * d ≠ e ∧ d * e * d ∈ E :=
  ⟨fun h => hde (by rw [h]), Pair.mul_mul_ne_left hP hd hde, Pair.mul_mul_ne_right hP hd hde,
    Pair.mul_mul_mem hP hd he⟩

theorem commute_mul_mul_of_commute {d e z : X} (hd : z * d = d * z) (he : z * e = e * z) :
    z * (d * e * d) = d * e * d * z := by
  calc z * (d * e * d) = z * d * e * d := by simp only [mul_assoc]
    _ = d * (z * e) * d := by rw [hd]; simp only [mul_assoc]
    _ = d * e * (z * d) := by rw [he]; simp only [mul_assoc]
    _ = d * e * d * z := by rw [hd]; simp only [mul_assoc]

end Line

section Path

theorem Pair.commute_conj_of_path (hP : Pair X E) {x y z : X} (hx : x ∈ E) (hy : y ∈ E)
    (hz : z ∈ E) (hxz : x * z = z * x) (hxy : x * y ≠ y * x) (hyz : y * z ≠ z * y) :
    y * (x * z * y * (x * z)) = x * z * y * (x * z) * y := by
  have h1 : x * y * x = y * x * y := Pair.mul_mul_eq hP hx hy hxy
  have h2 : y * z * y = z * y * z := Pair.mul_mul_eq hP hy hz hyz
  have hb : x * z * y * (x * z) = x * (y * z * y) * x := by
    rw [h2]
    calc x * z * y * (x * z) = x * z * y * (z * x) := by rw [hxz]
      _ = x * (z * y * z) * x := by simp only [mul_assoc]
  rw [hb]
  calc y * (x * (y * z * y) * x) = y * x * y * z * y * x := by simp only [mul_assoc]
    _ = x * y * x * z * y * x := by rw [← h1]
    _ = x * y * (x * z) * y * x := by simp only [mul_assoc]
    _ = x * y * (z * x) * y * x := by rw [hxz]
    _ = x * y * z * (x * y * x) := by simp only [mul_assoc]
    _ = x * y * z * (y * x * y) := by rw [h1]
    _ = x * (y * z * y) * x * y := by simp only [mul_assoc]

end Path

section Affine

theorem Pair.conj_mul_eq_inv (hP : Pair X E) {d f : X} (hd : d ∈ E) (hf : f ∈ E) :
    d * (d * f) * d = (d * f)⁻¹ := by
  rw [mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP hf, ← mul_assoc, Pair.mul_self hP hd,
    one_mul]

theorem Pair.conj_mul_pow_eq_inv (hP : Pair X E) {d f : X} (hd : d ∈ E) (hf : f ∈ E) (n : ℕ) :
    d * (d * f) ^ n * d = ((d * f) ^ n)⁻¹ := by
  have h := conj_pow (a := d) (b := d * f) (i := n)
  rw [Pair.inv_eq hP hd] at h
  rw [← h, Pair.conj_mul_eq_inv hP hd hf, inv_pow]

theorem conj_commutatorElement (g a b : X) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

variable (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
  (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
  (hzl : z * (d * e * d) ≠ d * e * d * z)

include hP hd he hz hde hdz hez hzl in
theorem Pair.cubeRel_of_affine : CubeRel (d * e) (d * z) where
  cube_left := by rw [← Pair.orderOf_mul_eq_three hP hd he hde, pow_orderOf_eq_one]
  cube_right := by rw [← Pair.orderOf_mul_eq_three hP hd hz hdz, pow_orderOf_eq_one]
  cube_mul := by
    rw [show d * e * (d * z) = d * e * d * z by simp only [mul_assoc],
      ← Pair.orderOf_mul_eq_three hP (Pair.mul_mul_mem hP hd he) hz fun h => hzl h.symm,
      pow_orderOf_eq_one]
  cube_mul_inv := by
    rw [show d * e * (d * z)⁻¹ = d * (e * z) * d⁻¹ by
        rw [mul_inv_rev, Pair.inv_eq hP hz]; simp only [mul_assoc],
      conj_pow, ← Pair.orderOf_mul_eq_three hP he hz hez, pow_orderOf_eq_one, mul_one,
      mul_inv_cancel]

include hP hd he hz hde hdz hez hzl in
theorem Pair.commute_commutator_of_affine : Commute d ⁅d * e, d * z⁆ := by
  have h := conj_commutatorElement d (d * e) (d * z)
  rw [Pair.inv_eq hP hd, Pair.conj_mul_eq_inv hP hd he, Pair.conj_mul_eq_inv hP hd hz,
    (Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl).commutator_inv_inv] at h
  show d * _ = _ * d
  calc d * ⁅d * e, d * z⁆ = d * ⁅d * e, d * z⁆ * d * d := by
        rw [mul_assoc _ d d, Pair.mul_self hP hd, mul_one]
    _ = ⁅d * e, d * z⁆ * d := by rw [h]

include hP hd he hz hde hdz hez hzl in
theorem Pair.mul_eq_one_of_commute_of_affine {i j : ℕ}
    (h : Commute d ((d * e) ^ i * (d * z) ^ j)) : (d * e) ^ i * (d * z) ^ j = 1 := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  refine mul_eq_one_of_inv_mul_inv_eq (by rw [← pow_mul, mul_comm, pow_mul, hR.cube_left,
    one_pow]) (by rw [← pow_mul, mul_comm, pow_mul, hR.cube_right, one_pow]) ?_
  rw [← Pair.conj_mul_pow_eq_inv hP hd he, ← Pair.conj_mul_pow_eq_inv hP hd hz]
  calc d * (d * e) ^ i * d * (d * (d * z) ^ j * d)
      = d * ((d * e) ^ i * (d * z) ^ j) * d := by
        simp only [mul_assoc, ← mul_assoc d d, Pair.mul_self hP hd, one_mul]
    _ = (d * e) ^ i * (d * z) ^ j := by
        rw [h.eq, mul_assoc, Pair.mul_self hP hd, mul_one]

include hP hd he hz hde hdz hez hzl in
theorem Pair.mod_three_eq_zero_of_affine {i j : ℕ} (h : (d * e) ^ i * (d * z) ^ j = 1) :
    i % 3 = 0 ∧ j % 3 = 0 := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  rw [pow_eq_pow_mod i hR.cube_left, pow_eq_pow_mod j hR.cube_right] at h
  have hx1 : d * e ≠ 1 := fun h' => (Pair.line_ne hP hd he hde).1
    ((Pair.inv_eq hP hd).symm.trans (inv_eq_of_mul_eq_one_right h'))
  have hy1 : d * z ≠ 1 := fun h' => (Pair.line_ne hP hd hz hdz).1
    ((Pair.inv_eq hP hd).symm.trans (inv_eq_of_mul_eq_one_right h'))
  have hxy : d * e ≠ d * z := fun h' => (Pair.line_ne hP he hz hez).1 (mul_left_cancel h')
  have hxy1 : d * e * (d * z) ≠ 1 := by
    intro h'
    apply hzl
    have h'' : (d * e * d)⁻¹ = z :=
      inv_eq_of_mul_eq_one_right (by rw [← h']; simp only [mul_assoc])
    rw [Pair.inv_eq hP (Pair.mul_mul_mem hP hd he)] at h''
    rw [← h'']
  have hx2 := sq_eq_inv_of_pow_three hR.cube_left
  have hy2 := sq_eq_inv_of_pow_three hR.cube_right
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = a at h hi ⊢
  generalize j % 3 = b at h hj ⊢
  interval_cases a <;> interval_cases b <;>
    simp only [pow_zero, pow_one, hx2, hy2, one_mul, mul_one, inv_eq_one] at h ⊢
  all_goals first
    | trivial
    | exact absurd h hx1
    | exact absurd h hy1
    | exact absurd h hxy1
    | exact absurd (mul_inv_eq_one.1 h) hxy
    | exact absurd (inv_mul_eq_one.1 h) hxy
    | exact absurd (mul_eq_one_comm.1 (inv_eq_one.1 (by rw [mul_inv_rev]; exact h))) hxy1

include hP hd he hz hde hdz hez hzl in
theorem Pair.exists_eq_commutator_pow_of_affine {w : X}
    (hw : w ∈ Subgroup.closure ({d * e, d * z} : Set X)) (hdw : Commute d w) :
    ∃ k : ℕ, w = ⁅d * e, d * z⁆ ^ k := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  obtain ⟨i, j, k, -, -, -, rfl⟩ := hR.exists_eq_of_mem_closure hw
  have hdc := (Pair.commute_commutator_of_affine hP hd he hz hde hdz hez hzl).pow_right k
  have h1 : (d * e) ^ i * (d * z) ^ j = 1 := by
    refine Pair.mul_eq_one_of_commute_of_affine hP hd he hz hde hdz hez hzl ?_
    have h2 := hdw.mul_right hdc.inv_right
    rwa [mul_inv_cancel_right] at h2
  exact ⟨k, by rw [h1, one_mul]⟩

include hP hd he hz hde hdz hez hzl in
theorem Pair.mod_eq_of_affine {a b m a' b' m' : ℕ}
    (h : (d * e) ^ a * (d * z) ^ b * ⁅d * e, d * z⁆ ^ m =
      (d * e) ^ a' * (d * z) ^ b' * ⁅d * e, d * z⁆ ^ m') :
    (2 * a' + a) % 3 = 0 ∧ (b + 2 * b') % 3 = 0 := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  have hdc := Pair.commute_commutator_of_affine hP hd he hz hde hdz hez hzl
  have hxa : (d * e) ^ (2 * a' + a) = ((d * e) ^ a')⁻¹ * (d * e) ^ a := by
    rw [pow_add, pow_mul, sq_eq_inv_of_pow_three hR.cube_left, inv_pow]
  have hyb : (d * z) ^ (b + 2 * b') = (d * z) ^ b * ((d * z) ^ b')⁻¹ := by
    rw [pow_add, pow_mul, sq_eq_inv_of_pow_three hR.cube_right, inv_pow]
  have hcy : Commute (⁅d * e, d * z⁆ ^ m' * (⁅d * e, d * z⁆ ^ m)⁻¹) ((d * z) ^ b') :=
    ((hR.commute_commutator_right.pow_left m').mul_left
      (hR.commute_commutator_right.pow_left m).inv_left).pow_right b'
  have key : (d * e) ^ (2 * a' + a) * (d * z) ^ (b + 2 * b') =
      ⁅d * e, d * z⁆ ^ m' * (⁅d * e, d * z⁆ ^ m)⁻¹ := by
    rw [hxa, hyb]
    calc ((d * e) ^ a')⁻¹ * (d * e) ^ a * ((d * z) ^ b * ((d * z) ^ b')⁻¹)
        = ((d * e) ^ a')⁻¹ * ((d * e) ^ a * (d * z) ^ b * ⁅d * e, d * z⁆ ^ m) *
          (⁅d * e, d * z⁆ ^ m)⁻¹ * ((d * z) ^ b')⁻¹ := by group
      _ = ((d * e) ^ a')⁻¹ * ((d * e) ^ a' * (d * z) ^ b' * ⁅d * e, d * z⁆ ^ m') *
          (⁅d * e, d * z⁆ ^ m)⁻¹ * ((d * z) ^ b')⁻¹ := by rw [h]
      _ = (d * z) ^ b' * (⁅d * e, d * z⁆ ^ m' * (⁅d * e, d * z⁆ ^ m)⁻¹) *
          ((d * z) ^ b')⁻¹ := by group
      _ = ⁅d * e, d * z⁆ ^ m' * (⁅d * e, d * z⁆ ^ m)⁻¹ := by
        rw [← hcy.eq, mul_inv_cancel_right]
  have hcomm : Commute d ((d * e) ^ (2 * a' + a) * (d * z) ^ (b + 2 * b')) := by
    rw [key]
    exact (hdc.pow_right m').mul_right (hdc.pow_right m).inv_right
  exact Pair.mod_three_eq_zero_of_affine hP hd he hz hde hdz hez hzl
    (Pair.mul_eq_one_of_commute_of_affine hP hd he hz hde hdz hez hzl hcomm)

include hP hd he hz in
theorem Pair.exists_eq_or_eq_mul_of_mem_closure {g : X}
    (hg : g ∈ Subgroup.closure ({d, e, z} : Set X)) :
    ∃ n ∈ Subgroup.closure ({d * e, d * z} : Set X), g = n ∨ g = d * n := by
  set N := Subgroup.closure ({d * e, d * z} : Set X)
  have hxN : d * e ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyN : d * z ∈ N := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdE : ∀ s ∈ ({d, e, z} : Set X), s ∈ E := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs | hs <;> rw [hs] <;> assumption
  have key : ∀ s ∈ ({d, e, z} : Set X), ∃ w ∈ N, s = d * w ∧ d * w * d = w⁻¹ := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs | hs <;> rw [hs]
    · exact ⟨1, N.one_mem, (mul_one _).symm, by rw [mul_one, Pair.mul_self hP hd, inv_one]⟩
    · exact ⟨d * e, hxN, by rw [← mul_assoc, Pair.mul_self hP hd, one_mul],
        Pair.conj_mul_eq_inv hP hd he⟩
    · exact ⟨d * z, hyN, by rw [← mul_assoc, Pair.mul_self hP hd, one_mul],
        Pair.conj_mul_eq_inv hP hd hz⟩
  let Q : X → Prop := fun g => ∃ n ∈ N, g = n ∨ g = d * n
  have hstep : ∀ s ∈ ({d, e, z} : Set X), ∀ g, Q g → Q (s * g) := by
    rintro s hs g ⟨n, hn, hg⟩
    obtain ⟨w, hw, hsw, hdw⟩ := key s hs
    rw [hsw]
    rcases hg with hg | hg <;> rw [hg]
    · exact ⟨w * n, N.mul_mem hw hn, Or.inr (mul_assoc _ _ _)⟩
    · refine ⟨w⁻¹ * n, N.mul_mem (N.inv_mem hw) hn, Or.inl ?_⟩
      rw [← hdw]
      simp only [mul_assoc]
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, N.one_mem, Or.inl rfl⟩
  | mul_left s hs g _ ih => exact hstep s hs g ih
  | inv_mul_cancel s hs g _ ih =>
    rw [Pair.inv_eq hP (hdE s hs)]
    exact hstep s hs g ih

include hP hd he hz hde hdz hez hzl in
theorem Pair.conj_injective_of_affine :
    Function.Injective fun p : Fin 3 × Fin 3 =>
      (d * e) ^ (p.1 : ℕ) * (d * z) ^ (p.2 : ℕ) * d *
        ((d * e) ^ (p.1 : ℕ) * (d * z) ^ (p.2 : ℕ))⁻¹ := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hT
  simp only at hT
  set N := Subgroup.closure ({d * e, d * z} : Set X)
  have hxN : d * e ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyN : d * z ∈ N := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set g := (d * e) ^ (a : ℕ) * (d * z) ^ (b : ℕ) with hg
  set g' := (d * e) ^ (a' : ℕ) * (d * z) ^ (b' : ℕ) with hg'
  have hgN : g ∈ N := N.mul_mem (N.pow_mem hxN _) (N.pow_mem hyN _)
  have hg'N : g' ∈ N := N.mul_mem (N.pow_mem hxN _) (N.pow_mem hyN _)
  have hw : Commute d (g'⁻¹ * g) := by
    show d * (g'⁻¹ * g) = g'⁻¹ * g * d
    calc d * (g'⁻¹ * g) = g'⁻¹ * (g' * d * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * d * g⁻¹) * g := by rw [hT]
      _ = g'⁻¹ * g * d := by group
  obtain ⟨k, hk⟩ := Pair.exists_eq_commutator_pow_of_affine hP hd he hz hde hdz hez hzl
    (N.mul_mem (N.inv_mem hg'N) hgN) hw
  have h : (d * e) ^ (a : ℕ) * (d * z) ^ (b : ℕ) * ⁅d * e, d * z⁆ ^ 0 =
      (d * e) ^ (a' : ℕ) * (d * z) ^ (b' : ℕ) * ⁅d * e, d * z⁆ ^ k := by
    rw [pow_zero, mul_one, ← hg, ← hg', ← hk]
    group
  obtain ⟨ha, hb⟩ := Pair.mod_eq_of_affine hP hd he hz hde hdz hez hzl h
  have := a.isLt
  have := a'.isLt
  have := b.isLt
  have := b'.isLt
  rw [Prod.mk.injEq]
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

include hP hd he hz hde hdz hez hzl in
theorem Pair.inter_closure_eq_range_of_affine :
    E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X) =
      Set.range fun p : Fin 3 × Fin 3 =>
        (d * e) ^ (p.1 : ℕ) * (d * z) ^ (p.2 : ℕ) * d *
          ((d * e) ^ (p.1 : ℕ) * (d * z) ^ (p.2 : ℕ))⁻¹ := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  set N := Subgroup.closure ({d * e, d * z} : Set X)
  set G0 := Subgroup.closure ({d, e, z} : Set X)
  have hdG : d ∈ G0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have heG : e ∈ G0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hzG : z ∈ G0 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hNG : N ≤ G0 := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    rcases hs with hs | hs <;> rw [hs]
    · exact G0.mul_mem hdG heG
    · exact G0.mul_mem hdG hzG
  have hxN : d * e ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyN : d * z ∈ N := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  ext f
  constructor
  · rintro ⟨hfE, hfG⟩
    obtain ⟨n, hn, hfn | hfn⟩ := Pair.exists_eq_or_eq_mul_of_mem_closure hP hd he hz hfG
    · exfalso
      have h3 := hR.pow_three_eq_one (hfn ▸ hn)
      rw [pow_three', Pair.mul_self hP hfE, one_mul] at h3
      exact Pair.ne_one hP hfE h3
    · have hn3 := hR.pow_three_eq_one hn
      obtain ⟨i, j, k, hi, hj, -, hijk⟩ := hR.exists_eq_of_mem_closure hn
      refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
      show (d * e) ^ i * (d * z) ^ j * d * ((d * e) ^ i * (d * z) ^ j)⁻¹ = f
      have hdnd : d * n * d = n⁻¹ := by
        have hff : f * f = 1 := Pair.mul_self hP hfE
        rw [hfn] at hff
        exact mul_eq_one_iff_eq_inv.1 (by rw [← hff]; simp only [mul_assoc])
      have hf' : f = n * d * n⁻¹ := by
        have hninv : n⁻¹ = n ^ 2 := (sq_eq_inv_of_pow_three hn3).symm
        calc f = d * n * d * d := by rw [hfn, mul_assoc (d * n) d d, Pair.mul_self hP hd, mul_one]
          _ = n * n * d := by rw [hdnd, hninv, sq]
          _ = n * d * (d * n * d) := by
            simp only [mul_assoc, ← mul_assoc d d, Pair.mul_self hP hd, one_mul]
          _ = n * d * n⁻¹ := by rw [hdnd]
      have hdc := (Pair.commute_commutator_of_affine hP hd he hz hde hdz hez hzl).pow_right k
      have hcd : ⁅d * e, d * z⁆ ^ k * d * (⁅d * e, d * z⁆ ^ k)⁻¹ = d := by
        rw [← hdc.eq, mul_inv_cancel_right]
      rw [hf', hijk]
      calc (d * e) ^ i * (d * z) ^ j * d * ((d * e) ^ i * (d * z) ^ j)⁻¹
          = (d * e) ^ i * (d * z) ^ j * (⁅d * e, d * z⁆ ^ k * d * (⁅d * e, d * z⁆ ^ k)⁻¹) *
            ((d * e) ^ i * (d * z) ^ j)⁻¹ := by rw [hcd]
        _ = (d * e) ^ i * (d * z) ^ j * ⁅d * e, d * z⁆ ^ k * d *
            ((d * e) ^ i * (d * z) ^ j * ⁅d * e, d * z⁆ ^ k)⁻¹ := by group
  · rintro ⟨⟨a, b⟩, rfl⟩
    have hgN : (d * e) ^ (a : ℕ) * (d * z) ^ (b : ℕ) ∈ N :=
      N.mul_mem (N.pow_mem hxN _) (N.pow_mem hyN _)
    exact ⟨Pair.conj_mem hP hd _, G0.mul_mem (G0.mul_mem (hNG hgN) hdG) (G0.inv_mem (hNG hgN))⟩

include hP hd he hz hde hdz hez hzl in
theorem Pair.ncard_inter_closure_affine :
    (E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X)).ncard = 9 := by
  rw [Pair.inter_closure_eq_range_of_affine hP hd he hz hde hdz hez hzl,
    Set.ncard_range_of_injective (Pair.conj_injective_of_affine hP hd he hz hde hdz hez hzl)]
  simp

include hP hd he hz hde hdz hez hzl in
theorem Pair.card_closure_affine :
    Nat.card (Subgroup.closure ({d, e, z} : Set X)) ∈ ({18, 54} : Set ℕ) := by
  have := Pair.finite hP
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  set N := Subgroup.closure ({d * e, d * z} : Set X)
  set G0 := Subgroup.closure ({d, e, z} : Set X)
  have hdG : d ∈ G0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have heG : e ∈ G0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hzG : z ∈ G0 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hNG : N ≤ G0 := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    rcases hs with hs | hs <;> rw [hs]
    · exact G0.mul_mem hdG heG
    · exact G0.mul_mem hdG hzG
  have hxN : d * e ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyN : d * z ∈ N := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hcN : ⁅d * e, d * z⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hxN hyN) (N.inv_mem hxN)) (N.inv_mem hyN)
  have hdN : d ∉ N := by
    intro h
    have h3 := hR.pow_three_eq_one h
    rw [pow_three', Pair.mul_self hP hd, one_mul] at h3
    exact Pair.ne_one hP hd h3
  have hcard : Nat.card G0 = 2 * Nat.card N := by
    let F : N ⊕ N → G0 := Sum.elim (fun n => ⟨n, hNG n.2⟩)
      (fun n => ⟨d * n, G0.mul_mem hdG (hNG n.2)⟩)
    have hF : Function.Bijective F := by
      constructor
      · rintro (n | n) (n' | n') h <;>
          simp only [F, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
        · exact congrArg Sum.inl (Subtype.ext h)
        · exfalso
          apply hdN
          rw [show d = n * (n' : X)⁻¹ by rw [h]; group]
          exact N.mul_mem n.2 (N.inv_mem n'.2)
        · exfalso
          apply hdN
          rw [show d = n' * (n : X)⁻¹ by rw [← h]; group]
          exact N.mul_mem n'.2 (N.inv_mem n.2)
        · exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h))
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn, hgn | hgn⟩ := Pair.exists_eq_or_eq_mul_of_mem_closure hP hd he hz hg
        · exact ⟨Sum.inl ⟨n, hn⟩, Subtype.ext hgn.symm⟩
        · exact ⟨Sum.inr ⟨n, hn⟩, Subtype.ext hgn.symm⟩
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_sum, two_mul]
  have hp : IsPGroup 3 N := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hR.pow_three_eq_one g.2,
      Subgroup.coe_one])⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
  have hle : Nat.card N ≤ 27 := by
    let f : Fin 3 × Fin 3 × Fin 3 → N := fun t =>
      ⟨(d * e) ^ (t.1 : ℕ) * (d * z) ^ (t.2.1 : ℕ) * ⁅d * e, d * z⁆ ^ (t.2.2 : ℕ),
        N.mul_mem (N.mul_mem (N.pow_mem hxN _) (N.pow_mem hyN _)) (N.pow_mem hcN _)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := hR.exists_eq_of_mem_closure hg
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), rfl⟩
    simpa using Nat.card_le_card_of_surjective f hf
  have hge : 9 ≤ Nat.card N := by
    let f : Fin 3 × Fin 3 → N := fun p =>
      ⟨(d * e) ^ (p.1 : ℕ) * (d * z) ^ (p.2 : ℕ), N.mul_mem (N.pow_mem hxN _) (N.pow_mem hyN _)⟩
    have hf : Function.Injective f := by
      intro p q h
      apply Pair.conj_injective_of_affine hP hd he hz hde hdz hez hzl
      simp only [f, Subtype.mk.injEq] at h
      simp only [h]
    simpa using Nat.card_le_card_of_injective f hf
  rw [hm] at hle hge
  have hm4 : m < 4 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hcard, hm]
  interval_cases m <;> simp_all

end Affine

end CFSG.Fischer.Classification
