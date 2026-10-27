module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517P
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma sec5b517_commute_of_mul_commute {a b u : G} (hab : Commute (a * b) u)
    (hb : Commute b u) : Commute a u := by
  rw [commute_iff_eq] at hab hb ⊢
  refine mul_right_cancel (b := b) ?_
  calc
    a * u * b = a * (u * b) := by rw [mul_assoc]
    _ = a * (b * u) := by rw [hb]
    _ = a * b * u := by rw [← mul_assoc]
    _ = u * (a * b) := hab
    _ = u * a * b := by rw [← mul_assoc]

private lemma sec5b517_comm_factor_of_comm_prod {a : Fin 4 → G} {u : G}
    (hpair : ∀ j l : Fin 4, j ≠ l → Commute (a j) (a l))
    (h : Commute (Sec5B517Prod a) u) {i : Fin 4}
    (hu : ∀ j : Fin 4, j ≠ i → Commute (a j) u) : Commute (a i) u := by
  fin_cases i
  · have hP : Commute (a 1 * a 2 * a 3) u :=
      ((hu 1 (by decide)).mul_left (hu 2 (by decide))).mul_left (hu 3 (by decide))
    have h0 : Commute (a 0 * (a 1 * a 2 * a 3)) u := by
      have hEq : a 0 * (a 1 * a 2 * a 3) = Sec5B517Prod a := by
        simp only [Sec5B517Prod, mul_assoc]
      rw [hEq]; exact h
    exact sec5b517_commute_of_mul_commute h0 hP
  · have hP : Commute (a 0 * a 2 * a 3) u :=
      ((hu 0 (by decide)).mul_left (hu 2 (by decide))).mul_left (hu 3 (by decide))
    have h1 : Commute (a 1 * (a 0 * a 2 * a 3)) u := by
      have h01 : a 0 * a 1 = a 1 * a 0 := (hpair 0 1 (by decide)).eq
      have hEq : a 1 * (a 0 * a 2 * a 3) = Sec5B517Prod a := by
        calc
          a 1 * (a 0 * a 2 * a 3) = a 1 * a 0 * a 2 * a 3 := by group
          _ = a 0 * a 1 * a 2 * a 3 := by rw [← h01]
          _ = Sec5B517Prod a := by rfl
      rw [hEq]; exact h
    exact sec5b517_commute_of_mul_commute h1 hP
  · have hP : Commute (a 0 * a 1 * a 3) u :=
      ((hu 0 (by decide)).mul_left (hu 1 (by decide))).mul_left (hu 3 (by decide))
    have h2 : Commute (a 2 * (a 0 * a 1 * a 3)) u := by
      have h02 : a 0 * a 2 = a 2 * a 0 := (hpair 0 2 (by decide)).eq
      have h12 : a 1 * a 2 = a 2 * a 1 := (hpair 1 2 (by decide)).eq
      have hEq : a 2 * (a 0 * a 1 * a 3) = Sec5B517Prod a := by
        calc
          a 2 * (a 0 * a 1 * a 3) = a 2 * a 0 * a 1 * a 3 := by group
          _ = a 0 * a 2 * a 1 * a 3 := by rw [← h02]
          _ = a 0 * (a 2 * a 1) * a 3 := by group
          _ = a 0 * (a 1 * a 2) * a 3 := by rw [← h12]
          _ = a 0 * a 1 * a 2 * a 3 := by group
          _ = Sec5B517Prod a := by rfl
      rw [hEq]; exact h
    exact sec5b517_commute_of_mul_commute h2 hP
  · have hP : Commute (a 0 * a 1 * a 2) u :=
      ((hu 0 (by decide)).mul_left (hu 1 (by decide))).mul_left (hu 2 (by decide))
    have h3 : Commute (a 3 * (a 0 * a 1 * a 2)) u := by
      have h03 : a 0 * a 3 = a 3 * a 0 := (hpair 0 3 (by decide)).eq
      have h13 : a 1 * a 3 = a 3 * a 1 := (hpair 1 3 (by decide)).eq
      have h23 : a 2 * a 3 = a 3 * a 2 := (hpair 2 3 (by decide)).eq
      have hEq : a 3 * (a 0 * a 1 * a 2) = Sec5B517Prod a := by
        calc
          a 3 * (a 0 * a 1 * a 2) = a 3 * a 0 * a 1 * a 2 := by group
          _ = a 0 * a 3 * a 1 * a 2 := by rw [← h03]
          _ = a 0 * (a 3 * a 1) * a 2 := by group
          _ = a 0 * (a 1 * a 3) * a 2 := by rw [← h13]
          _ = a 0 * a 1 * a 3 * a 2 := by group
          _ = a 0 * a 1 * (a 3 * a 2) := by group
          _ = a 0 * a 1 * (a 2 * a 3) := by rw [← h23]
          _ = a 0 * a 1 * a 2 * a 3 := by group
          _ = Sec5B517Prod a := by rfl
      rw [hEq]; exact h
    exact sec5b517_commute_of_mul_commute h3 hP

private theorem sec5b517_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem sec5b517_isPGroup_twoCoreIn (X : Subgroup G) : IsPGroup 2 (twoCoreIn X) := by
  unfold twoCoreIn CFSG.inSubgroup
  exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype

private theorem sec5b517_le_twoCoreIn_of_normal {X P : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hn : (P.subgroupOf X).Normal) : P ≤ twoCoreIn X := by
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
  have hle : P.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hn, hP2'⟩
  calc
    P = (P.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hPX).symm
    _ ≤ (CFSG.pCore 2 ↥X).map X.subtype := Subgroup.map_mono hle
    _ = twoCoreIn X := rfl

@[expose] def Sec5B517Q8 (hq : Sec5B517Quad K z) : Subgroup G where
  carrier := {x | ∃ k : Fin 4 → G, (∀ i, k i ∈ K i ∧ k i ^ 4 = 1) ∧ x = Sec5B517Prod k}
  one_mem' := ⟨fun _ => 1, fun i => ⟨(K i).one_mem, by simp⟩, sec5b517_prod_one.symm⟩
  mul_mem' := by
    rintro x y ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
    refine ⟨fun i => k i * l i, fun i => ⟨(K i).mul_mem (hk i).1 (hl i).1,
      hq.pow4_mul (hk i).1 (hl i).1 (hk i).2 (hl i).2⟩, ?_⟩
    exact sec5b517_prod_mul hq (fun i => (hk i).1) (fun i => (hl i).1)
  inv_mem' := by
    rintro x ⟨k, hk, rfl⟩
    refine ⟨fun i => (k i)⁻¹, fun i => ⟨(K i).inv_mem (hk i).1, ?_⟩, ?_⟩
    · rw [inv_pow, (hk i).2, inv_one]
    · exact sec5b517_prod_inv hq (fun i => (hk i).1)

theorem Sec5B517Q8.mem_iff (hq : Sec5B517Quad K z) {x : G} :
    x ∈ Sec5B517Q8 hq ↔ ∃ k : Fin 4 → G, (∀ i, k i ∈ K i ∧ k i ^ 4 = 1) ∧ x = Sec5B517Prod k :=
  Iff.rfl

theorem Sec5B517Q8.pow_four (hq : Sec5B517Quad K z) {x : G} (hx : x ∈ Sec5B517Q8 hq) :
    x ^ 4 = 1 := by
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hx
  have hfam : (fun i => k i ^ 4) = fun _ : Fin 4 => (1 : G) := by
    funext i; exact (hk i).2
  rw [sec5b517_prod_pow hq (fun i => (hk i).1) 4, hfam, sec5b517_prod_one]

theorem Sec5B517Q8.le_all (hq : Sec5B517Quad K z) : Sec5B517Q8 hq ≤ Sec5B517All K := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hx
  exact sec5b517_prod_mem (fun i => (hk i).1)

theorem Sec5B517Q8.mem_of_mem (hq : Sec5B517Quad K z) {i : Fin 4} {u : G} (hu : u ∈ K i)
    (h4 : u ^ 4 = 1) : u ∈ Sec5B517Q8 hq := by
  refine ⟨fun j => if j = i then u else 1, ?_, (sec5b517_prod_single i u).symm⟩
  intro j
  by_cases hj : j = i
  · subst hj; simp [hu, h4]
  · simp [hj, (K j).one_mem]

theorem Sec5B517Q8.conj_mem (hq : Sec5B517Quad K z) {y x : G} (hy : y ∈ Sec5B517All K)
    (hx : x ∈ Sec5B517Q8 hq) : y * x * y⁻¹ ∈ Sec5B517Q8 hq := by
  obtain ⟨u, hu, rfl⟩ := sec5b517_decomp hq hy
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hx
  have hui : ∀ i, (u i)⁻¹ ∈ K i := fun i => (K i).inv_mem (hu i)
  refine ⟨fun i => u i * k i * (u i)⁻¹, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact (K i).mul_mem ((K i).mul_mem (hu i) (hk i).1) ((K i).inv_mem (hu i))
  · rw [conj_pow, (hk i).2]; simp
  · have h2 : (Sec5B517Prod (fun i => (u i)⁻¹))⁻¹ = Sec5B517Prod u := by
      rw [← sec5b517_prod_inv hq hu, inv_inv]
    have hgoal : Sec5B517Prod u * Sec5B517Prod k * (Sec5B517Prod u)⁻¹ =
        (Sec5B517Prod (fun i => (u i)⁻¹))⁻¹ * Sec5B517Prod k *
          (Sec5B517Prod (fun i => (u i)⁻¹)) := by
      rw [h2, sec5b517_prod_inv hq hu]
    rw [hgoal, sec5b517_prod_conj hq hui (fun i => (hk i).1)]
    simp

theorem Sec5B517Q8.mem_of_pow (hq : Sec5B517Quad K z) {x : G} (hx : x ∈ Sec5B517All K)
    {m : ℕ} (h : x ^ (2 ^ m) = 1) : x ∈ Sec5B517Q8 hq := by
  obtain ⟨k, hk, rfl⟩ := sec5b517_decomp hq hx
  refine ⟨k, ?_, rfl⟩
  have hprod : Sec5B517Prod (fun i => k i ^ (2 ^ m)) = 1 := by
    rw [← sec5b517_prod_pow hq hk (2 ^ m)]
    exact h
  have hcentral : ∀ i : Fin 4, ∀ v ∈ K i, (k i) ^ (2 ^ m) * v = v * (k i) ^ (2 ^ m) := by
    intro i v hv
    have hpair : ∀ j l : Fin 4, j ≠ l → Commute (k j ^ (2 ^ m)) (k l ^ (2 ^ m)) := by
      intro j l hjl
      exact ((commute_iff_eq _ _).mpr (hq.comm j l hjl (k j) (hk j) (k l) (hk l))).pow_pow _ _
    have hu : ∀ j : Fin 4, j ≠ i → Commute (k j ^ (2 ^ m)) v := by
      intro j hj
      exact ((commute_iff_eq _ _).mpr (hq.comm j i hj (k j) (hk j) v hv)).pow_left _
    have hik : Commute (k i ^ (2 ^ m)) v :=
      sec5b517_comm_factor_of_comm_prod hpair (by rw [hprod]; exact Commute.one_left v) hu
    exact hik.eq
  intro i
  refine ⟨hk i, ?_⟩
  have haK : (k i) ^ (2 ^ m) ∈ K i := (K i).pow_mem (hk i) _
  rcases hq.eq_of_central haK (hcentral i) with h1 | hz
  · exact hq.pow4_of_pow (hk i) h1
  · refine hq.pow4_of_pow (hk i) (m := m + 1) ?_
    rw [pow_succ, pow_mul, hz, pow_two, hq.z_sq]

private theorem sec5b517Q8_isPGroup (hq : Sec5B517Quad K z) : IsPGroup 2 (Sec5B517Q8 hq) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  simpa using Sec5B517Q8.pow_four hq g.2

private theorem sec5b517Q8_normal (hq : Sec5B517Quad K z) :
    ((Sec5B517Q8 hq).subgroupOf (Sec5B517All K)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Sec5B517Q8.le_all hq)]
  intro h k hh hk
  exact Sec5B517Q8.conj_mem hq hk hh

theorem Sec5B517Quad.core_eq (hq : Sec5B517Quad K z) :
    twoCoreIn (Sec5B517All K) = Sec5B517Q8 hq := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxX : x ∈ Sec5B517All K := sec5b517_twoCoreIn_le_self _ hx
    obtain ⟨m, hm⟩ := (sec5b517_isPGroup_twoCoreIn (Sec5B517All K)).exists_pow_pow_eq_one ⟨x, hx⟩
    have hxm : x ^ (2 ^ m) = 1 := by
      simpa using congrArg (fun y : ↥(twoCoreIn (Sec5B517All K)) => (y : G)) hm
    exact Sec5B517Q8.mem_of_pow hq hxX hxm
  · intro x hx
    exact sec5b517_le_twoCoreIn_of_normal (Sec5B517Q8.le_all hq) (sec5b517Q8_isPGroup hq)
      (sec5b517Q8_normal hq) hx

theorem Sec5B517Quad.mem_core_iff (hq : Sec5B517Quad K z) {x : G} :
    x ∈ twoCoreIn (Sec5B517All K) ↔ x ∈ Sec5B517All K ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  constructor
  · intro hx
    refine ⟨sec5b517_twoCoreIn_le_self _ hx, ?_⟩
    obtain ⟨m, hm⟩ := (sec5b517_isPGroup_twoCoreIn (Sec5B517All K)).exists_pow_pow_eq_one ⟨x, hx⟩
    exact ⟨m, by
      simpa using congrArg (fun y : ↥(twoCoreIn (Sec5B517All K)) => (y : G)) hm⟩
  · rintro ⟨hxX, m, hm⟩
    rw [core_eq hq]
    exact Sec5B517Q8.mem_of_pow hq hxX hm

theorem Sec5B517Quad.mem_normalizer_of_conj (hq : Sec5B517Quad K z) {g : G}
    (hg : CFSG.conjugate (Sec5B517All K) g = Sec5B517All K) :
    g ∈ normalizer (twoCoreIn (Sec5B517All K) : Set G) := by
  have hgN : g ∈ normalizer (Sec5B517All K : Set G) := by
    rw [← Subgroup.inv_mem_iff, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxX, m, hm⟩ := (Sec5B517Quad.mem_core_iff hq).mp hx
    refine (Sec5B517Quad.mem_core_iff hq).mpr ⟨?_, m, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hxX
    · rw [conj_pow, hm]; simp
  · intro hx
    obtain ⟨hgxX, m, hm⟩ := (Sec5B517Quad.mem_core_iff hq).mp hx
    refine (Sec5B517Quad.mem_core_iff hq).mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mpr hgxX, m, ?_⟩
    have hgx : g * x ^ (2 ^ m) * g⁻¹ = 1 := by
      rw [← conj_pow]; exact hm
    calc
      x ^ (2 ^ m) = g⁻¹ * (g * x ^ (2 ^ m) * g⁻¹) * g := by group
      _ = 1 := by rw [hgx]; simp

theorem Sec5B517Quad.z_mem_core (hq : Sec5B517Quad K z) : z ∈ twoCoreIn (Sec5B517All K) := by
  rw [core_eq hq]
  refine Sec5B517Q8.mem_of_mem hq (hq.z_mem 0) ?_
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hq.z_sq
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hz2, one_pow]

theorem Sec5B517Quad.z_comm_all (hq : Sec5B517Quad K z) {x : G} (hx : x ∈ Sec5B517All K) :
    z * x = x * z := by
  obtain ⟨k, hk, rfl⟩ := sec5b517_decomp hq hx
  exact (sec5b517_commute_prod (fun i => hq.z_comm (hk i))).eq

theorem Sec5B517Quad.central_core (hq : Sec5B517Quad K z) {w : G}
    (hw : w ∈ twoCoreIn (Sec5B517All K))
    (h : ∀ x ∈ twoCoreIn (Sec5B517All K), w * x = x * w) : w = 1 ∨ w = z := by
  have hwq : w ∈ Sec5B517Q8 hq := by rwa [core_eq hq] at hw
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hwq
  have hki : ∀ i, k i = 1 ∨ k i = z := by
    intro i
    refine hq.eq_of_central_q8 (hk i).1 (hk i).2 ?_
    intro v hv hv4
    have hvcore : v ∈ twoCoreIn (Sec5B517All K) := by
      rw [core_eq hq]
      exact Sec5B517Q8.mem_of_mem hq hv hv4
    have hwv : Commute (Sec5B517Prod k) v := (commute_iff_eq _ _).mpr (h v hvcore)
    have hpair : ∀ j l : Fin 4, j ≠ l → Commute (k j) (k l) := by
      intro j l hjl
      exact (commute_iff_eq _ _).mpr (hq.comm j l hjl (k j) (hk j).1 (k l) (hk l).1)
    have hu : ∀ j : Fin 4, j ≠ i → Commute (k j) v := by
      intro j hj
      exact (commute_iff_eq _ _).mpr (hq.comm j i hj (k j) (hk j).1 v hv)
    exact (sec5b517_comm_factor_of_comm_prod hpair hwv hu).eq
  rcases hki 0 with h0 | h0 <;> rcases hki 1 with h1 | h1 <;>
    rcases hki 2 with h2 | h2 <;> rcases hki 3 with h3 | h3 <;>
    simp [Sec5B517Prod, h0, h1, h2, h3, hq.z_sq]

end CFSG.OddStandard.SmallF3.Omega
