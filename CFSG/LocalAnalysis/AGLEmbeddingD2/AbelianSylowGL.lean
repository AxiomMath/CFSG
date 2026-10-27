module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.NumberTheory.Multiplicity
public import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL

public section

namespace CFSG.AGLEmbeddingD2.AbelianSylowGL

open CFSG.AGLEmbeddingD2.CyclicSylowGL

theorem isMulCommutative_of_isPGroup_of_not_dvd_index {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] (S : Subgroup G) [IsMulCommutative S] (hS : ¬ r ∣ S.index) {P : Subgroup G}
    (hP : IsPGroup r P) : IsMulCommutative P := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r S))
  have hQ : ¬ r ∣ (Q.map S.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out Q.not_dvd_index hS
  let R₀ : Sylow r G := (Q.isPGroup'.map S.subtype).toSylow hQ
  have hR₀ : IsMulCommutative (R₀ : Subgroup G) :=
    isMulCommutative_anti (t := S) (Subgroup.map_subtype_le _)
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  have hR : IsMulCommutative (R : Subgroup G) :=
    (R₀.equiv R).surjective.isMulCommutative hR₀
  exact isMulCommutative_anti hPR

theorem dvd_pow_sub_one_iff {q r d : ℕ} (hq : 0 < q) (hd1 : 1 ≤ d) (hd : r ∣ q ^ d - 1)
    (hmin : ∀ j, 1 ≤ j → j < d → ¬ r ∣ q ^ j - 1) (j : ℕ) : r ∣ q ^ j - 1 ↔ d ∣ j := by
  have key : ∀ n : ℕ, r ∣ q ^ n - 1 ↔ (q : ZMod r) ^ n = 1 := fun n => by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
      Nat.cast_one, sub_eq_zero]
  have hord : orderOf (q : ZMod r) = d := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨(key d).1 hd, fun j hj hj0 h => hmin j hj0 hj ((key j).2 h)⟩
  rw [key, ← orderOf_dvd_iff_pow_eq_one, hord]

theorem padicValNat_pow_mul_sub_one {q r d i : ℕ} [hr : Fact r.Prime] (hodd : Odd r) (hq : 1 < q)
    (h0 : ¬ r ∣ q) (hd1 : 1 ≤ d) (hd : r ∣ q ^ d - 1) (hi0 : 0 < i) (hir : i < r) :
    padicValNat r (q ^ (d * i) - 1) = padicValNat r (q ^ d - 1) := by
  have hqd : 1 < q ^ d := Nat.one_lt_pow (by omega) hq
  have h := padicValNat.pow_sub_pow (p := r) hodd (x := q ^ d) (y := 1) hqd (by simpa using hd)
    (fun h => h0 (hr.out.dvd_of_dvd_pow h)) hi0.ne'
  rwa [← pow_mul, one_pow, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hi0 hir),
    add_zero] at h

theorem padicValNat_pow_sub_one_eq {q r d j : ℕ} [hr : Fact r.Prime] (hodd : Odd r) (hq : 1 < q)
    (h0 : ¬ r ∣ q) (hd1 : 1 ≤ d) (hd : r ∣ q ^ d - 1)
    (hmin : ∀ j, 1 ≤ j → j < d → ¬ r ∣ q ^ j - 1) (hj0 : 0 < j) (hj : j < r * d) :
    padicValNat r (q ^ j - 1) = if d ∣ j then padicValNat r (q ^ d - 1) else 0 := by
  split_ifs with h
  · obtain ⟨i, rfl⟩ := h
    have hi0 : 0 < i := Nat.pos_of_ne_zero (right_ne_zero_of_mul hj0.ne')
    have hir : i < r := by
      refine Nat.lt_of_mul_lt_mul_right (a := d) ?_
      rwa [mul_comm i d]
    exact padicValNat_pow_mul_sub_one hodd hq h0 hd1 hd hi0 hir
  · exact padicValNat.eq_zero_of_not_dvd fun h' =>
      h ((dvd_pow_sub_one_iff (by omega) hd1 hd hmin j).1 h')

theorem sum_range_ite_dvd (V d m : ℕ) :
    ∑ j ∈ Finset.range m, (if d ∣ j + 1 then V else 0) = m / d * V := by
  induction m with
  | zero => rw [Finset.sum_range_zero, Nat.zero_div, zero_mul]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_div]
    split_ifs <;> ring

theorem padicValNat_finset_prod {ι : Type*} {r : ℕ} [hr : Fact r.Prime] (s : Finset ι)
    (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat r (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat r (f i) := by
  rw [← Nat.factorization_def _ hr.out, Nat.factorization_prod_apply hf]
  exact Finset.sum_congr rfl fun i _ => Nat.factorization_def _ hr.out

theorem padicValNat_card_GL {k : Type*} [Field k] [Fintype k] {r : ℕ} [hr : Fact r.Prime]
    (hodd : Odd r) {m d : ℕ} (h0 : ¬ r ∣ Fintype.card k) (hd1 : 1 ≤ d)
    (hd : r ∣ Fintype.card k ^ d - 1)
    (hmin : ∀ j, 1 ≤ j → j < d → ¬ r ∣ Fintype.card k ^ j - 1) (hm : m < r * d) :
    padicValNat r (Nat.card (GL (Fin m) k)) = m / d * padicValNat r (Fintype.card k ^ d - 1) := by
  set q := Fintype.card k with hqdef
  have hq : 1 < q := Fintype.one_lt_card
  have hnz : ∀ i ∈ (Finset.univ : Finset (Fin m)), q ^ m - q ^ (i : ℕ) ≠ 0 := fun i _ =>
    (Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq i.2)).ne'
  have hterm : ∀ i : Fin m, padicValNat r (q ^ m - q ^ (i : ℕ)) =
      padicValNat r (q ^ (m - (i : ℕ)) - 1) := fun i => by
    have hi : (i : ℕ) ≤ m := i.2.le
    have hne : q ^ (m - (i : ℕ)) - 1 ≠ 0 :=
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hq)).ne'
    rw [pow_sub_pow_eq hi, padicValNat.mul (by positivity) hne,
      padicValNat.eq_zero_of_not_dvd (fun h => h0 (hr.out.dvd_of_dvd_pow h)), zero_add]
  rw [Matrix.card_GL_field, padicValNat_finset_prod _ _ hnz,
    Finset.sum_congr rfl fun i _ => hterm i,
    Fin.sum_univ_eq_sum_range (fun i => padicValNat r (q ^ (m - i) - 1)) m]
  have hrefl := Finset.sum_range_reflect (fun j => padicValNat r (q ^ (j + 1) - 1)) m
  have h1 : ∑ i ∈ Finset.range m, padicValNat r (q ^ (m - i) - 1) =
      ∑ j ∈ Finset.range m, padicValNat r (q ^ (m - 1 - j + 1) - 1) :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      congr 3
      omega
  rw [h1, hrefl, Finset.sum_congr rfl (fun j hj => padicValNat_pow_sub_one_eq hodd hq h0 hd1 hd
    hmin (j := j + 1) (Nat.succ_pos j) (by have := Finset.mem_range.1 hj; omega)),
    sum_range_ite_dvd]

theorem exists_abelian_subgroup_GL {k : Type*} [Field k] [Fintype k] {d t m : ℕ} (hd : 1 ≤ d)
    (htm : t * d ≤ m) :
    ∃ S : Subgroup (GL (Fin m) k),
      IsMulCommutative S ∧ Nat.card S = (Fintype.card k ^ d - 1) ^ t := by
  obtain ⟨p, hp⟩ := CharP.exists k
  have : NeZero p := ⟨CharP.char_ne_zero_of_finite k p⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have : NeZero d := ⟨by omega⟩
  let L := FiniteField.Extension k p d
  have hfr : Module.finrank k (Fin t → L) = t * d := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, show Module.finrank k L = d from FiniteField.finrank_extension k p d]
  let b : Module.Basis (Fin (t * d)) k (Fin t → L) := Module.finBasisOfFinrankEq k _ hfr
  let ψ : (Fin t → L)ˣ →* GL (Fin (t * d)) k := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => Units.ext
    (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  obtain ⟨ι, hι⟩ := exists_injective_GL_of_le (R := k) htm
  have hιψ : Function.Injective (ι.comp ψ) := hι.comp hψ
  refine ⟨(ι.comp ψ).range, inferInstance, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hιψ).toEquiv,
    Nat.card_congr (MulEquiv.piUnits (M := fun _ : Fin t => L)).toEquiv, Nat.card_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units,
    FiniteField.natCard_extension, Nat.card_eq_fintype_card]

theorem isMulCommutative_of_isPGroup_GL {k : Type*} [Field k] [Fintype k] {r : ℕ}
    [Fact r.Prime] (hodd : Odd r) {m d : ℕ} (h0 : ¬ r ∣ Fintype.card k)
    (hd : r ∣ Fintype.card k ^ d - 1)
    (hmin : ∀ j, 1 ≤ j → j < d → ¬ r ∣ Fintype.card k ^ j - 1) (hm : m < r * d)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup r P) : IsMulCommutative P := by
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  obtain ⟨S, hScomm, hScard⟩ :=
    exists_abelian_subgroup_GL (k := k) hd1 (Nat.div_mul_le_self m d)
  have hval := padicValNat_card_GL hodd h0 hd1 hd hmin hm
  have hindex : ¬ r ∣ S.index := by
    have hine : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [← Subgroup.card_mul_index S, padicValNat.mul Nat.card_pos.ne' hine, hScard,
      padicValNat.pow] at hval
    rw [dvd_iff_padicValNat_ne_zero hine]
    omega
  exact isMulCommutative_of_isPGroup_of_not_dvd_index S hindex hP

theorem isMulCommutative_of_isPGroup_of_injective {X G : Type*} [Group X] [Group G] {r : ℕ}
    (φ : X →* G) (hφ : Function.Injective φ)
    (h : ∀ Q : Subgroup G, IsPGroup r Q → IsMulCommutative Q) {P : Subgroup X}
    (hP : IsPGroup r P) : IsMulCommutative P := by
  have := h _ (hP.map φ)
  refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => hφ ?_
  rw [map_mul, map_mul]
  exact setLike_mul_comm (Subgroup.mem_map_of_mem φ ha) (Subgroup.mem_map_of_mem φ hb)

theorem isMulCommutative_of_isPGroup_of_injective_GL {X : Type*} [Group X] {k : Type*} [Field k]
    [Fintype k] {r : ℕ} [Fact r.Prime] (hodd : Odd r) {m d : ℕ} (h0 : ¬ r ∣ Fintype.card k)
    (hd : r ∣ Fintype.card k ^ d - 1)
    (hmin : ∀ j, 1 ≤ j → j < d → ¬ r ∣ Fintype.card k ^ j - 1) (hm : m < r * d)
    (φ : X →* GL (Fin m) k) (hφ : Function.Injective φ) (P : Subgroup X) (hP : IsPGroup r P) :
    IsMulCommutative P :=
  isMulCommutative_of_isPGroup_of_injective φ hφ
    (isMulCommutative_of_isPGroup_GL hodd h0 hd hmin hm) hP

theorem isMulCommutative_of_isPGroup_five_GL_two_pow_of_odd {k : Type*} [Field k] [Fintype k]
    {f m : ℕ} (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hm : m < 20)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : IsMulCommutative P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine isMulCommutative_of_isPGroup_GL (r := 5) (d := 4) ⟨2, rfl⟩ (hk ▸ not_five_dvd_two_pow f) ?_
    (fun j hj1 hj4 => ?_) (by omega) P hP
  · rw [five_dvd_pow_sub_one_iff hk]
    omega
  · rw [five_dvd_pow_sub_one_iff hk]
    obtain ⟨a, ha⟩ := hf
    interval_cases j <;> omega

theorem isMulCommutative_of_isPGroup_five_GL_two_pow_of_mod_four_eq_two {k : Type*} [Field k]
    [Fintype k] {f m : ℕ} (hf : f % 4 = 2) (hk : Fintype.card k = 2 ^ f) (hm : m < 10)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : IsMulCommutative P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine isMulCommutative_of_isPGroup_GL (r := 5) (d := 2) ⟨2, rfl⟩ (hk ▸ not_five_dvd_two_pow f) ?_
    (fun j hj1 hj2 => ?_) (by omega) P hP
  · rw [five_dvd_pow_sub_one_iff hk]
    omega
  · rw [five_dvd_pow_sub_one_iff hk]
    obtain rfl : j = 1 := by omega
    omega

theorem isMulCommutative_of_isPGroup_five_GL_two_pow_of_four_dvd {k : Type*} [Field k]
    [Fintype k] {f m : ℕ} (hf : 4 ∣ f) (hk : Fintype.card k = 2 ^ f) (hm : m < 5)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : IsMulCommutative P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine isMulCommutative_of_isPGroup_GL (r := 5) (d := 1) ⟨2, rfl⟩ (hk ▸ not_five_dvd_two_pow f) ?_
    (fun j hj1 hj2 => absurd hj2 (by omega)) (by omega) P hP
  rw [five_dvd_pow_sub_one_iff hk]
  omega

theorem isMulCommutative_of_isPGroup_five_GL_two_pow {k : Type*} [Field k] [Fintype k] {f m : ℕ}
    (hk : Fintype.card k = 2 ^ f)
    (hfm : (Odd f ∧ m < 20) ∨ (f % 4 = 2 ∧ m < 10) ∨ (4 ∣ f ∧ m < 5))
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : IsMulCommutative P := by
  rcases hfm with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩
  · exact isMulCommutative_of_isPGroup_five_GL_two_pow_of_odd hf hk hm P hP
  · exact isMulCommutative_of_isPGroup_five_GL_two_pow_of_mod_four_eq_two hf hk hm P hP
  · exact isMulCommutative_of_isPGroup_five_GL_two_pow_of_four_dvd hf hk hm P hP

theorem isMulCommutative_of_isPGroup_five_of_injective_GL_two_pow {X : Type*} [Group X]
    {k : Type*} [Field k] [Fintype k] {f m : ℕ} (hk : Fintype.card k = 2 ^ f)
    (hfm : (Odd f ∧ m < 20) ∨ (f % 4 = 2 ∧ m < 10) ∨ (4 ∣ f ∧ m < 5))
    (φ : X →* GL (Fin m) k) (hφ : Function.Injective φ) (P : Subgroup X) (hP : IsPGroup 5 P) :
    IsMulCommutative P :=
  isMulCommutative_of_isPGroup_of_injective φ hφ
    (isMulCommutative_of_isPGroup_five_GL_two_pow hk hfm) hP

theorem isMulCommutative_of_isPGroup_pi {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {r : ℕ}
    (h : ∀ (i : ι) (Q : Subgroup (G i)), IsPGroup r Q → IsMulCommutative Q)
    {P : Subgroup (∀ i, G i)} (hP : IsPGroup r P) : IsMulCommutative P := by
  refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => funext fun i => ?_
  have := h i _ (hP.map (Pi.evalMonoidHom G i))
  exact setLike_mul_comm (Subgroup.mem_map_of_mem (Pi.evalMonoidHom G i) ha)
    (Subgroup.mem_map_of_mem (Pi.evalMonoidHom G i) hb)

end CFSG.AGLEmbeddingD2.AbelianSylowGL
