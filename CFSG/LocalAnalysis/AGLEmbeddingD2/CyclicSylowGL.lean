module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.AGLEmbeddingD2.CyclicSylowGL

theorem isCyclic_of_isPGroup_of_not_dvd_index {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] (S : Subgroup G) [IsCyclic S] (hS : ¬ r ∣ S.index) {P : Subgroup G}
    (hP : IsPGroup r P) : IsCyclic P := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r S))
  have hQ : ¬ r ∣ (Q.map S.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out Q.not_dvd_index hS
  let R₀ : Sylow r G := (Q.isPGroup'.map S.subtype).toSylow hQ
  have hR₀ : IsCyclic (R₀ : Subgroup G) :=
    Subgroup.isCyclic_of_le (H' := S) (Subgroup.map_subtype_le _)
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  have hR : IsCyclic (R : Subgroup G) :=
    isCyclic_of_surjective (R₀.equiv R).toMonoidHom (R₀.equiv R).surjective
  exact Subgroup.isCyclic_of_le hPR

theorem eq_bot_of_isPGroup_of_not_dvd_card {G : Type*} [Group G] {r : ℕ} [Fact r.Prime]
    {P : Subgroup G} (hP : IsPGroup r P) (h : ¬ r ∣ Nat.card G) : P = ⊥ := by
  rcases hP.card_eq_or_dvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq P h1
  · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card P)) h

theorem exists_injective_GL_of_le {R : Type*} [CommRing R] {d m : ℕ} (h : d ≤ m) :
    ∃ ι : GL (Fin d) R →* GL (Fin m) R, Function.Injective ι := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  let β : Matrix (Fin d) (Fin d) R →* Matrix (Fin (d + e)) (Fin (d + e)) R :=
    { toFun := fun A => Matrix.reindexAlgEquiv R R finSumFinEquiv (Matrix.fromBlocks A 0 0 1)
      map_one' := by simp [Matrix.fromBlocks_one]
      map_mul' := fun A B => by
        rw [← map_mul, Matrix.fromBlocks_multiply]
        simp }
  refine ⟨Units.map β, Units.map_injective fun A B hAB => ?_⟩
  have h1 := (Matrix.reindexAlgEquiv R R finSumFinEquiv).injective hAB
  exact (Matrix.fromBlocks_inj.1 h1).1

theorem exists_cyclic_subgroup_GL {k : Type*} [Field k] [Fintype k] {d m : ℕ} (hd : 1 ≤ d)
    (hdm : d ≤ m) :
    ∃ S : Subgroup (GL (Fin m) k), IsCyclic S ∧ Nat.card S = Fintype.card k ^ d - 1 := by
  obtain ⟨p, hp⟩ := CharP.exists k
  have : NeZero p := ⟨CharP.char_ne_zero_of_finite k p⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have : NeZero d := ⟨by omega⟩
  let L := FiniteField.Extension k p d
  have : Fintype L := Fintype.ofFinite L
  let b : Module.Basis (Fin d) k L :=
    Module.finBasisOfFinrankEq k L (FiniteField.finrank_extension k p d)
  let ψ : Lˣ →* GL (Fin d) k := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => Units.ext
    (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  obtain ⟨ι, hι⟩ := exists_injective_GL_of_le (R := k) hdm
  have hιψ : Function.Injective (ι.comp ψ) := hι.comp hψ
  refine ⟨(ι.comp ψ).range, ?_, ?_⟩
  · exact isCyclic_of_surjective (MonoidHom.ofInjective hιψ).toMonoidHom
      (MonoidHom.ofInjective hιψ).surjective
  · rw [← Nat.card_congr (MonoidHom.ofInjective hιψ).toEquiv, Nat.card_units,
      FiniteField.natCard_extension, Nat.card_eq_fintype_card]

theorem pow_sub_pow_eq {q m i : ℕ} (hi : i ≤ m) :
    q ^ m - q ^ i = q ^ i * (q ^ (m - i) - 1) := by
  rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi]

theorem not_dvd_prod_pow_sub_pow {r q m : ℕ} (hr : r.Prime) (h0 : ¬ r ∣ q) (s : Finset (Fin m))
    (hs : ∀ i ∈ s, ¬ r ∣ q ^ (m - (i : ℕ)) - 1) : ¬ r ∣ ∏ i ∈ s, (q ^ m - q ^ (i : ℕ)) := by
  rw [hr.prime.dvd_finsetProd_iff]
  rintro ⟨i, hi, hdvd⟩
  rw [pow_sub_pow_eq i.2.le] at hdvd
  rcases hr.dvd_mul.1 hdvd with h | h
  · exact h0 (hr.dvd_of_dvd_pow h)
  · exact hs i hi h

theorem not_dvd_card_GL {k : Type*} [Field k] [Fintype k] {r : ℕ} [hr : Fact r.Prime] {m : ℕ}
    (h0 : ¬ r ∣ Fintype.card k) (hj : ∀ j, 1 ≤ j → j ≤ m → ¬ r ∣ Fintype.card k ^ j - 1) :
    ¬ r ∣ Nat.card (GL (Fin m) k) := by
  rw [Matrix.card_GL_field]
  exact not_dvd_prod_pow_sub_pow hr.out h0 _ fun i _ => hj _ (by omega) (by omega)

theorem isPGroup_eq_bot_GL {k : Type*} [Field k] [Fintype k] {r : ℕ} [Fact r.Prime] {m : ℕ}
    (h0 : ¬ r ∣ Fintype.card k) (hj : ∀ j, 1 ≤ j → j ≤ m → ¬ r ∣ Fintype.card k ^ j - 1)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup r P) : P = ⊥ :=
  eq_bot_of_isPGroup_of_not_dvd_card hP (not_dvd_card_GL h0 hj)

theorem isCyclic_of_isPGroup_GL {k : Type*} [Field k] [Fintype k] {r : ℕ} [hr : Fact r.Prime]
    {m d : ℕ} (hd : 1 ≤ d) (hdm : d ≤ m) (h0 : ¬ r ∣ Fintype.card k)
    (hj : ∀ j, 1 ≤ j → j ≤ m → j ≠ d → ¬ r ∣ Fintype.card k ^ j - 1)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup r P) : IsCyclic P := by
  obtain ⟨S, hScyc, hScard⟩ := exists_cyclic_subgroup_GL (k := k) hd hdm
  set q := Fintype.card k
  let i₀ : Fin m := ⟨m - d, by omega⟩
  have hGL : Nat.card (GL (Fin m) k) = (q ^ d - 1) *
      (q ^ (i₀ : ℕ) * ∏ i ∈ Finset.univ.erase i₀, (q ^ m - q ^ (i : ℕ))) := by
    rw [Matrix.card_GL_field, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
      pow_sub_pow_eq i₀.2.le, show m - (i₀ : ℕ) = d by simp [i₀]; omega]
    ring
  have hqd : 0 < q ^ d - 1 := by
    have : 1 < q ^ d := Nat.one_lt_pow (by omega) Fintype.one_lt_card
    omega
  have hindex : S.index = q ^ (i₀ : ℕ) * ∏ i ∈ Finset.univ.erase i₀, (q ^ m - q ^ (i : ℕ)) := by
    have h := Subgroup.card_mul_index S
    rw [hScard, hGL] at h
    exact Nat.eq_of_mul_eq_mul_left hqd h
  refine isCyclic_of_isPGroup_of_not_dvd_index S ?_ hP
  rw [hindex]
  refine Nat.Prime.not_dvd_mul hr.out (fun h => h0 (hr.out.dvd_of_dvd_pow h)) ?_
  refine not_dvd_prod_pow_sub_pow hr.out h0 _ fun i hi => ?_
  have hi' : (i : ℕ) ≠ m - d := fun h => (Finset.mem_erase.1 hi).1 (Fin.ext h)
  exact hj _ (by have := i.2; omega) (by omega) (by omega)

theorem isCyclic_of_isPGroup_of_injective {X G : Type*} [Group X] [Group G] {r : ℕ}
    (φ : X →* G) (hφ : Function.Injective φ) (h : ∀ Q : Subgroup G, IsPGroup r Q → IsCyclic Q)
    {P : Subgroup X} (hP : IsPGroup r P) : IsCyclic P :=
  (P.equivMapOfInjective φ hφ).isCyclic.2 (h _ (hP.map φ))

theorem eq_bot_of_isPGroup_of_injective {X G : Type*} [Group X] [Group G] {r : ℕ}
    (φ : X →* G) (hφ : Function.Injective φ) (h : ∀ Q : Subgroup G, IsPGroup r Q → Q = ⊥)
    {P : Subgroup X} (hP : IsPGroup r P) : P = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective P hφ).1 (h _ (hP.map φ))

theorem nonempty_mulEquiv_GL_of_finrank_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] {m : ℕ} (hV : Module.finrank k V = m) :
    Nonempty (LinearMap.GeneralLinearGroup k V ≃* GL (Fin m) k) :=
  ⟨(Matrix.GeneralLinearGroup.toLin' (Module.finBasisOfFinrankEq k V hV)).symm⟩

theorem five_dvd_two_pow_sub_one_iff (n : ℕ) : 5 ∣ 2 ^ n - 1 ↔ 4 ∣ n := by
  have h : 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have key : 2 ^ n % 5 = 1 ↔ n % 4 = 0 := by
    rw [h]
    have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize n % 4 = a at this ⊢
    interval_cases a <;> simp
  omega

theorem five_dvd_pow_sub_one_iff {q e : ℕ} (hq : q = 2 ^ e) (j : ℕ) :
    5 ∣ q ^ j - 1 ↔ 4 ∣ e * j := by
  rw [hq, ← pow_mul, five_dvd_two_pow_sub_one_iff]

theorem not_five_dvd_two_pow (e : ℕ) : ¬ 5 ∣ 2 ^ e := fun h =>
  absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h : 5 ∣ 2) (by norm_num)

theorem isPGroup_five_GL_two_pow_eq_bot {k : Type*} [Field k] [Fintype k] {f m : ℕ}
    (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hm : m ≤ 3)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : P = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine isPGroup_eq_bot_GL (hk ▸ not_five_dvd_two_pow f) (fun j hj1 hjm => ?_) P hP
  rw [five_dvd_pow_sub_one_iff hk]
  obtain ⟨a, ha⟩ := hf
  have : j ≤ 3 := by omega
  interval_cases j <;> omega

theorem isCyclic_of_isPGroup_five_GL_two_pow {k : Type*} [Field k] [Fintype k] {f m : ℕ}
    (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hm : m ≤ 7)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : IsCyclic P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases h4 : 4 ≤ m
  · refine isCyclic_of_isPGroup_GL (d := 4) (by norm_num) h4 (hk ▸ not_five_dvd_two_pow f)
      (fun j hj1 hjm hj4 => ?_) P hP
    rw [five_dvd_pow_sub_one_iff hk]
    obtain ⟨a, ha⟩ := hf
    have : j ≤ 7 := by omega
    interval_cases j <;> omega
  · rw [isPGroup_five_GL_two_pow_eq_bot hf hk (by omega) P hP]
    infer_instance

theorem isCyclic_of_isPGroup_five_GL_four_pow {k : Type*} [Field k] [Fintype k] {f m : ℕ}
    (hf : Odd f) (hk : Fintype.card k = 4 ^ f) (hm : m ≤ 3)
    (P : Subgroup (GL (Fin m) k)) (hP : IsPGroup 5 P) : IsCyclic P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hk' : Fintype.card k = 2 ^ (2 * f) := by rw [hk, pow_mul]; norm_num
  obtain ⟨a, ha⟩ := hf
  by_cases h2 : 2 ≤ m
  · refine isCyclic_of_isPGroup_GL (d := 2) (by norm_num) h2 (hk' ▸ not_five_dvd_two_pow _)
      (fun j hj1 hjm hj2 => ?_) P hP
    rw [five_dvd_pow_sub_one_iff hk']
    have : j ≤ 3 := by omega
    interval_cases j <;> omega
  · have hbot : P = ⊥ := by
      refine isPGroup_eq_bot_GL (hk' ▸ not_five_dvd_two_pow _) (fun j hj1 hjm => ?_) P hP
      rw [five_dvd_pow_sub_one_iff hk']
      obtain rfl : j = 1 := by omega
      omega
    rw [hbot]
    infer_instance

theorem isCyclic_of_isPGroup_five_of_injective_GL_two_pow {X : Type*} [Group X] {k : Type*}
    [Field k] [Fintype k] {f m : ℕ} (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hm : m ≤ 7)
    (φ : X →* GL (Fin m) k) (hφ : Function.Injective φ) (P : Subgroup X) (hP : IsPGroup 5 P) :
    IsCyclic P :=
  isCyclic_of_isPGroup_of_injective φ hφ (isCyclic_of_isPGroup_five_GL_two_pow hf hk hm) hP

theorem eq_bot_of_isPGroup_five_of_injective_GL_two_pow {X : Type*} [Group X] {k : Type*}
    [Field k] [Fintype k] {f m : ℕ} (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hm : m ≤ 3)
    (φ : X →* GL (Fin m) k) (hφ : Function.Injective φ) (P : Subgroup X) (hP : IsPGroup 5 P) :
    P = ⊥ :=
  eq_bot_of_isPGroup_of_injective φ hφ (isPGroup_five_GL_two_pow_eq_bot hf hk hm) hP

theorem isCyclic_of_isPGroup_five_of_injective_GL_four_pow {X : Type*} [Group X] {k : Type*}
    [Field k] [Fintype k] {f m : ℕ} (hf : Odd f) (hk : Fintype.card k = 4 ^ f) (hm : m ≤ 3)
    (φ : X →* GL (Fin m) k) (hφ : Function.Injective φ) (P : Subgroup X) (hP : IsPGroup 5 P) :
    IsCyclic P :=
  isCyclic_of_isPGroup_of_injective φ hφ (isCyclic_of_isPGroup_five_GL_four_pow hf hk hm) hP

theorem isCyclic_of_isPGroup_five_of_injective_GeneralLinearGroup_two_pow {X : Type*} [Group X]
    {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {f : ℕ} (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hV : Module.finrank k V ≤ 7)
    (φ : X →* LinearMap.GeneralLinearGroup k V) (hφ : Function.Injective φ) (P : Subgroup X)
    (hP : IsPGroup 5 P) : IsCyclic P := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_finrank_eq (rfl : Module.finrank k V = _)
  exact isCyclic_of_isPGroup_five_of_injective_GL_two_pow hf hk hV (e.toMonoidHom.comp φ)
    (e.injective.comp hφ) P hP

theorem eq_bot_of_isPGroup_five_of_injective_GeneralLinearGroup_two_pow {X : Type*} [Group X]
    {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {f : ℕ} (hf : Odd f) (hk : Fintype.card k = 2 ^ f) (hV : Module.finrank k V ≤ 3)
    (φ : X →* LinearMap.GeneralLinearGroup k V) (hφ : Function.Injective φ) (P : Subgroup X)
    (hP : IsPGroup 5 P) : P = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_finrank_eq (rfl : Module.finrank k V = _)
  exact eq_bot_of_isPGroup_five_of_injective_GL_two_pow hf hk hV (e.toMonoidHom.comp φ)
    (e.injective.comp hφ) P hP

end CFSG.AGLEmbeddingD2.CyclicSylowGL
