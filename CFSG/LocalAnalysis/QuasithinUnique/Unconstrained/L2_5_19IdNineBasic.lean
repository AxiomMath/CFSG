module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdAux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def TabThreeRankNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) → IsCaseGroup X →
      ∃ A : Subgroup G, A ≤ X ∧ IsElemAbelian 3 A ∧ Nat.card A = 9

section Gens

variable {Q : Type} [Group Q]

theorem pow_mul_pow_ne_one {x y : Q} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) :
    ∀ a b : ℕ, a < 3 → b < 3 → (a ≠ 0 ∨ b ≠ 0) → x ^ a * y ^ b ≠ 1 := by
  have hy1' : y ≠ 1 := fun h => hy1 0 (by rw [pow_zero, h])
  have hxinv : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)
  have hyinv : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy)
  have hx2inv : (x ^ 2)⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hx)
  have hx2 : x ^ 2 ≠ 1 := fun h => hx1 (by rw [← inv_eq_one, hxinv, h])
  have hy2 : y ^ 2 ≠ 1 := fun h => hy1' (by rw [← inv_eq_one, hyinv, h])
  have hy4 : y ^ 4 = y := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hy, one_mul]
  have hyx : y ≠ x := fun h => hy1 1 (by rw [pow_one, h])
  have hyx2 : y ≠ x ^ 2 := fun h => hy1 2 h.symm
  intro a b ha hb hne
  interval_cases a <;> interval_cases b
  · simp at hne
  · simpa using hy1'
  · simpa using hy2
  · simpa using hx1
  · intro h
    simp only [pow_one] at h
    exact hyx2 ((eq_inv_of_mul_eq_one_right h).trans hxinv)
  · intro h
    simp only [pow_one] at h
    have h2 : y ^ 2 = x⁻¹ := eq_inv_of_mul_eq_one_right h
    apply hyx
    calc y = y ^ 4 := hy4.symm
      _ = (y ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (x⁻¹) ^ 2 := by rw [h2]
      _ = x := by rw [hxinv, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_succ, hx, one_mul]
  · simpa using hx2
  · intro h
    simp only [pow_one] at h
    exact hyx ((eq_inv_of_mul_eq_one_right h).trans hx2inv)
  · intro h
    have h2 : y ^ 2 = (x ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
    apply hyx2
    calc y = y ^ 4 := hy4.symm
      _ = (y ^ 2) ^ 2 := by rw [← pow_mul]
      _ = ((x ^ 2)⁻¹) ^ 2 := by rw [h2]
      _ = x ^ 2 := by rw [hx2inv]

theorem hasElemAb_nine_of_gens {x y : Q} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) : HasElemAb 3 9 Q := by
  obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.exists_elemAbelian_of_commuting (![x, y] : Fin 2 → Q)
    (by intro i; fin_cases i <;> simpa)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hxy, hxy.symm])
    (by
      intro a ha
      have h0 := (a 0).isLt
      have h1 := (a 1).isLt
      have hne : (a 0 : ℕ) ≠ 0 ∨ (a 1 : ℕ) ≠ 0 := by
        by_contra h
        push Not at h
        apply ha
        funext i
        fin_cases i
        · exact Fin.ext h.1
        · exact Fin.ext h.2
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one]
      exact pow_mul_pow_ne_one hx hy hx1 hy1 _ _ h0 h1 hne)
  exact ⟨E, hE, by rw [hcard]; norm_num⟩

end Gens

section Lift

variable {X : Type} [Group X] [Finite X]

theorem HasElemAb.of_quotient_two (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N)
    (h : HasElemAb 3 9 (X ⧸ N)) : HasElemAb 3 9 X := by
  obtain ⟨E, hE, hcard⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hdvd : 3 ^ 2 ∣ Nat.card ↥(E.comap π) := by
    have hsurj : Function.Surjective (π.subgroupComap E) := by
      intro e
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e : X ⧸ N)
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [Subgroup.mem_comap]
      have hx' : π x = (e : X ⧸ N) := hx
      rw [hx']
      exact e.2
    have := Subgroup.card_dvd_of_surjective hsurj
    rw [hcard] at this
    simpa using this
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set K : Subgroup X := K₀.map (E.comap π).subtype with hK
  have hK9 : Nat.card ↥K = 9 := by
    rw [hK, Subgroup.card_map_of_injective (E.comap π).subtype_injective, hK₀]
    norm_num
  have hKE : ∀ k ∈ K, π k ∈ E := by
    rintro k ⟨k', -, rfl⟩
    exact k'.2
  have htriv : ∀ k ∈ K, π k = 1 → k = 1 := by
    intro k hk hπ
    have hkN : k ∈ N := (QuotientGroup.eq_one_iff k).mp hπ
    have h9 : orderOf k ∣ 9 := hK9 ▸ Subgroup.orderOf_dvd_natCard _ hk
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hN ⟨k, hkN⟩
    have hm' : orderOf k = 2 ^ m := (Subgroup.orderOf_coe (⟨k, hkN⟩ : N)).trans hm
    rw [hm'] at h9
    have h1 : 2 ^ m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left _ (by norm_num)) h9
    rw [h1] at hm'
    exact orderOf_eq_one_iff.mp hm'
  have hEc : IsMulCommutative ↥E := hE.1
  refine ⟨K, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, hK9⟩
  · apply Subtype.ext
    have hab : (a : X) * b = b * a := by
      have hmem : ((a : X) * b)⁻¹ * (b * a) ∈ K :=
        K.mul_mem (K.inv_mem (K.mul_mem a.2 b.2)) (K.mul_mem b.2 a.2)
      have hπ : π (((a : X) * b)⁻¹ * (b * a)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one]
        exact setLike_mul_comm (hKE a a.2) (hKE b b.2)
      exact inv_mul_eq_one.mp (htriv _ hmem hπ)
    exact hab
  · apply htriv _ (K.pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hKE x hx)

end Lift

section Alt

open Equiv Perm

theorem hasElemAb_nine_alt_aux {n : ℕ} {a b c d e f : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hx3 : (swap a b * swap a c) ^ 3 = 1)
    (hy3 : (swap d e * swap d f) ^ 3 = 1)
    (hcomm : swap a b * swap a c * (swap d e * swap d f) =
      swap d e * swap d f * (swap a b * swap a c))
    (hx1 : swap a b * swap a c ≠ 1)
    (hy1 : ∀ m : ℕ, (swap a b * swap a c) ^ m ≠ swap d e * swap d f) :
    HasElemAb 3 9 (alternatingGroup (Fin n)) := by
  have hxa : swap a b * swap a c ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hac]
    rfl
  have hya : swap d e * swap d f ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hde, sign_swap hdf]
    rfl
  refine hasElemAb_nine_of_gens (x := ⟨swap a b * swap a c, hxa⟩) (y := ⟨swap d e * swap d f, hya⟩)
    (Subtype.ext hx3) (Subtype.ext hy3) (Subtype.ext hcomm) (fun h => hx1 (congrArg Subtype.val h))
    (fun m h => hy1 m (congrArg Subtype.val h))

theorem hasElemAb_nine_alt_six : HasElemAb 3 9 (alternatingGroup (Fin 6)) := by
  refine hasElemAb_nine_alt_aux (a := 0) (b := 1) (c := 2) (d := 3) (e := 4) (f := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  intro m
  have h3 : (swap (0 : Fin 6) 1 * swap 0 2) ^ 3 = 1 := by decide
  rw [pow_eq_pow_mod m h3]
  have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 3) <;> decide

theorem hasElemAb_nine_alt_eight : HasElemAb 3 9 (alternatingGroup (Fin 8)) := by
  refine hasElemAb_nine_alt_aux (a := 0) (b := 1) (c := 2) (d := 3) (e := 4) (f := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  intro m
  have h3 : (swap (0 : Fin 8) 1 * swap 0 2) ^ 3 = 1 := by decide
  rw [pow_eq_pow_mod m h3]
  have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 3) <;> decide

end Alt

end CFSG.QuasithinUnique.Id2519
