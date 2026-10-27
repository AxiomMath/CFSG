module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

namespace ExistsZ

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

theorem inv_eq_self_of_sq {a : G} (ha : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rwa [← pow_two])

theorem mul_comm_of_sq {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  have h1 := inv_eq_self_of_sq ha
  have h2 := inv_eq_self_of_sq hb
  have h3 := inv_eq_self_of_sq hab
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h2]

theorem comm_of_sq {a b : G} (hE : ∀ e ∈ E, e ^ 2 = 1) (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a :=
  mul_comm_of_sq (hE a ha) (hE b hb) (hE _ (mul_mem ha hb))

theorem normClass_subset {x : G} (hx : x ∈ E) : normClass E x ⊆ E := by
  rintro y ⟨n, hn, rfl⟩
  exact (mem_normalizer_iff.1 hn x).1 hx

theorem conj_mem_normClass {x y n : G} (hy : y ∈ normClass E x)
    (hn : n ∈ normalizer (E : Set G)) : n * y * n⁻¹ ∈ normClass E x := by
  obtain ⟨m, hm, rfl⟩ := hy
  refine ⟨n * m, mul_mem hn hm, ?_⟩
  simp only [mul_inv_rev, mul_assoc]

theorem one_notMem_normClass (ht : t ≠ 1) : (1 : G) ∉ normClass E t := by
  rintro ⟨n, -, h⟩
  apply ht
  have := congrArg (fun y => n⁻¹ * y * n) h
  simpa [mul_assoc] using this

theorem mul_mem_normClass_of_not_exists (hE : ∀ e ∈ E, e ^ 2 = 1) (htE : t ∈ E)
    (hno : ¬ ∃ z, IsZ E t z) {a b : G} (ha : a ∈ normClass E t) (hb : b ∈ normClass E t)
    (hab : a ≠ b) : a * b ∈ normClass E t := by
  obtain ⟨n, hn, hna⟩ := ha
  have hnE : ∀ e ∈ E, n⁻¹ * e * n ∈ E := fun e he => by
    have := (mem_normalizer_iff.1 (inv_mem hn) e).1 he
    simpa using this
  have haE : a ∈ E := hna ▸ (mem_normalizer_iff.1 hn t).1 htE
  have hbE : b ∈ E := normClass_subset htE hb
  have hconj : n⁻¹ * a * n = t := by rw [← hna]; group
  by_contra hmem
  apply hno
  refine ⟨n⁻¹ * (a * b) * n, hnE _ (mul_mem haE hbE), ?_, ?_, ?_⟩
  · intro h1
    apply hab
    have h2 : a * b = 1 := by
      have := congrArg (fun y => n * y * n⁻¹) h1
      simpa [mul_assoc] using this
    have h3 : a⁻¹ = b := inv_eq_of_mul_eq_one_right h2
    rw [← h3]
    exact (inv_eq_self_of_sq (hE a haE)).symm
  · intro h1
    apply hmem
    have h2 := conj_mem_normClass h1 hn
    have h3 : n * (n⁻¹ * (a * b) * n) * n⁻¹ = a * b := by group
    rwa [h3] at h2
  · have hsq : a * a = 1 := by rw [← pow_two]; exact hE a haE
    have h2 : t * (n⁻¹ * (a * b) * n) = n⁻¹ * b * n := by
      calc t * (n⁻¹ * (a * b) * n) = (n⁻¹ * a * n) * (n⁻¹ * (a * b) * n) := by rw [hconj]
        _ = n⁻¹ * ((a * a) * b) * n := by group
        _ = n⁻¹ * b * n := by rw [hsq, one_mul]
    rw [h2]
    obtain ⟨m, hm, hmb⟩ := hb
    refine ⟨n⁻¹ * m, mul_mem (inv_mem hn) hm, ?_⟩
    rw [← hmb]
    group

end ExistsZ

theorem exists_isZ_of_m24Out {G : Type} [Group G] {E : Subgroup G} {t : G} (hm : M24Out G E t) :
    ∃ z, IsZ E t z := by
  by_contra hno
  set C : Set G := normClass E t with hC
  have hCE : C ⊆ E := ExistsZ.normClass_subset hm.t_mem
  have h1 : (1 : G) ∉ C := ExistsZ.one_notMem_normClass hm.t_ne_one
  have hfin : C.Finite := Set.finite_of_ncard_ne_zero (by rw [hC, hm.ncard_t]; norm_num)
  let S : Subgroup G :=
    { carrier := insert 1 C
      mul_mem' := by
        intro x y hx hy
        rcases hx with rfl | hx
        · rw [one_mul]; exact hy
        rcases hy with rfl | hy
        · rw [mul_one]; exact Or.inr hx
        by_cases hxy : x = y
        · subst hxy
          left
          rw [← pow_two]
          exact hm.E_sq x (hCE hx)
        · right
          exact ExistsZ.mul_mem_normClass_of_not_exists hm.E_sq hm.t_mem hno hx hy hxy
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro x hx
        rcases hx with rfl | hx
        · simp
        · right
          rw [ExistsZ.inv_eq_self_of_sq (hm.E_sq x (hCE hx))]
          exact hx }
  have hSE : S ≤ E := by
    intro x hx
    rcases hx with rfl | hx
    · exact one_mem E
    · exact hCE hx
  have hcard : Nat.card S = 277 := by
    have h2 : Nat.card S = (insert (1 : G) C).ncard := Nat.card_coe_set_eq (insert (1 : G) C)
    rw [h2, Set.ncard_insert_of_notMem h1 hfin, hC, hm.ncard_t]
  have hdvd : Nat.card S ∣ Nat.card E := Subgroup.card_dvd_of_le hSE
  rw [hcard, hm.card_E] at hdvd
  exact absurd hdvd (by norm_num)

theorem exists_z_holds : ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (t : G),
    M24Out G E t → ∃ z, IsZ E t z :=
  fun _ _ _ _ _ hm => exists_isZ_of_m24Out hm

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
