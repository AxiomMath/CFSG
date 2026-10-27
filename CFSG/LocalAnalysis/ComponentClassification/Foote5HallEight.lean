module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallApply
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSubBase

public section

namespace CFSG.ComponentClassification.Foote5.HallD8

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {G : Type} [Group G]

section Sixteen

variable {P : Subgroup G} {y u : G}

theorem exists_normal_form [Finite G] (hP : Nat.card P = 16) (hyP : y ∈ P) (huP : u ∈ P)
    (hy8 : orderOf y = 8) (hu : u ∉ zpowers y) {p : G} (hp : p ∈ P) :
    ∃ i < 8, ∃ j < 2, p = y ^ i * u ^ j := by
  classical
  let f : Fin 8 × Fin 2 → G := fun ij => y ^ (ij.1 : ℕ) * u ^ (ij.2 : ℕ)
  have hy : ∀ n : ℕ, y ^ n ∈ zpowers y := fun n => pow_mem (mem_zpowers y) n
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f] at h
    have hj : j = j' := by
      by_contra hjj
      apply hu
      fin_cases j <;> fin_cases j' <;> simp at hjj h ⊢
      · have : u = (y ^ (i' : ℕ))⁻¹ * y ^ (i : ℕ) := by rw [h]; group
        rw [this]
        exact mul_mem (inv_mem (hy _)) (hy _)
      · have : u = (y ^ (i : ℕ))⁻¹ * y ^ (i' : ℕ) := by rw [← h]; group
        rw [this]
        exact mul_mem (inv_mem (hy _)) (hy _)
    subst hj
    have hi : y ^ (i : ℕ) = y ^ (i' : ℕ) := mul_right_cancel h
    rw [pow_inj_mod, hy8] at hi
    have hi' : (i : ℕ) = i' := by
      rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at hi
      exact hi
    rw [Fin.ext hi']
  have hsub : Set.range f ⊆ (P : Set G) := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact mul_mem (pow_mem hyP _) (pow_mem huP _)
  have hcard : (P : Set G).ncard ≤ (Set.range f).ncard := by
    rw [Set.ncard_range_of_injective hf, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hP]
    simp
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard
  have hpf : p ∈ Set.range f := by
    rw [heq]
    exact hp
  obtain ⟨⟨i, j⟩, rfl⟩ := hpf
  exact ⟨i, i.2, j, j.2, rfl⟩

theorem conj_pow_of_rel {k : ℕ} (hrel : u * y * u⁻¹ = y ^ k) (i : ℕ) :
    u * y ^ i * u⁻¹ = y ^ (k * i) := by
  rw [← conj_pow, hrel, ← pow_mul]

theorem sq_pow_mul_of_rel {k : ℕ} (hu2 : u * u = 1) (hrel : u * y * u⁻¹ = y ^ k) (i : ℕ) :
    (y ^ i * u) * (y ^ i * u) = y ^ ((k + 1) * i) := by
  have h : (y ^ i * u) * (y ^ i * u) = y ^ i * (u * y ^ i * u⁻¹) * (u * u) := by group
  rw [h, conj_pow_of_rel hrel, hu2, mul_one, ← pow_add, add_mul, one_mul, add_comm]

end Sixteen

variable [Finite G] {D : Subgroup G} (e : D ≃* DihedralGroup 4)
  (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
    ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)

include e hcl in
theorem hall_d8 :
    ∃ S₀ T : Subgroup G, IsSylowOf 2 T ⊤ ∧ D ≤ S₀ ∧ S₀ ≤ T ∧
      Open.fusionStronglyClosed (S₀ : Set G) T ∧
      (S₀ = D ∨ (AschbacherTheorem3.IsSemidihedralTwoGroup S₀ ∧
        Nat.card S₀ = 2 * Nat.card D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD8 : Nat.card D = 8 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD8]; norm_num)
  obtain ⟨T, hT, hDT⟩ := FooteLit.exists_isSylowOf_ge_of_le (le_top : D ≤ ⊤) hD2
  have hTN := le_normalizer_of_sic e hcl hT.isPGroup hDT
  have hDM := le_Mq e
  have hrot : ∀ {p g : G}, p ∈ Mq e → p * p = cen e → g⁻¹ * p * g ∈ T →
      g⁻¹ * p * g ∈ T ⊓ Mq e ∧ (g⁻¹ * p * g) * (g⁻¹ * p * g) = cen e := by
    intro p g hpM hp hpT
    have hg := mem_centralizer_of_conj e hcl hTN hp hpT
    refine ⟨mem_inf.mpr ⟨hpT, conj_mem_Mq e hg hpM⟩, ?_⟩
    have hgz : g * cen e = cen e * g := mem_centralizer_singleton_iff.mp hg
    calc (g⁻¹ * p * g) * (g⁻¹ * p * g) = g⁻¹ * (p * p) * g := by group
      _ = cen e := by
        rw [hp]
        calc g⁻¹ * cen e * g = g⁻¹ * (g * cen e) := by rw [hgz]; group
          _ = cen e := by group
  have hinv : ∀ {d g : G}, d ∈ D → d * d = 1 → g⁻¹ * d * g ∈ T → g⁻¹ * d * g ∈ D :=
    fun hd hd2 hdg => conj_mem_of_sic hcl hd hd2 (hTN hdg)
  have hrotD : ∀ {d : G}, d ∈ D → d * d ≠ 1 → d * d = cen e := by
    intro d hd hd1
    rcases mem_cases e hd with h | rfl | rfl
    · exact absurd h hd1
    · exact rot_mul_rot e
    · exact inv_rot_mul_inv_rot e
  have hclosed : (∀ x ∈ T ⊓ Mq e, x * x = cen e → x ∈ D) →
      Open.fusionStronglyClosed (D : Set G) T := by
    intro hP a ha g hag
    by_cases ha2 : a * a = 1
    · exact hinv ha ha2 hag
    · obtain ⟨hx, hx2⟩ := hrot (hDM ha) (hrotD ha ha2) hag
      exact hP _ hx hx2
  rcases hall_cases e hcl hT hDT with hA | ⟨hP16, y, hyP, hyD, hyz⟩
  · refine ⟨D, T, hT, le_rfl, hDT, hclosed fun x hx hx2 => hA x hx ?_, Or.inl rfl⟩
    rw [hx2]
    exact mem_zpowers _
  · set P := T ⊓ Mq e with hPdef
    have hyT : y ∈ T := (mem_inf.mp hyP).1
    have hy2 : y * y = rot e ∨ y * y = (rot e)⁻¹ := by
      rcases mem_cases e hyD with h | h | h
      · exfalso
        apply hyz
        rcases sq_cases e (hTN hyT) hyD h with h1 | h1 <;> rw [h1]
        · exact one_mem _
        · exact mem_zpowers _
      · exact Or.inl h
      · exact Or.inr h
    have hy4 : (y * y) * (y * y) = cen e := by
      rcases hy2 with h | h <;> rw [h]
      · exact rot_mul_rot e
      · exact inv_rot_mul_inv_rot e
    have hy4' : y ^ 4 = cen e := by
      rw [← hy4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have hy8 : orderOf y = 8 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := y) (by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hy4']
        exact cen_ne_one e) (by
        rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, hy4', sq, cen_mul_cen])
      rw [h]
      norm_num
    set u := refl e with hu
    have huD : u ∈ D := refl_mem e
    have huP : u ∈ P := mem_inf.mpr ⟨hDT huD, hDM huD⟩
    have hu2 : u * u = 1 := by
      apply eq_of_e_eq e (mul_mem huD huD) (one_mem D)
      rw [e_mul e huD huD, e_one, show e ⟨u, huD⟩ = sr 0 from e_symm e (sr 0)]
      decide
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have huy : u ∉ zpowers y := by
      intro hmem
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      apply refl_not_mem e
      rw [← hu, ← hk]
      have h2 : (y ^ k) ^ (2 : ℤ) = 1 := by
        rw [hk, zpow_two, hu2]
      have hdvd : (orderOf y : ℤ) ∣ k * 2 := by
        rw [← zpow_mul] at h2
        exact orderOf_dvd_iff_zpow_eq_one.mpr h2
      rw [hy8] at hdvd
      obtain ⟨j, hj⟩ : (4 : ℤ) ∣ k := by omega
      rw [hj, zpow_mul, show y ^ (4 : ℤ) = cen e by rw [← hy4']; norm_cast]
      exact zpow_mem (mem_zpowers _) j
    have hurot : u * rot e * u⁻¹ = (rot e)⁻¹ := by
      rcases inv_cases e huD hu2 with h | h | h
      · exact absurd (by rw [← hu, h]; exact one_mem _) (refl_not_mem e)
      · exact absurd (by rw [← hu, h]; exact mem_zpowers _) (refl_not_mem e)
      · exact h
    have huy2 : u * (y * y) * u⁻¹ = (y * y)⁻¹ := by
      rcases hy2 with h | h <;> rw [h]
      · exact hurot
      · rw [show u * (rot e)⁻¹ * u⁻¹ = (u * rot e * u⁻¹)⁻¹ by group, hurot]
    have hNF := fun {p : G} (hp : p ∈ P) => exists_normal_form hP16 hyP huP hy8 huy hp
    obtain ⟨k, hk8, hrel⟩ : ∃ k < 8, u * y * u⁻¹ = y ^ k := by
      have hm : u * y * u⁻¹ ∈ P := mul_mem (mul_mem huP hyP) (inv_mem huP)
      obtain ⟨i, hi, j, hj, hij⟩ := hNF hm
      interval_cases j
      · exact ⟨i, hi, by simpa using hij⟩
      · exfalso
        apply huy
        have : u = y ^ i * y⁻¹ := by
          rw [pow_one] at hij
          calc u = (u * y * u⁻¹) * u * y⁻¹ := by group
            _ = y ^ i * u * u * y⁻¹ := by rw [hij]
            _ = y ^ i * y⁻¹ := by rw [mul_assoc (y ^ i), hu2, mul_one]
        rw [this]
        exact mul_mem (pow_mem (mem_zpowers y) _) (inv_mem (mem_zpowers y))
    have hk : k = 3 ∨ k = 7 := by
      have h := huy2
      rw [show u * (y * y) * u⁻¹ = (u * y * u⁻¹) * (u * y * u⁻¹) by group, hrel] at h
      have h' : y ^ (2 * k + 2) = 1 := by
        calc y ^ (2 * k + 2) = (y ^ k * y ^ k) * (y * y) := by
              rw [← pow_add, ← two_mul, show y * y = y ^ 2 from (sq y).symm, ← pow_add]
          _ = 1 := by rw [h, inv_mul_cancel]
      have hdvd := orderOf_dvd_of_pow_eq_one h'
      rw [hy8] at hdvd
      omega
    rcases hk with rfl | rfl
    ·
      refine ⟨P, T, hT, le_inf hDT hDM, inf_le_left, ?_, Or.inr ⟨?_, ?_⟩⟩
      ·
        have hcases : ∀ p ∈ P, (p * p = 1 ∧ p ∈ D) ∨ p * p = cen e ∨
            (p * p) * (p * p) = cen e := by
          intro p hp
          obtain ⟨i, hi, j, hj, rfl⟩ := hNF hp
          have hyi : ∀ n : ℕ, y ^ (2 * n) ∈ D := fun n => by
            rw [pow_mul, sq]
            exact pow_mem hyD n
          have hy8' : y ^ 8 = 1 := by rw [← hy8]; exact pow_orderOf_eq_one y
          interval_cases j
          · simp only [pow_zero, mul_one]
            rcases Nat.even_or_odd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
            · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
              · left
                refine ⟨?_, by rw [← two_mul]; exact hyi _⟩
                rw [← pow_add, show m + m + (m + m) + (m + m + (m + m)) = 8 * m by ring,
                  pow_mul, hy8', one_pow]
              · right; left
                rw [← pow_add, show 2 * m + 1 + (2 * m + 1) + (2 * m + 1 + (2 * m + 1)) =
                  8 * m + 4 by ring, pow_add, pow_mul, hy8', one_pow, one_mul, hy4']
            · right; right
              rw [← pow_add, ← pow_add, show 2 * n + 1 + (2 * n + 1) +
                (2 * n + 1 + (2 * n + 1)) = 8 * n + 4 by ring, pow_add, pow_mul, hy8', one_pow,
                one_mul, hy4']
          · simp only [pow_one]
            rw [sq_pow_mul_of_rel hu2 hrel]
            rcases Nat.even_or_odd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
            · left
              refine ⟨by rw [show (3 + 1) * (n + n) = 8 * n by ring, pow_mul, hy8', one_pow], ?_⟩
              rw [← two_mul]
              exact mul_mem (hyi n) huD
            · right; left
              rw [show (3 + 1) * (2 * n + 1) = 8 * n + 4 by ring, pow_add, pow_mul, hy8',
                one_pow, one_mul, hy4']
        intro p hp g hpg
        rcases hcases p hp with ⟨hp2, hpD⟩ | hp2 | hp4
        · exact le_inf hDT hDM (hinv hpD hp2 hpg)
        · exact (hrot (mem_inf.mp hp).2 hp2 hpg).1
        · have hq : g⁻¹ * (p * p) * g ∈ T := by
            rw [show g⁻¹ * (p * p) * g = (g⁻¹ * p * g) * (g⁻¹ * p * g) by group]
            exact mul_mem hpg hpg
          have hg := mem_centralizer_of_conj e hcl hTN hp4 hq
          exact mem_inf.mpr ⟨hpg, conj_mem_Mq e hg (mem_inf.mp hp).2⟩
      · refine ⟨4, le_rfl, ?_⟩
        exact FooteLit.TwoSub.nonempty_mulEquiv_semidihedral_of (n := 4) le_rfl
          (by rw [hP16]; norm_num) hyP huP (by rw [hy8]; norm_num) (by rw [sq, hu2])
          (by norm_num [hrel]) huy
      · rw [hP16, hD8]
    ·
      refine ⟨D, T, hT, le_rfl, hDT, hclosed fun x hx hx2 => ?_, Or.inl rfl⟩
      obtain ⟨i, hi, j, hj, rfl⟩ := hNF hx
      have hy8' : y ^ 8 = 1 := by rw [← hy8]; exact pow_orderOf_eq_one y
      interval_cases j
      · simp only [pow_zero, mul_one] at hx2 ⊢
        rw [← pow_add, ← hy4'] at hx2
        have hmod := (pow_inj_mod.mp hx2)
        rw [hy8] at hmod
        have hi' : i = 2 ∨ i = 6 := by omega
        rcases hi' with rfl | rfl
        · rw [sq]
          exact hyD
        · rw [show y ^ 6 = (y ^ 2)⁻¹ from eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact hy8'),
            sq]
          exact inv_mem hyD
      · exfalso
        simp only [pow_one] at hx2
        rw [sq_pow_mul_of_rel hu2 hrel, show (7 + 1) * i = 8 * i by ring, pow_mul, hy8',
          one_pow] at hx2
        exact cen_ne_one e hx2.symm

end CFSG.ComponentClassification.Foote5.HallD8
