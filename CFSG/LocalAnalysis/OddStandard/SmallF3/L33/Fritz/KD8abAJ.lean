module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAI

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open KD7 Sec8

section Generic

variable {X : Type} [Group X] [Finite X]

theorem false_of_gen_transfer_one [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    {H K : Subgroup X} (hH : IsPGroup 2 H)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → H ≤ R → R = H) (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    (habel : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ K) {g : X} (hgH : g ∈ H) (hgK : g ∉ K)
    (hgp : ∃ n : ℕ, g ^ 2 ^ n = 1)
    (hfus : ∀ (m : ℤ) (a : X), a⁻¹ * g ^ m * a ∈ H → (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := sylowOfMax hH fun R hR hle => hmax R hR hle
  have hindex : Nat.Coprime 2 H.index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index
  have hKnormal : (K.subgroupOf H).Normal := by
    rw [normal_subgroupOf_iff hKH]
    intro k h hk hh
    exact hKn h hh k hk
  have hcomm : ⁅H, H⁆ ≤ K := by
    rw [commutator_le]
    intro a ha b hb
    exact habel a ha b hb
  have h1 := CFSG.Quasithin.generalized_thompson_transfer_one hindex ⟨hKH, hKnormal⟩ hcomm hgH
    hgK hgp hfus
  rw [commutator_eq_top hX] at h1
  exact h1 (mem_top g)

omit [Finite X] in
theorem comm_mem_of_sup_zpowers {K : Subgroup X} {d : X} (hN : d ∈ normalizer (K : Set X))
    (hd2 : d ^ 2 ∈ K) {a b : X} (ha : a ∈ K ⊔ zpowers d) (hb : b ∈ K ⊔ zpowers d) :
    a * b * a⁻¹ * b⁻¹ ∈ K := by
  have hle : K ⊔ zpowers d ≤ normalizer (K : Set X) := sup_le le_normalizer (zpowers_le.mpr hN)
  have hdi : d⁻¹ ∈ normalizer (K : Set X) := inv_mem hN
  have hconj : ∀ {g k : X}, g ∈ K ⊔ zpowers d → k ∈ K → g * k * g⁻¹ ∈ K := fun hg hk =>
    Sec7.conj_mem_of_mem_normalizer (hle hg) hk
  rcases Sec7.mem_or_of_mem_sup_zpowers hN hd2 ha with ha' | ha' <;>
    rcases Sec7.mem_or_of_mem_sup_zpowers hN hd2 hb with hb' | hb'
  · exact mul_mem (mul_mem (mul_mem ha' hb') (inv_mem ha')) (inv_mem hb')
  · rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem ha' (hconj hb (inv_mem ha'))
  · exact mul_mem (hconj ha hb') (inv_mem hb')
  · rw [show a * b * a⁻¹ * b⁻¹ = (a * d⁻¹) * (d * (b * d⁻¹) * d⁻¹) *
      (d * (a * d⁻¹)⁻¹ * d⁻¹) * (b * d⁻¹)⁻¹ by group]
    exact mul_mem (mul_mem (mul_mem ha' (Sec7.conj_mem_of_mem_normalizer hN hb'))
      (Sec7.conj_mem_of_mem_normalizer hN (inv_mem ha'))) (inv_mem hb')

end Generic

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

theorem ι_mem_M₀_iff (H : AD S T₁) (c : MA) :
    H.ι c ∈ MA.M.map H.ι ↔ MA.inM c = true :=
  ⟨fun ⟨_, hc', he⟩ => H.ι_injective he ▸ hc', fun h => ⟨c, h, rfl⟩⟩

namespace TD

variable {H : AD S T₁} (T : H.TD)

theorem t_mem_R₂ : t ∈ T.R₂ := by
  have h := T.ι_mem_R₂ MA.t
  rwa [H.ι_t] at h

theorem d_mul_d_t (he : T.e = true) : T.d * T.d = t := by
  rw [T.sq, he]; exact H.ι_t

theorem sq_ne_one (he : T.e = true) {x : X} (hx : x ∈ T.T₂) (hxR : x ∉ T.R₂) : x * x ≠ 1 := by
  obtain ⟨a, i, j, rfl⟩ := T.T₂_cases hx
  cases j
  · exfalso; apply hxR
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    refine mul_mem (T.ι_mem_R₂ a) ?_
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact one_mem _
    · simp only [↓reduceIte]; exact T.p_mem_R₂
  simp only [↓reduceIte]
  intro hx1
  have key := noinv T.c₂ T.hc₂
  by_cases haT : MA.inT1 a = true
  · cases i
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hx1
      have e : H.ι a * T.d * (H.ι a * T.d) = H.ι (a * dc T.e T.c₂ a * tE T.e) := by
        rw [map_mul, map_mul, T.conj a haT, ← T.sq]; group
      rw [e, he] at hx1
      exact (key a haT).1 (H.ι_injective (hx1.trans (map_one _).symm))
    · simp only [↓reduceIte] at hx1
      apply T.p_not_mem_S₁
      set c := H.ι (dc T.e T.c₂ a) * H.ι (tE T.e * MA.w₂ * tE T.e) * H.ι (tE T.e) with hc
      have e : H.ι a * T.p * T.d * (H.ι a * T.p * T.d) = H.ι a * T.p * c := by
        rw [hc, T.conj a haT, ← T.d_conj_p, ← T.sq]; group
      rw [e] at hx1
      have h1 : T.p = (H.ι a)⁻¹ * c⁻¹ := by
        calc T.p = (H.ι a)⁻¹ * (H.ι a * T.p * c) * c⁻¹ := by group
          _ = (H.ι a)⁻¹ * c⁻¹ := by rw [hx1]; group
      rw [h1]
      exact mul_mem (inv_mem (H.ι_mem_S₁ _)) (inv_mem (mul_mem (mul_mem (H.ι_mem_S₁ _)
        (H.ι_mem_S₁ _)) (H.ι_mem_S₁ _)))
  · obtain ⟨b, hb, rfl⟩ : ∃ b : MA, MA.inT1 b = true ∧ a = MA.w₂ * b :=
      ⟨MA.w₂ * a, T1_of_not a (by simpa using haT), by rw [← mul_assoc, MA.w₂_sq, one_mul]⟩
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hx1
      apply T.p_not_mem_S₁
      set c := H.ι (dc T.e T.c₂ b) * H.ι (tE T.e) with hc
      have e : H.ι (MA.w₂ * b) * T.d * (H.ι (MA.w₂ * b) * T.d) =
          H.ι (MA.w₂ * b) * T.p * c := by
        calc H.ι (MA.w₂ * b) * T.d * (H.ι (MA.w₂ * b) * T.d) =
            H.ι (MA.w₂ * b) * (T.d * H.ι (MA.w₂ * b) * T.d⁻¹) * (T.d * T.d) := by group
          _ = H.ι (MA.w₂ * b) * T.p * c := by rw [T.d_conj_ι_w₂ b hb, T.sq, hc]; group
      rw [e] at hx1
      have h1 : T.p = (H.ι (MA.w₂ * b))⁻¹ * c⁻¹ := by
        calc T.p = (H.ι (MA.w₂ * b))⁻¹ * (H.ι (MA.w₂ * b) * T.p * c) * c⁻¹ := by group
          _ = (H.ι (MA.w₂ * b))⁻¹ * c⁻¹ := by rw [hx1]; group
      rw [h1]
      exact mul_mem (inv_mem (H.ι_mem_S₁ _)) (inv_mem (mul_mem (H.ι_mem_S₁ _) (H.ι_mem_S₁ _)))
    · simp only [↓reduceIte] at hx1
      have e : H.ι (MA.w₂ * b) * T.p * T.d * (H.ι (MA.w₂ * b) * T.p * T.d) =
          H.ι (MA.w₂ * b * dc T.e T.c₂ b * (tE T.e * MA.w₂ * tE T.e) * tE T.e) := by
        calc H.ι (MA.w₂ * b) * T.p * T.d * (H.ι (MA.w₂ * b) * T.p * T.d) =
            H.ι (MA.w₂ * b) * T.p * (T.d * H.ι (MA.w₂ * b) * T.d⁻¹) * (T.d * T.p * T.d⁻¹) *
              (T.d * T.d) := by group
          _ = H.ι (MA.w₂ * b) * (T.p * T.p) * H.ι (dc T.e T.c₂ b) *
              H.ι (tE T.e * MA.w₂ * tE T.e) * H.ι (tE T.e) := by
            rw [T.d_conj_ι_w₂ b hb, T.d_conj_p, T.sq]; group
          _ = _ := by rw [T.p_mul_p, mul_one]; simp only [map_mul]
      rw [e, he] at hx1
      exact (key b hb).2 (H.ι_injective (hx1.trans (map_one _).symm))

theorem conj_t_mem_R₂ (he : T.e = true) {y : X} (hy : y ∈ T.T₂) (hc : ConjTo t y) : y ∈ T.R₂ :=
  by_contra fun hyR => T.sq_ne_one he hy hyR (SPkg.sq_of_conjTo hc (tt (A := A)))

theorem max_T₂ (he : T.e = true) {R : Subgroup X} (hR : IsPGroup 2 R) (hle : T.T₂ ≤ R) :
    R = T.T₂ :=
  eq_of_conj A T.Tp_le_T₂ T.Tp_le_centralizer T.card_T_le_Tp (fun _ _ _ h _ hh => by
    have hy : h * t * h⁻¹ ∈ T.T₂ := Sec7.conj_mem_of_mem_normalizer hh T.t_mem_T₂
    obtain ⟨r, hr, hre⟩ := T.exists_conj_R₂ (T.conj_t_mem_R₂ he hy ⟨h, rfl⟩) ⟨h, rfl⟩
    exact ⟨r, T.R₂_le_T₂ hr, hre⟩) hR hle

theorem not_conjTo_sq {r : X} (hr : r ∈ T.R₂) : ¬ ConjTo t (r * r) := by
  rcases T.mem_R₂ hr with h | h
  · obtain ⟨a, rfl⟩ := H.mem_range_of_mem_S₁ h
    rw [← map_mul]
    exact H.not_conjTo_M₀ ⟨a * a, sq_M a, rfl⟩
  · obtain ⟨a, ha⟩ := H.mem_range_of_mem_S₁ h
    have hre : r = H.ι a * T.p := by rw [ha]; group
    obtain ⟨a', ha'⟩ := H.mem_range_of_mem_S₁
      (Sec7.conj_mem_of_mem_normalizer T.p_mem_normalizer (H.ι_mem_S₁ a))
    have hsq : r * r = H.ι (a * a') := by
      rw [hre, map_mul, ha']
      calc H.ι a * T.p * (H.ι a * T.p) = H.ι a * (T.p * H.ι a * T.p⁻¹) * (T.p * T.p) := by
            group
        _ = H.ι a * (T.p * H.ι a * T.p⁻¹) := by rw [T.p_mul_p, mul_one]
    have hM : MA.inM a = true ↔ MA.inM a' = true := by
      have h3 := mem_normalizer_iff.mp T.p_mem_normalizer_M₀ (H.ι a)
      rw [← ha', H.ι_mem_M₀_iff, H.ι_mem_M₀_iff] at h3
      exact h3
    rw [hsq]
    refine H.not_conjTo_M₀ ⟨a * a', ?_, rfl⟩
    cases h1 : MA.inM a
    · have h2 : MA.inM a' = false := by
        cases h2 : MA.inM a'
        · rfl
        · rw [← hM, h1] at h2; exact h2.symm
      rw [show a * a' = (a * MA.t) * (MA.t * a') by
        rw [mul_assoc, ← mul_assoc MA.t, t_mul_t, one_mul]]
      exact MA.M.mul_mem (show MA.inM (a * MA.t) = true by rw [MA.inM_mul_t, h1]; rfl)
        (show MA.inM (MA.t * a') = true by rw [inM_t_mul, h2]; rfl)
    · exact MA.M.mul_mem h1 (hM.mp h1)

theorem d_zpow_even (he : T.e = true) (j : ℤ) : T.d ^ (2 * j) = 1 ∨ T.d ^ (2 * j) = t := by
  rw [zpow_mul, zpow_two, T.d_mul_d_t he]
  rcases Int.even_or_odd' j with ⟨i, rfl | rfl⟩
  · left; rw [zpow_mul, zpow_two, tt (A := A), one_zpow]
  · right; rw [zpow_add_one, zpow_mul, zpow_two, tt (A := A), one_zpow, one_mul]

theorem d_zpow_odd (he : T.e = true) (j : ℤ) :
    T.d ^ (2 * j + 1) = T.d ∨ T.d ^ (2 * j + 1) = t * T.d := by
  rw [zpow_add_one]
  rcases T.d_zpow_even he j with h | h <;> rw [h]
  · exact Or.inl (one_mul _)
  · exact Or.inr rfl

theorem inv_mul_mem_R₂ {x y : X} (hx : x ∈ T.T₂) (hxR : x ∉ T.R₂) (hy : y ∈ T.T₂)
    (hyR : y ∉ T.R₂) : x⁻¹ * y ∈ T.R₂ := by
  have hx' := (T.mem_T₂ hx).resolve_left hxR
  have hy' := (T.mem_T₂ hy).resolve_left hyR
  have h1 := Sec7.conj_mem_of_mem_normalizer (inv_mem T.d_mem_normalizer_R₂)
    (mul_mem (inv_mem hx') hy')
  rwa [show T.d⁻¹ * ((x * T.d⁻¹)⁻¹ * (y * T.d⁻¹)) * T.d⁻¹⁻¹ = x⁻¹ * y by group] at h1

theorem false_of_e_true [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) (he : T.e = true) :
    False := by
  have hN : T.T₂ ≤ normalizer (T.R₂ : Set X) :=
    sup_le le_normalizer (zpowers_le.mpr T.d_mem_normalizer_R₂)
  refine false_of_gen_transfer_one hX T.isPGroup_T₂ (fun R hR hle => T.max_T₂ he hR hle)
    T.R₂_le_T₂ (fun h hh k hk => Sec7.conj_mem_of_mem_normalizer (hN hh) hk)
    (fun a ha b hb => comm_mem_of_sup_zpowers T.d_mem_normalizer_R₂
      (by rw [pow_two]; exact T.d_sq_mem_R₂) ha hb)
    T.d_mem_T₂ T.d_not_mem_R₂ ⟨2, by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; exact T.d_pow_four⟩ ?_
  intro m a hma
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · rcases T.d_zpow_even he j with h | h <;> rw [h] at hma ⊢
    · rw [inv_one, one_mul, mul_one, inv_mul_cancel]; exact one_mem _
    · exact mul_mem (inv_mem T.t_mem_R₂) (T.conj_t_mem_R₂ he hma ⟨a⁻¹, by group⟩)
  · have hyT : T.d ^ (2 * j + 1) ∈ T.T₂ := zpow_mem T.d_mem_T₂ _
    have hyR : T.d ^ (2 * j + 1) ∉ T.R₂ := by
      rcases T.d_zpow_odd he j with h | h <;> rw [h]
      · exact T.d_not_mem_R₂
      · intro h'
        apply T.d_not_mem_R₂
        have := mul_mem (inv_mem T.t_mem_R₂) h'
        rwa [inv_mul_cancel_left] at this
    have hy2 : T.d ^ (2 * j + 1) * T.d ^ (2 * j + 1) = t := by
      rcases T.d_zpow_odd he j with h | h <;> rw [h]
      · exact T.d_mul_d_t he
      · rw [show t * T.d * (t * T.d) = t * (T.d * t) * T.d by group, T.d_comm_t,
          show t * (t * T.d) * T.d = (t * t) * (T.d * T.d) by group, tt (A := A), one_mul,
          T.d_mul_d_t he]
    have hay : a⁻¹ * T.d ^ (2 * j + 1) * a ∉ T.R₂ := fun h' => T.not_conjTo_sq h' ⟨a⁻¹, by
      rw [show a⁻¹ * T.d ^ (2 * j + 1) * a * (a⁻¹ * T.d ^ (2 * j + 1) * a) =
        a⁻¹ * (T.d ^ (2 * j + 1) * T.d ^ (2 * j + 1)) * a by group, hy2]; group⟩
    exact T.inv_mul_mem_R₂ hyT hyR hma hay

end TD

end AD

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
