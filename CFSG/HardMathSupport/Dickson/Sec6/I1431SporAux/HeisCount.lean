module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenCensus

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

@[expose] def lineOn (t : Bool) (a b : ℕ) : Bool :=
  censusLines.any fun e => e.toC == t && (List.range 13).any fun μ =>
    μ != 0 && (μ * e.a) % 13 == a && (μ * e.b) % 13 == b

theorem lineOn_partition : (List.range 13).all (fun a => (List.range 13).all fun b =>
    (a == 0 && b == 0) || (lineOn true a b != lineOn false a b)) = true := by
  decide

theorem lineOn_count_x : ∑ a ∈ Finset.range 13, ∑ b ∈ Finset.range 13,
    (if a = 0 ∧ b = 0 then 0 else if lineOn false a b then 1 else 0) = 96 := by
  decide

theorem lineOn_count_c : ∑ a ∈ Finset.range 13, ∑ b ∈ Finset.range 13,
    (if a = 0 ∧ b = 0 then 0 else if lineOn false a b then 0 else 1) = 72 := by
  decide

theorem sum_blocks (A Fc Fx : ℕ) : ∑ a ∈ Finset.range 13, ∑ b ∈ Finset.range 13,
    (if a = 0 ∧ b = 0 then A else 13 * (if lineOn false a b then Fx else Fc)) =
      A + 13 * (96 * Fx + 72 * Fc) := by
  have h0 : ∑ a ∈ Finset.range 13, ∑ b ∈ Finset.range 13,
      (if a = 0 ∧ b = 0 then 1 else 0) = 1 := by decide
  have hpt : ∀ a b : ℕ, (if a = 0 ∧ b = 0 then A else 13 * (if lineOn false a b then Fx else Fc)) =
      A * (if a = 0 ∧ b = 0 then 1 else 0) +
        13 * Fx * (if a = 0 ∧ b = 0 then 0 else if lineOn false a b then 1 else 0) +
        13 * Fc * (if a = 0 ∧ b = 0 then 0 else if lineOn false a b then 0 else 1) := by
    intro a b
    by_cases h : a = 0 ∧ b = 0 <;> by_cases h' : lineOn false a b = true <;> simp [h, h']
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h0, lineOn_count_x, lineOn_count_c]
  ring

section Conj

variable {G : Type*} [Group G] {g d c x : G}

theorem conj_line_element (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1)
    (hc1 : c ≠ 1) (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    {e : CensusLine} (he : e ∈ censusLines) {W : G}
    (hW : W * (g ^ e.a * d ^ e.b) * W⁻¹ = (if e.toC then c else x) ^ e.lam)
    {μ a b : ℕ} (hμ : μ % 13 ≠ 0) (hae : (μ * e.a) % 13 = a) (hbe : (μ * e.b) % 13 = b) (k : ℕ) :
    ∃ Y : G, Y * (g ^ a * d ^ b * c ^ k) * Y⁻¹ = (if e.toC then c else x) ^ (e.lam * μ) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  have hco : orderOf c = 13 := orderOf_eq_prime hc13 hc1
  obtain ⟨f, hf⟩ := heis_pow hcg hcd hdg hc13 e.a e.b μ
  have hga : g ^ a = g ^ (e.a * μ) := by
    rw [pow_eq_pow_mod (e.a * μ) hg13, mul_comm e.a μ, hae]
  have hdb : d ^ b = d ^ (e.b * μ) := by
    rw [pow_eq_pow_mod (e.b * μ) hd13, mul_comm e.b μ, hbe]
  set se := g ^ e.a * d ^ e.b with hse
  have hcse : Commute c se := (hcg'.pow_right _).mul_right (hcd'.pow_right _)
  have htse : g ^ a * d ^ b * c ^ k = se ^ μ * c ^ (f + k) := by
    rw [hga, hdb, hf, mul_assoc, ← pow_add]
  rw [htse]
  have hshape := lines_shape
  rw [List.all_eq_true] at hshape
  have hsh := hshape e he
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hsh
  obtain ⟨hab, hlam⟩ := hsh
  have hcentral : ∃ y : G, y * (se ^ μ * c ^ (f + k)) * y⁻¹ = se ^ μ := by
    rcases hab with hab1 | ⟨ha0, hb1⟩
    · obtain ⟨j, hj⟩ := exists_j_mod (4 * μ) (f + k) (by omega)
      refine ⟨d ^ j, ?_⟩
      have hconj : d ^ j * se * (d ^ j)⁻¹ = se * c ^ (4 * j) := by
        rw [hse, hab1, pow_one]; exact dpow_conj hcg hcd hdg e.b j
      have hpow : d ^ j * se ^ μ * (d ^ j)⁻¹ = se ^ μ * c ^ (4 * j * μ) := by
        rw [← conj_pow, hconj, (hcse.symm.pow_right _).mul_pow, ← pow_mul]
      calc d ^ j * (se ^ μ * c ^ (f + k)) * (d ^ j)⁻¹ =
          d ^ j * se ^ μ * (d ^ j)⁻¹ * (d ^ j * c ^ (f + k) * (d ^ j)⁻¹) := by group
        _ = se ^ μ * c ^ (4 * j * μ) * c ^ (f + k) := by
            rw [hpow, ← (hcd'.pow_pow (f + k) j).eq, mul_inv_cancel_right]
        _ = se ^ μ := by
            rw [mul_assoc, ← pow_add, ← pow_mod_orderOf c, hco,
              show (4 * j * μ + (f + k)) % 13 = 0 by rw [mul_right_comm]; exact hj, pow_zero,
              mul_one]
    · obtain ⟨j, hj⟩ := exists_j_mod (9 * μ) (f + k) (by omega)
      refine ⟨g ^ j, ?_⟩
      have hsed : se = d := by rw [hse, ha0, hb1, pow_zero, pow_one, one_mul]
      have hpow : g ^ j * se ^ μ * (g ^ j)⁻¹ = se ^ μ * c ^ (9 * j * μ) := by
        rw [← conj_pow, hsed, gpow_conj_d hcg hcd hdg hc13, (hcd'.symm.pow_right _).mul_pow,
          ← pow_mul]
      calc g ^ j * (se ^ μ * c ^ (f + k)) * (g ^ j)⁻¹ =
          g ^ j * se ^ μ * (g ^ j)⁻¹ * (g ^ j * c ^ (f + k) * (g ^ j)⁻¹) := by group
        _ = se ^ μ * c ^ (9 * j * μ) * c ^ (f + k) := by
            rw [hpow, ← (hcg'.pow_pow (f + k) j).eq, mul_inv_cancel_right]
        _ = se ^ μ := by
            rw [mul_assoc, ← pow_add, ← pow_mod_orderOf c, hco,
              show (9 * j * μ + (f + k)) % 13 = 0 by rw [mul_right_comm]; exact hj, pow_zero,
              mul_one]
  obtain ⟨y, hy⟩ := hcentral
  refine ⟨W * y, ?_⟩
  calc W * y * (se ^ μ * c ^ (f + k)) * (W * y)⁻¹ =
      W * (y * (se ^ μ * c ^ (f + k)) * y⁻¹) * W⁻¹ := by group
    _ = W * se ^ μ * W⁻¹ := by rw [hy]
    _ = ((if e.toC then c else x) ^ e.lam) ^ μ := by rw [← conj_pow, hW]
    _ = (if e.toC then c else x) ^ (e.lam * μ) := by rw [← pow_mul]

theorem exists_conj_of_lineOn (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1)
    (hc1 : c ≠ 1) (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hlines : ∀ e ∈ censusLines, ∃ W : G,
      W * (g ^ e.a * d ^ e.b) * W⁻¹ = (if e.toC then c else x) ^ e.lam)
    {t : Bool} {a b : ℕ} (h : lineOn t a b = true) (k : ℕ) :
    ∃ Y : G, ∃ j : ℕ, j % 13 ≠ 0 ∧
      Y * (g ^ a * d ^ b * c ^ k) * Y⁻¹ = (if t then c else x) ^ j := by
  unfold lineOn at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, hμ⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at hμ
  obtain ⟨het, μ, hμ13, hμe⟩ := hμ
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hμe
  obtain ⟨⟨hμ0, hae⟩, hbe⟩ := hμe
  have hμ13' : μ % 13 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hμ13]; exact hμ0
  have hshape := lines_shape
  rw [List.all_eq_true] at hshape
  have hsh := hshape e he
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hsh
  obtain ⟨-, hlam⟩ := hsh
  obtain ⟨W, hW⟩ := hlines e he
  obtain ⟨Y, hY⟩ := conj_line_element hg13 hd13 hc13 hc1 hcg hcd hdg he hW hμ13' hae hbe k
  refine ⟨Y, e.lam * μ, ?_, ?_⟩
  · intro h0
    have hdvd : 13 ∣ e.lam * μ := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 hdvd with h | h
    · exact hlam (Nat.mod_eq_zero_of_dvd h)
    · exact hμ13' (Nat.mod_eq_zero_of_dvd h)
  · rw [hY, het]

theorem sum_fin_triple (F : ℕ → ℕ → ℕ → ℕ) :
    ∑ t : Fin 13 × Fin 13 × Fin 13, F t.1.val t.2.1.val t.2.2.val =
      ∑ a ∈ Finset.range 13, ∑ b ∈ Finset.range 13, ∑ k ∈ Finset.range 13, F a b k := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range
    (fun a => ∑ b ∈ Finset.range 13, ∑ k ∈ Finset.range 13, F a b k) 13]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun b => ∑ k ∈ Finset.range 13, F a b k) 13]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k => F a b k) 13]

variable [Finite G]

theorem sum_over_sylow (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1)
    (hc1 : c ≠ 1) (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hlines : ∀ e ∈ censusLines, ∃ W : G,
      W * (g ^ e.a * d ^ e.b) * W⁻¹ = (if e.toC then c else x) ^ e.lam)
    {S : Subgroup G} [Fintype S] (hgS : g ∈ S) (hdS : d ∈ S) (hcS : c ∈ S)
    (hScard : Nat.card S = 13 ^ 3)
    (hSform : ∀ s ∈ S, ∃ a b k : ℕ, a < 13 ∧ b < 13 ∧ k < 13 ∧ s = g ^ a * d ^ b * c ^ k)
    (f : G → ℕ) (hf : ∀ w s : G, f (w * s * w⁻¹) = f s) {Fc Fx : ℕ}
    (hfc : ∀ j : ℕ, j % 13 ≠ 0 → f (c ^ j) = Fc) (hfx : ∀ j : ℕ, j % 13 ≠ 0 → f (x ^ j) = Fx) :
    ∑ s : S, f s = f 1 + 948 * Fc + 1248 * Fx := by
  have hmem : ∀ a b k : ℕ, g ^ a * d ^ b * c ^ k ∈ S := fun a b k =>
    S.mul_mem (S.mul_mem (S.pow_mem hgS _) (S.pow_mem hdS _)) (S.pow_mem hcS _)
  let ψ : Fin 13 × Fin 13 × Fin 13 → S := fun t =>
    ⟨g ^ t.1.val * d ^ t.2.1.val * c ^ t.2.2.val, hmem _ _ _⟩
  have hψs : Function.Surjective ψ := by
    intro s
    obtain ⟨a, b, k, ha, hb, hk, hs⟩ := hSform s.1 s.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨k, hk⟩), Subtype.ext hs.symm⟩
  have hψ : Function.Bijective ψ := by
    refine hψs.bijective_of_nat_card_le ?_
    rw [hScard]
    simp
  have hsum : ∑ s : S, f s = ∑ t : Fin 13 × Fin 13 × Fin 13,
      f (g ^ t.1.val * d ^ t.2.1.val * c ^ t.2.2.val) :=
    (Equiv.sum_comp (Equiv.ofBijective ψ hψ) (fun s : S => f s.1)).symm
  rw [hsum, sum_fin_triple (fun a b k => f (g ^ a * d ^ b * c ^ k))]
  have hval : ∀ a ∈ Finset.range 13, ∀ b ∈ Finset.range 13, ¬ (a = 0 ∧ b = 0) →
      ∀ k : ℕ, f (g ^ a * d ^ b * c ^ k) = if lineOn false a b then Fx else Fc := by
    intro a ha b hb hab k
    have hpart := lineOn_partition
    rw [List.all_eq_true] at hpart
    have h1 := hpart a (List.mem_range.2 (Finset.mem_range.1 ha))
    rw [List.all_eq_true] at h1
    have h2 := h1 b (List.mem_range.2 (Finset.mem_range.1 hb))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 hab
    · by_cases hx : lineOn false a b = true
      · obtain ⟨Y, j, hj, hY⟩ := exists_conj_of_lineOn hg13 hd13 hc13 hc1 hcg hcd hdg hlines hx k
        rw [if_pos hx, ← hf Y, hY]
        simpa using hfx j hj
      · have hc : lineOn true a b = true := by
          by_contra hcon
          apply h2
          simp only [Bool.not_eq_true] at hx hcon
          rw [hx, hcon]
        obtain ⟨Y, j, hj, hY⟩ := exists_conj_of_lineOn hg13 hd13 hc13 hc1 hcg hcd hdg hlines hc k
        rw [if_neg hx, ← hf Y, hY]
        simpa using hfc j hj
  have hblock : ∀ a ∈ Finset.range 13, ∀ b ∈ Finset.range 13,
      ∑ k ∈ Finset.range 13, f (g ^ a * d ^ b * c ^ k) =
        if a = 0 ∧ b = 0 then f 1 + 12 * Fc else 13 * (if lineOn false a b then Fx else Fc) := by
    intro a ha b hb
    by_cases hab : a = 0 ∧ b = 0
    · rw [if_pos hab, hab.1, hab.2]
      simp only [pow_zero, one_mul]
      rw [Finset.sum_range_succ']
      have : ∀ k ∈ Finset.range 12, f (c ^ (k + 1)) = Fc := fun k hk => by
        apply hfc
        have := Finset.mem_range.1 hk
        omega
      rw [Finset.sum_congr rfl this]
      simp [add_comm]
    · rw [if_neg hab, Finset.sum_congr rfl fun k _ => hval a ha b hb hab k]
      simp
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hblock a ha b hb,
    sum_blocks]
  ring

end Conj

end CFSG.HardMathSupport.Dickson.Sec6.I1431
