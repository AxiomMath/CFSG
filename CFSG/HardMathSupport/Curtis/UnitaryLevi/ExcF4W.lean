module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.RankThree.PartOne.K133H.F4Weyl

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.K133H


@[expose] def laF : List (Fin Tag.F4.rank) := ([0, 1] : List (Fin 4))

@[expose] def lbF : List (Fin Tag.F4.rank) :=
  ([2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3] : List (Fin 4))

theorem laF_cube : wordW Tag.F4 (laF ++ laF ++ laF) = wordW Tag.F4 [] :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem lbF_cube : wordW Tag.F4 (lbF ++ lbF ++ lbF) = wordW Tag.F4 [] :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem laF_lbF_comm : wordW Tag.F4 (laF ++ lbF) = wordW Tag.F4 (lbF ++ laF) :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem pair_comm_of_closure {G : Type*} [Group G] (a b : G) (h : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x := by
  have hcomm : ∀ x ∈ ({a, b} : Set G), x ∈ Subgroup.centralizer ({a, b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact h | exact h.symm
  intro x hx y hy
  have h1 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({a, b} : Set G) :=
    (Subgroup.closure_le _).2 hcomm
  have h2 := h1 hx
  rw [← Subgroup.centralizer_closure] at h2
  exact (Subgroup.mem_centralizer_iff.1 h2 y hy).symm

@[expose] def wa : WeylGroup Tag.F4 := wordW Tag.F4 laF

@[expose] def wb : WeylGroup Tag.F4 := wordW Tag.F4 lbF

theorem wa_cube : wa ^ 3 = 1 := by
  have := laF_cube
  rw [wordW_append, wordW_append] at this
  simpa [wa, wordW, pow_succ, mul_assoc] using this

theorem wb_cube : wb ^ 3 = 1 := by
  have := lbF_cube
  rw [wordW_append, wordW_append] at this
  simpa [wb, wordW, pow_succ, mul_assoc] using this

theorem wa_wb_comm : wa * wb = wb * wa := by
  have := laF_lbF_comm
  rw [wordW_append, wordW_append] at this
  exact this

theorem wa_ne_one : wa ≠ 1 := fun h => by
  have := matrix_eq_of_wordW_eq Tag.F4 laF [] (by simpa [wa, wordW] using h)
  revert this
  decide +kernel

theorem wb_ne_one : wb ≠ 1 := fun h => by
  have := matrix_eq_of_wordW_eq Tag.F4 lbF [] (by simpa [wb, wordW] using h)
  revert this
  decide +kernel

theorem wb_ne_wa : wb ≠ wa := fun h => by
  have := matrix_eq_of_wordW_eq Tag.F4 lbF laF h
  revert this
  decide +kernel

theorem wb_ne_wa_sq : wb ≠ wa ^ 2 := fun h => by
  have h' : wordW Tag.F4 lbF = wordW Tag.F4 (laF ++ laF) := by
    rw [wordW_append]; simpa [wa, wb, sq] using h
  have := matrix_eq_of_wordW_eq Tag.F4 lbF (laF ++ laF) h'
  revert this
  decide +kernel

theorem zpow_mod_three_aux {G : Type*} [Group G] (g : G) (h3 : g ^ 3 = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g ∨ g ^ k = g ^ 2 := by
  have hg3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast h3
  have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h2 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hpow : g ^ k = g ^ (k % 3) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, hg3, one_zpow, one_mul]
  rw [hpow]
  obtain ⟨r, hr⟩ : ∃ r, r = k % 3 := ⟨_, rfl⟩
  rw [← hr] at h0 h2 ⊢
  interval_cases r
  · exact Or.inl (zpow_zero g)
  · exact Or.inr (Or.inl (zpow_one g))
  · exact Or.inr (Or.inr (by simpa using zpow_two g))

theorem zpowers_wa_cases {x : WeylGroup Tag.F4} (hx : x ∈ Subgroup.zpowers wa) :
    x = 1 ∨ x = wa ∨ x = wa ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact zpow_mod_three_aux wa wa_cube k

theorem wb_not_mem_zpowers : wb ∉ Subgroup.zpowers wa := fun h => by
  rcases zpowers_wa_cases h with h | h | h
  · exact wb_ne_one h
  · exact wb_ne_wa h
  · exact wb_ne_wa_sq h

@[expose] def QF4 : Subgroup (WeylGroup Tag.F4) := Subgroup.closure {wa, wb}

theorem QF4_comm : ∀ x ∈ QF4, ∀ y ∈ QF4, x * y = y * x :=
  pair_comm_of_closure wa wb wa_wb_comm

theorem QF4_cube : ∀ x ∈ QF4, x ^ 3 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => rcases hy with rfl | rfl; exact wa_cube; exact wb_cube
  | one => simp
  | mul a b ha hb ha3 hb3 =>
    rw [(show Commute a b from QF4_comm a ha b hb).mul_pow, ha3, hb3, one_mul]
  | inv a ha ha3 => simp [inv_pow, ha3]

theorem QF4_pGroup : IsPGroup 3 QF4 := fun x => ⟨1, by
  ext
  simpa using QF4_cube x x.2⟩

theorem finite_W : Finite (WeylGroup Tag.F4) :=
  Nat.finite_of_card_ne_zero (by rw [card_weylGroup_F4]; norm_num)

theorem QF4_card : Nat.card QF4 = 9 := by
  haveI := finite_W
  obtain ⟨k, hk⟩ := QF4_pGroup.exists_card_eq
  have hdvd : Nat.card QF4 ∣ 1152 := by
    rw [← card_weylGroup_F4]
    exact Subgroup.card_subgroup_dvd_card QF4
  have hwaQ : wa ∈ QF4 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hord : orderOf wa = 3 := orderOf_eq_prime wa_cube wa_ne_one
  have hz : Nat.card (Subgroup.zpowers wa) = 3 := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers wa ≤ QF4 := (Subgroup.zpowers_le).2 hwaQ
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h27 : 27 ∣ 1152 := by
      refine dvd_trans ?_ (hk ▸ hdvd)
      exact (show (27 : ℕ) = 3 ^ 3 by norm_num) ▸ pow_dvd_pow 3 h
    norm_num at h27
  have hk1 : 2 ≤ k := by
    by_contra h
    push Not at h
    have hle3 : Nat.card QF4 ≤ 3 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    have heq : Subgroup.zpowers wa = QF4 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hz]; exact hle3)
    exact wb_not_mem_zpowers (heq ▸ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl) :
      wb ∈ QF4))
  have : k = 2 := le_antisymm hk2 hk1
  rw [hk, this]
  norm_num

noncomputable def QF4Sylow : Sylow 3 (WeylGroup Tag.F4) :=
  haveI := finite_W
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard QF4 (by
    rw [QF4_card, card_weylGroup_F4, Nat.factorization_def _ Nat.prime_three]
    have : padicValNat 3 1152 = 2 := by
      rw [show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this]; norm_num)

theorem exists_conj_mem_QF4 (x : WeylGroup Tag.F4) (hx : x ^ 3 = 1) :
    ∃ w : WeylGroup Tag.F4, w * x * w⁻¹ ∈ QF4 := by
  haveI := finite_W
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    show (x ^ n) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.F4) QF4Sylow P
  have hxP : x ∈ (P : Subgroup (WeylGroup Tag.F4)) := hP' (Subgroup.mem_zpowers x)
  rw [← hg] at hxP
  refine ⟨g⁻¹, ?_⟩
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hxP
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hxP
  have hx' : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [inv_inv, hx']
  exact hs

theorem mem_QF4 {x : WeylGroup Tag.F4} (hx : x ∈ QF4) : ∃ i j : ℕ, x = wa ^ i * wb ^ j := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨i', j', rfl⟩ := hb
    refine ⟨i + i', j + j', ?_⟩
    have hc : Commute (wb ^ j) (wa ^ i') :=
      ((show Commute wa wb from wa_wb_comm).symm.pow_pow j i')
    calc wa ^ i * wb ^ j * (wa ^ i' * wb ^ j') = wa ^ i * (wb ^ j * wa ^ i') * wb ^ j' := by
          group
      _ = wa ^ i * (wa ^ i' * wb ^ j) * wb ^ j' := by rw [hc.eq]
      _ = _ := by rw [pow_add, pow_add]; group
  | inv a _ ha =>
    obtain ⟨i, j, rfl⟩ := ha
    refine ⟨2 * i, 2 * j, ?_⟩
    have hc : Commute (wa ^ i) (wb ^ j) := ((show Commute wa wb from wa_wb_comm).pow_pow i j)
    have h1 : (wa ^ i)⁻¹ = wa ^ (2 * i) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, wa_cube,
        one_pow]
    have h2 : (wb ^ j)⁻¹ = wb ^ (2 * j) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, wb_cube,
        one_pow]
    rw [mul_inv_rev, h1, h2]
    exact ((show Commute wa wb from wa_wb_comm).symm.pow_pow (2 * j) (2 * i)).eq

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
