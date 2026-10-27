module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMOrders
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

theorem exists_orderOf_four_psl2_of_seven {F : Type*} [Field F] (h7 : (7 : F) = 0) :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, orderOf x = 4 := by
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have : (1 : F) = 0 := by linear_combination h7 - 2 * h
    exact one_ne_zero this
  let M : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![3, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
  have hM2 : ((M ^ 2 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 3; -3, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals linear_combination h7
  have hM4 : ((M ^ 4 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 0; 0, -1] := by
    have : M ^ 4 = M ^ 2 * M ^ 2 := by group
    rw [this, Matrix.SpecialLinearGroup.coe_mul, hM2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals linear_combination -h7
  have hc4 : M ^ 4 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    rw [hM4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hc2 : M ^ 2 ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro h
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) hr
    simp only [hM2] at this
    simp at this
    exact h3 this.symm
  refine ⟨(QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), ?_⟩
  have h2 : ¬ (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 2 ^ 1 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using hc2
  have h4 : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 2 ^ (1 + 1) =
      1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using hc4
  simpa using orderOf_eq_prime_pow (p := 2) h2 h4

theorem exists_orderOf_four_catGroup_seven {q : TauCeti.PrimePower} (hq : q.card = 7)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    ∃ x : CatGroup ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩, orderOf x = 4 := by
  have hp7 : q.p = 7 := by
    have h1 : q.p ∣ 7 := by
      rw [← hq, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 h1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h7 : (7 : GaloisField q.p q.exponent) = 0 := by
    have : ((7 : ℕ) : GaloisField q.p q.exponent) = 0 := by
      rw [← hp7]
      exact CharP.cast_eq_zero _ _
    exact_mod_cast this
  obtain ⟨x, hx⟩ := exists_orderOf_four_psl2_of_seven h7
  exact ⟨(CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm x,
    by rw [MulEquiv.orderOf_eq]; exact hx⟩


theorem sixteen_dvd_card_unitary_three {q : TauCeti.PrimePower} (hq : q.card = 3)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩) := by
  rw [card_catGroup_twistedA (d := ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩) (r := 2) (q := q)
    rfl]
  have h3 : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq
  rw [h3]
  unfold CFSG.Open.ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, prod_toNat_icc_two_three 3 (by norm_num)]
  norm_num

theorem five_dvd_card_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    5 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h5 : 5 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  obtain ⟨k, hk⟩ := h2
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hk] at h5
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5

theorem false_of_alternating_of_not_five_dvd {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) (h5 : ¬ 5 ∣ Nat.card Y) {n : ℕ}
    (e : Y ≃* alternatingGroup (Fin n)) : False := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · have hsolv : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have : Group.IsSolvable Y :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
  · exact h5 ((Nat.card_congr e.toEquiv).symm ▸ five_dvd_card_alternatingGroup hn)

theorem primePower_p_eq_two {q : TauCeti.PrimePower} (h : q.card = 2) : q.p = 2 := by
  have h1 : q.p ∣ 2 := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1

theorem false_of_orthogonalTwo_of_not_dvd
    {Y : Type} [Group Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h5 : ¬ 5 ∣ Nat.card Y) (h16 : ¬ 16 ∣ Nat.card Y) (h : IsOrthogonalTwo Y) : False := by
  rcases h with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · have hp2 : q.p = 2 := primePower_p_eq_two hq
    have hcl : IsClassicalOrG2Index d.1 := by
      rcases hd with hd | hd | ⟨-, hd⟩ <;> rw [hd] <;> exact hp2
    rcases sixteen_dvd_card_or_l28 hcl with h16' | ⟨q', -, -, hA⟩
    · exact h16 (by rwa [Nat.card_congr e.toEquiv])
    · rcases hd with hd | hd | ⟨-, hd⟩ <;> rw [hd] at hA <;> cases hA
  · exact false_of_alternating_of_not_five_dvd hs hna h5 e

theorem isCaseTwoGroup_three_of_classical
    {Y : Type} [Group Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h5 : ¬ 5 ∣ Nat.card Y) (h16 : ¬ 16 ∣ Nat.card Y) (h4 : ∀ y : Y, orderOf y ≠ 4)
    (h : IsClassicalTwoOrG2 Y) : IsCaseTwoGroup 3 Y := by
  rcases h with ⟨d, hcl, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases sixteen_dvd_card_or_l28 hcl with h16' | ⟨q, hq2, hq3, hdq⟩
    · exact absurd (by rwa [Nat.card_congr e.toEquiv]) h16
    · exact ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hdq⟩, ⟨e⟩⟩
  · exact (false_of_alternating_of_not_five_dvd hs hna h5 e).elim
  · obtain ⟨x0, hv⟩ := d
    rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · obtain rfl : x0 = TauCeti.LieTypeIndex.A 1 q := hdq
      obtain ⟨x, hx⟩ := exists_orderOf_four_catGroup_seven hq hv
      exact (h4 (e.symm x) (by rw [MulEquiv.orderOf_eq]; exact hx)).elim
    · obtain rfl : x0 = TauCeti.LieTypeIndex.twistedA 2 q := hdq
      exact absurd (by rw [Nat.card_congr e.toEquiv]; exact sixteen_dvd_card_unitary_three hq hv)
        h16

end CFSG.AGLEmbedding
