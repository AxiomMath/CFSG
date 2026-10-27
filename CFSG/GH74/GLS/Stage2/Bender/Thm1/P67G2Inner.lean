module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2SplitThree
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Qplus

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem prime_dvd_g2_order {q r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ q)
    (h : r ∣ q ^ 6 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) * (q ^ 2 - q + 1)) :
    r ∣ q - 1 ∨ r ∣ q + 1 ∨ r ∣ q ^ 2 + q + 1 ∨ r ∣ q ^ 2 - q + 1 := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact absurd (hr.dvd_of_dvd_pow h) hrq
      · have h2 := hr.dvd_of_dvd_pow h
        have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
          have := Nat.sq_sub_sq q 1
          simpa using this
        rw [e] at h2
        rcases (Nat.Prime.dvd_mul hr).1 h2 with h3 | h3
        · exact Or.inr (Or.inl h3)
        · exact Or.inl h3
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial

theorem g2_no_plane_of_cyclotomic (K : Type) [Field K] [Finite K] (hKodd : Odd (Nat.card K))
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (h : r ∣ Nat.card K ^ 2 + Nat.card K + 1 ∨ r ∣ Nat.card K ^ 2 - Nat.card K + 1)
    (E : Subgroup (adjointGroup Tag.G2 K)) (hEe : CFSG.IsElementaryAbelian r E)
    (hEc : Nat.card E = r ^ 2) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have := hEe
  rcases h with h | h
  · obtain ⟨T, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K
      hKodd 1 (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) hr hr3 h
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc
      (hcyc E (IsElementaryAbelian.isPGroup r E))
  · have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
    obtain ⟨T, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K
      hKodd (-1) (Or.inl rfl) (Nat.card K ^ 2 - Nat.card K + 1)
      (by push_cast [Nat.cast_sub hle]; ring) hr hr3 h
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc
      (hcyc E (IsElementaryAbelian.isPGroup r E))

theorem g2_false_of_inner {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = p ^ f) (hr : r.Prime) (hrodd : Odd r)
    (hrp : r ≠ p) [IsSimpleGroup (adjointGroup Tag.G2 K)] (hnab : ∃ a b : adjointGroup Tag.G2 K,
      a * b ≠ b * a) {V Z : Subgroup (MulAut (adjointGroup Tag.G2 K))}
    (h2 : N2Cfg (adjointGroup Tag.G2 K) r V Z) (h3 : N3Full (adjointGroup Tag.G2 K) V Z)
    (hinn : ∀ v ∈ V, v ∈
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range) :
    False := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hcen : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  obtain ⟨E, hEe, hEc, hEV⟩ := exists_plane_of_inner hcen hVe hVc hinn
  have := hEe
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hrq : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
  have hgen : Subgroup.closure {k : adjointGroup Tag.G2 K | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} =
      ⊤ := by
    by_cases hr3 : r = 3
    · subst hr3
      by_cases h31 : 3 ∣ Nat.card K - 1
      · exact g2_closure_centralizers_three_split K h31 E hEc
      · have h32 : 3 ∣ Nat.card K + 1 := by
          have hK1 : 1 ≤ Nat.card K := Nat.card_pos
          omega
        exact (g2_false_of_qplus_three hp hp2 hf K hK h32 h2 h3 hinn).elim
    · have hr5 : 5 ≤ r := by
        have := hr.two_le
        have h2' : r ≠ 2 := by
          rintro rfl
          exact absurd hrodd (by decide)
        have h4 : r ≠ 4 := by
          rintro rfl
          exact absurd hr (by decide)
        omega
      have hrY : r ∣ Nat.card (adjointGroup Tag.G2 K) := by
        refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
        rw [hEc]
        exact dvd_pow_self r two_ne_zero
      obtain ⟨hY1, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
      rw [hY1] at hrY
      rcases prime_dvd_g2_order hr hrq hrY with h | h | h | h
      ·
        exact closure_centralizers_adjoint_G2_split K p r hrp.symm hr5 h E hEc
      · exact (g2_false_of_qplus hp hp2 hf K hK hr (by omega) h h2 h3 hinn).elim
      · exact (g2_no_plane_of_cyclotomic K hKodd hr (by omega) (Or.inl h) E hEe hEc).elim
      · exact (g2_no_plane_of_cyclotomic K hKodd hr (by omega) (Or.inr h) E hEe hEc).elim
  have hgen' := iSup_fixSub_eq_top_of_closure hcen hgen
  rw [hEV] at hgen'
  exact false_of_generation inferInstance hnab h2 h3 hgen'


end CFSG.GH74.GLS.Stage2.Bender.Thm1
