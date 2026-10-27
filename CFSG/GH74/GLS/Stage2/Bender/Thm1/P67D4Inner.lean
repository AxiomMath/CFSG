module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Qplus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Phi36
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Normalizes
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeAssemble
public import CFSG.RankThree.PartOne.CTP.SeitzFineD4

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem prime_dvd_d4_order {q r : ℕ} (hq : 1 ≤ q) (hr : r.Prime) (hrq : ¬ r ∣ q)
    (h : r ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) :
    r ∣ q - 1 ∨ r ∣ q + 1 ∨ r ∣ q ^ 2 + q + 1 ∨ r ∣ q ^ 2 - q + 1 ∨ r ∣ q ^ 4 - q ^ 2 + 1 := by
  have h1 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : 1 ≤ q ^ 2 := le_trans hq h1
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e2 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hq, h3]; ring
  have e3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    zify [hq, h4]; ring
  have e3' : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [h1]; ring
  have e6 : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have := Nat.sq_sub_sq (q ^ 3) 1
    rw [← pow_mul] at this
    simpa [mul_comm] using this
  have e8 : q ^ 8 + q ^ 4 + 1 = (q ^ 2 + q + 1) * ((q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)) := by
    zify [h1, h2]; ring
  rw [e2, e6, e3, e3', e8] at h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact absurd (hr.dvd_of_dvd_pow h) hrq
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.CTP CFSG.RankThree.Chevalley

theorem d4_sigma_pow_order {p f : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    σ ^ TwistTag.D4.order = 1 := by
  have h3 : TwistTag.D4.order = 3 := rfl
  rw [h3]
  ext c
  have h := ringEquiv_cube_apply_eq hK hσ c
  simpa [pow_succ] using h

theorem d4_false_of_inner (hleaf : D4PlaneToral) {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hr : r.Prime) (hrodd : Odd r) (hrp : r ≠ p)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)]
    (hnab : ∃ a b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, a * b ≠ b * a)
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) r V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hchar : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  obtain ⟨E, hEe, hEc, hEV⟩ := exists_plane_of_inner hcen hVe hVc hinn
  have := hEe
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hrq : ¬ r ∣ p ^ f := fun h =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
  have hgen : Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    by_cases hr3 : r = 3
    · have hp3 : p ≠ 3 := fun h => hrp (hr3.trans h.symm)
      subst hr3
      by_cases hnorm : ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          IsPGroup p R ∧ R ≠ ⊥ ∧ E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K
            σ.toRingHom))
      · obtain ⟨R, hRp, hR1, hER⟩ := hnorm
        exact closure_centralizers_graphFixed_D4_of_normalizes hp hp3 hf K hK σ
          (d4_sigma_pow_order K hK σ hσ) E hEc R hRp hR1 hER
      · exact (d4_false_of_aniso hleaf hp hp2 hp3 hf K hK σ hσ h2 h3 E hEe hEc hEV
          fun R hRp hR1 hER => hnorm ⟨R, hRp, hR1, hER⟩).elim
    · have hr5 : 5 ≤ r := by
        have := hr.two_le
        have h2' : r ≠ 2 := by
          rintro rfl
          exact absurd hrodd (by decide)
        have h4 : r ≠ 4 := by
          rintro rfl
          exact absurd hr (by decide)
        omega
      have hrC : r ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
        refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
        rw [hEc]
        exact dvd_pow_self r two_ne_zero
      obtain ⟨hC1, -, -⟩ := triality_both_orientations_exact_finite_order p f hp hf K hK 1
        (Or.inl rfl) σ.toRingHom (by simpa using hσ)
      rw [hC1] at hrC
      rcases prime_dvd_d4_order hq1 hr hrq hrC with h | h | h | h | h
      ·
        exact closure_centralizers_graphFixed_D4_split p f hp hf K hK σ hσ
          (d4_sigma_pow_order K hK σ hσ) r hrp.symm hr5 h E hEc
      · exact (d4_false_of_qplus hp hf K hK σ hσ hr (by omega) h h2 h3 hinn).elim
      · exact (d4_false_of_phi36 hp hf K hK σ hσ hr hr5 (Or.inl h) h2 h3 hinn).elim
      · exact (d4_false_of_phi36 hp hf K hK σ hσ hr hr5 (Or.inr h) h2 h3 hinn).elim
      ·
        obtain ⟨T, -, -, hall⟩ := triality_cyclotomic_twelve_torus_and_prime_centralizers hp hf K
          hK σ hσ
        exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc
          ((hall r hr (by omega) h).2.1 E (IsElementaryAbelian.isPGroup r E))).elim
  have hgen' := iSup_fixSub_eq_top_of_closure hcen hgen
  rw [hEV] at hgen'
  exact false_of_generation inferInstance hnab h2 h3 hgen'

end CFSG.GH74.GLS.Stage2.Bender.Thm1
