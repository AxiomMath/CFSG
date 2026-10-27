module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112MMat
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSL
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.ClassicalInvolution.PerfectCase.Basic
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

section Transport

variable {G H : Type} [Group G] [Group H]

theorem t112m_commutator_eq_top_of_mulEquiv (e : G ≃* H) (h : commutator G = ⊤) :
    commutator H = ⊤ := by
  have h1 := congrArg (Subgroup.map e.toMonoidHom) h
  rw [commutator, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
  rw [commutator]
  exact h1

theorem t112m_two_le_of_data_mulEquiv [Finite G] (e : G ≃* H)
    (h : ∃ (T : Subgroup H) (u v : H), T ≠ ⊥ ∧ IsPGroup 2 T ∧ u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧
      u * v = v * u ∧ v ∉ Subgroup.zpowers u ∧ u ∈ Subgroup.normalizer (T : Set H) ∧
      v ∈ Subgroup.normalizer (T : Set H)) :
    2 ≤ GLATwoLocalRank 3 G := by
  obtain ⟨T, u, v, hT, hT2, hu1, hu3, hv3, huv, hvu, huN, hvN⟩ := h
  have hN : ∀ w ∈ Subgroup.normalizer (T : Set H),
      e.symm w ∈ Subgroup.normalizer ((T.comap e.toMonoidHom : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro a
    show e a ∈ T ↔ e (e.symm w * a * (e.symm w)⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.1 hw (e a)
  refine t112m_two_le_twoLocalRank (T := T.comap e.toMonoidHom) (u := e.symm u) (v := e.symm v)
    ?_ (hT2.comap_of_injective e.toMonoidHom e.injective) ?_ ?_ ?_ ?_ ?_ (hN u huN) (hN v hvN)
  · intro hb
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have h1 : e.symm t ∈ T.comap e.toMonoidHom := by
      show e (e.symm t) ∈ T
      rw [MulEquiv.apply_symm_apply]
      exact ht
    rw [hb, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e t, h1, map_one]
  · intro h1
    apply hu1
    rw [← MulEquiv.apply_symm_apply e u, h1, map_one]
  · rw [← map_pow, hu3, map_one]
  · rw [← map_pow, hv3, map_one]
  · rw [← map_mul, huv, map_mul]
  · intro h1
    apply hvu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg e hk
    rwa [map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

end Transport

section Sylow

variable {K : Type} [Group K] [Finite K]

theorem t112m_sylow_SL (hq : CFSG.Open.IsQuasisimple K) (h : IsSLThreeExc K) (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  obtain ⟨F, hF, hfin, hq9, ⟨e⟩⟩ := h
  have hperf := t112m_commutator_eq_top_of_mulEquiv e hq.1
  have hZ : Nat.card (Subgroup.center ↥(StatedSL 3 F)) = 3 :=
    CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSL_three (by omega)
  have hcard : Nat.card ↥(StatedSL 3 F) =
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
    CFSG.SectionRank.OddCover.card_statedSL_three
  have h3 : (Nat.card ↥(StatedSL 3 F)).factorization 3 = 3 := by
    rw [hcard, Nat.mul_right_comm]
    exact t112m_factorization_SL hq9
  exact i112v_sylow_facts_of_mulEquiv e (t112m_sylow_of_perfect hperf le_rfl hZ h3) R

theorem t112m_card_statedSU_three {F : Type} [Field F] [Finite F] {q : ℕ}
    (hK : Nat.card F = q ^ 2) :
    Nat.card ↥(StatedSU 3 q F) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
  CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK

theorem t112m_sylow_SU (hq : CFSG.Open.IsQuasisimple K) (h : IsSUThreeExc K) (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  obtain ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩ := h
  have hperf := t112m_commutator_eq_top_of_mulEquiv e hq.1
  have hZ : Nat.card (Subgroup.center ↥(StatedSU 3 q F)) = 3 :=
    CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSU_three hFq (by omega)
  have h3 : (Nat.card ↥(StatedSU 3 q F)).factorization 3 = 3 := by
    rw [t112m_card_statedSU_three hFq]
    exact t112m_factorization_SU hq9
  exact i112v_sylow_facts_of_mulEquiv e (t112m_sylow_of_perfect hperf le_rfl hZ h3) R

end Sylow

section TwoLocal

theorem t112m_of_two_pow_mod_nine {n : ℕ} (h : 2 ^ n % 9 = 2 ∨ 2 ^ n % 9 = 5) :
    n % 2 = 1 ∧ n % 3 ≠ 0 := by
  have h6 : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [h6] at h
  interval_cases hn : n % 6 <;> simp at h <;> omega

theorem t112m_exists_cube_root_unit (F : Type) [Field F] [Finite F] (h : 3 ∣ Nat.card F - 1) :
    ∃ ω : Fˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root F h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  refine ⟨Units.mk0 ω hω0, Units.ext (by simp [hω3]), fun h1 => hω1 ?_⟩
  simpa using congrArg Units.val h1

variable {K : Type} [Group K] [Finite K]

theorem t112m_T10_18_3 (hq : CFSG.Open.IsQuasisimple K) (h : IsSLThreeExc K ∨ IsSUThreeExc K)
    (hw : GLATwoLocalRank 3 K = 1) : IsSUThreeTwoPow K := by
  rcases h with ⟨F, hF, hfin, hq9, ⟨e⟩⟩ | ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩
  · exfalso
    obtain ⟨ω, hω3, hω1⟩ := t112m_exists_cube_root_unit F (by omega)
    have h2 : 2 ≤ GLATwoLocalRank 3 K := by
      apply t112m_two_le_of_data_mulEquiv e
      by_cases hc : ringChar F = 2
      · have : CharP F 2 := ringChar.eq_iff.1 hc
        exact t112m_data_diag_two hω3 hω1
      · refine t112m_data_diag_odd hω3 hω1 (Ring.neg_one_ne_one_of_char_ne_two hc) ?_ ?_ ?_
        · exact t112mDiag_mem_SL (by rw [← pow_three', hω3])
        · exact t112mDiag_mem_SL (by rw [mul_one, ← pow_succ', hω3])
        · exact t112mDiag_mem_SL (by simp)
    omega
  · have hq2 : 2 ≤ q := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      by_contra hlt
      interval_cases q <;> simp at hFq <;> omega
    by_cases hqo : q % 2 = 1
    · exfalso
      obtain ⟨ω, hω3, hω1⟩ := t112m_exists_cube_root_unit F (by
        rw [hFq]
        have : q % 3 = 2 := by omega
        have h1 : 3 ∣ q + 1 := by omega
        obtain ⟨c, hc⟩ := h1
        have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
          have : 1 ≤ q := by omega
          zify [Nat.one_le_pow 2 q (by omega), this]
          ring
        rw [this, hc]
        exact Dvd.dvd.mul_left (Dvd.intro c rfl) _)
      have hωq : (ω : F) ^ q * ω = 1 := by
        obtain ⟨c, hc⟩ : 3 ∣ q + 1 := by omega
        have : (ω : F) ^ 3 = 1 := by simpa using congrArg Units.val hω3
        rw [← pow_succ, hc, pow_mul, this, one_pow]
      have hω2q : ((ω ^ 2 : Fˣ) : F) ^ q * ((ω ^ 2 : Fˣ) : F) = 1 := by
        rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm 2 q, pow_mul, ← mul_pow, hωq, one_pow]
      have hneg : (-1 : F) ^ q * (-1) = 1 := by
        rw [← pow_succ, Even.neg_one_pow ⟨(q + 1) / 2, by omega⟩]
      have hchar : ringChar F ≠ 2 := by
        intro hc
        have := Fintype.ofFinite F
        have h1 := (FiniteField.even_card_iff_char_two (F := F)).1 hc
        rw [← Nat.card_eq_fintype_card, hFq] at h1
        have : q ^ 2 % 2 = 1 := by
          rw [Nat.pow_mod, hqo]
        omega
      have hq0 : q ≠ 0 := by omega
      have h2 : 2 ≤ GLATwoLocalRank 3 K := by
        apply t112m_two_le_of_data_mulEquiv e
        refine t112m_data_diag_odd hω3 hω1 (Ring.neg_one_ne_one_of_char_ne_two hchar) ?_ ?_ ?_
        · exact t112mDiag_mem_SU hq0 (by rw [← pow_three', hω3]) hωq hωq hωq
        · exact t112mDiag_mem_SU hq0 (by rw [mul_one, ← pow_succ', hω3]) hωq hω2q (by simp)
        · exact t112mDiag_mem_SU hq0 (by simp) (by simpa using hneg) (by simpa using hneg)
            (by simp)
      omega
    ·
      have := Fintype.ofFinite F
      have hc2 : ringChar F = 2 := by
        rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hFq, Nat.pow_mod]
        have : q % 2 = 0 := by omega
        rw [this]
      obtain ⟨k, -, hk⟩ := FiniteField.card F (ringChar F)
      rw [hc2, ← Nat.card_eq_fintype_card, hFq] at hk
      have hqd : q ∣ 2 ^ (k : ℕ) := ⟨q, by rw [← hk, pow_two]⟩
      obtain ⟨n, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hqd
      obtain ⟨hn2, hn3⟩ := t112m_of_two_pow_mod_nine hq9
      have hn1 : 1 < n := by
        by_contra hle
        have hn : n = 1 := by omega
        subst hn
        have : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) F) :=
          CFSG.Quasithin.isSolvable_statedSU_one hFq
        exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq
          (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
      exact ⟨F, hF, hfin, n, hn2, hn1, hn3, hFq, ⟨e⟩⟩

end TwoLocal

end CFSG.HardMathSupport.Solomon.Coordinator
