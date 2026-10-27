module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC4
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC2

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.RankTwoShapes

namespace UTSylow

variable {X : Type} [Group X] (D : UTSylow X)

theorem e1_f1_ne : D.toX ⟨1, 0, 0⟩ * D.toX ⟨0, 1, 0⟩ ≠ D.toX ⟨0, 1, 0⟩ * D.toX ⟨1, 0, 0⟩ := by
  rw [← map_mul, ← map_mul]
  intro h
  exact absurd ((ut_mul_comm_iff _ _).mp (D.toX_injective h)) (by decide)

theorem E_comm {x y : X} (hx : x ∈ D.E) (hy : y ∈ D.E) : x * y = y * x := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  rw [← map_mul, ← map_mul, (ut_mul_comm_iff u w).mpr (by
    rw [mem_Eu.mp hu, mem_Eu.mp hw, mul_zero, mul_zero])]

theorem swap_z0 : D.swap.toX ⟨0, 0, 1⟩ = D.toX ⟨0, 0, 1⟩ := by
  rw [swap_toX]
  congr 1

theorem mem_E_or_F {x : X} (hx : x ∈ (D.T : Subgroup X)) (hx2 : x * x = 1) : x ∈ D.E ∨ x ∈ D.F := by
  obtain ⟨u, rfl⟩ := D.exists_toX hx
  rw [← map_mul, ← map_one D.toX] at hx2
  rcases (ut_mul_self_eq_one_iff u).mp (D.toX_injective hx2) with h | h
  · exact Or.inr (D.toX_mem_F_iff.mpr h)
  · exact Or.inl (D.toX_mem_E_iff.mpr h)

theorem conj_E_cases {m : X} (hm : m ∈ normalizer ((D.T : Subgroup X) : Set X)) :
    (∀ e ∈ D.E, m * e * m⁻¹ ∈ D.E) ∨ (∀ e ∈ D.E, m * e * m⁻¹ ∈ D.F) := by
  have hT : ∀ t ∈ (D.T : Subgroup X), m * t * m⁻¹ ∈ (D.T : Subgroup X) :=
    fun t ht => (mem_normalizer_iff.mp hm t).mp ht
  have he₁ : D.toX ⟨1, 0, 0⟩ ∈ D.E := D.toX_mem_E_iff.mpr rfl
  obtain ⟨w, hw⟩ := D.exists_toX (hT _ (D.E_le_T he₁))
  have hww : w * w = 1 := by
    apply D.toX_injective
    rw [map_mul, hw, map_one]
    calc m * D.toX ⟨1, 0, 0⟩ * m⁻¹ * (m * D.toX ⟨1, 0, 0⟩ * m⁻¹) =
        m * D.toX (⟨1, 0, 0⟩ * ⟨1, 0, 0⟩) * m⁻¹ := by rw [map_mul]; group
      _ = 1 := by
        rw [show (⟨1, 0, 0⟩ * ⟨1, 0, 0⟩ : UT3 F4c) = 1 by decide, map_one, mul_one,
          mul_inv_cancel]
  have hwZ : ¬ (w.a = 0 ∧ w.b = 0) := by
    rintro ⟨ha, hb⟩
    have hf₁ : m * D.toX ⟨0, 1, 0⟩ * m⁻¹ ∈ (D.T : Subgroup X) := hT _ (D.toX_mem _)
    obtain ⟨v, hv⟩ := D.exists_toX hf₁
    have hc : D.toX w * D.toX v = D.toX v * D.toX w := by
      rw [← map_mul, ← map_mul, (ut_mul_comm_iff w v).mpr (by rw [ha, hb, zero_mul, mul_zero])]
    rw [hw, hv] at hc
    apply D.e1_f1_ne
    calc D.toX ⟨1, 0, 0⟩ * D.toX ⟨0, 1, 0⟩ =
        m⁻¹ * ((m * D.toX ⟨1, 0, 0⟩ * m⁻¹) * (m * D.toX ⟨0, 1, 0⟩ * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * D.toX ⟨0, 1, 0⟩ * m⁻¹) * (m * D.toX ⟨1, 0, 0⟩ * m⁻¹)) * m := by rw [hc]
      _ = D.toX ⟨0, 1, 0⟩ * D.toX ⟨1, 0, 0⟩ := by group
  have hcomm : ∀ e ∈ D.E, ∃ x, D.toX x = m * e * m⁻¹ ∧ x * w = w * x := by
    intro e he
    obtain ⟨x, hx⟩ := D.exists_toX (hT e (D.E_le_T he))
    refine ⟨x, hx, D.toX_injective ?_⟩
    rw [map_mul, map_mul, hx, hw]
    calc m * e * m⁻¹ * (m * D.toX ⟨1, 0, 0⟩ * m⁻¹) = m * (e * D.toX ⟨1, 0, 0⟩) * m⁻¹ := by group
      _ = m * (D.toX ⟨1, 0, 0⟩ * e) * m⁻¹ := by rw [D.E_comm he he₁]
      _ = m * D.toX ⟨1, 0, 0⟩ * m⁻¹ * (m * e * m⁻¹) := by group
  rcases (ut_mul_self_eq_one_iff w).mp hww with ha | hb
  · have hb : w.b ≠ 0 := fun hb => hwZ ⟨ha, hb⟩
    refine Or.inr fun e he => ?_
    obtain ⟨x, hx, hxw⟩ := hcomm e he
    rw [← hx]
    exact D.toX_mem_F_iff.mpr (ut_a_eq_zero_of_comm_F ha hb hxw)
  · have ha : w.a ≠ 0 := fun ha => hwZ ⟨ha, hb⟩
    refine Or.inl fun e he => ?_
    obtain ⟨x, hx, hxw⟩ := hcomm e he
    rw [← hx]
    exact D.toX_mem_E_iff.mpr (ut_b_eq_zero_of_comm_E hb ha hxw)

theorem conj_F_mem_E {m : X} (hm : m ∈ normalizer ((D.T : Subgroup X) : Set X))
    (hEF : ∀ e ∈ D.E, m * e * m⁻¹ ∈ D.F) : ∀ f ∈ D.F, m * f * m⁻¹ ∈ D.E := by
  rcases D.swap.conj_E_cases hm with hF | hF
  · exfalso
    rw [swap_E] at hF
    have hT : m⁻¹ * D.toX ⟨1, 0, 0⟩ * m⁻¹⁻¹ ∈ (D.T : Subgroup X) :=
      (mem_normalizer_iff.mp (inv_mem hm) _).mp (D.toX_mem _)
    obtain ⟨u, hu⟩ := D.exists_toX hT
    have hsplit : D.toX u = D.toX ⟨u.a, 0, u.c + u.a * u.b⟩ * D.toX ⟨0, u.b, 0⟩ := by
      rw [← map_mul, UT3.mul_def]
      congr 1
      ext : 1
      · exact (add_zero _).symm
      · exact (zero_add _).symm
      · change u.c = u.c + u.a * u.b + 0 + u.a * u.b
        linear_combination (-(u.a * u.b)) * f4_two
    have hmem : m * D.toX u * m⁻¹ ∈ D.F := by
      rw [hsplit, show m * (D.toX ⟨u.a, 0, u.c + u.a * u.b⟩ * D.toX ⟨0, u.b, 0⟩) * m⁻¹ =
        (m * D.toX ⟨u.a, 0, u.c + u.a * u.b⟩ * m⁻¹) * (m * D.toX ⟨0, u.b, 0⟩ * m⁻¹) by group]
      exact mul_mem (hEF _ (D.toX_mem_E_iff.mpr rfl)) (hF _ (D.toX_mem_F_iff.mpr rfl))
    rw [hu, show m * (m⁻¹ * D.toX ⟨1, 0, 0⟩ * m⁻¹⁻¹) * m⁻¹ = D.toX ⟨1, 0, 0⟩ by group] at hmem
    exact absurd (D.toX_mem_F_iff.mp hmem) (by decide)
  · rw [swap_E, swap_F] at hF
    exact hF

variable [Finite X]

theorem conj_mem_E_of_normalizer_T {m : X} (hm : m ∈ normalizer ((D.T : Subgroup X) : Set X)) :
    ∀ e ∈ D.E, m * e * m⁻¹ ∈ D.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases D.conj_E_cases hm with h | hEF
  · exact h
  exfalso
  have hFE := D.conj_F_mem_E hm hEF
  have hpow : ∀ j : ℕ, ∀ e ∈ D.E, m ^ (2 * j + 1) * e * (m ^ (2 * j + 1))⁻¹ ∈ D.F := by
    intro j
    induction j with
    | zero =>
      intro e he
      rw [Nat.mul_zero, Nat.zero_add, pow_one]
      exact hEF e he
    | succ j ih =>
      intro e he
      have h := hEF _ (hFE _ (ih e he))
      rwa [show m * (m * (m ^ (2 * j + 1) * e * (m ^ (2 * j + 1))⁻¹) * m⁻¹) * m⁻¹ =
        m ^ (2 * (j + 1) + 1) * e * (m ^ (2 * (j + 1) + 1))⁻¹ by
          rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, pow_succ, pow_succ]
          group] at h
  obtain ⟨k, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  obtain ⟨j, rfl⟩ := hr
  have hm₂ : m ^ (2 * j + 1) ∈ (D.T : Subgroup X) := by
    have hP : IsPGroup 2 (zpowers (m ^ (2 * j + 1))) := IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one])
    have hN : m ^ (2 * j + 1) ∈ normalizer ((D.T : Subgroup X) : Set X) := pow_mem hm _
    have h := (hP.inf_normalizer_sylow D.T).le (mem_inf.mpr ⟨mem_zpowers _, hN⟩)
    exact (mem_inf.mp h).2
  have h1 := hpow j _ (D.toX_mem_E_iff.mpr (show (⟨1, 0, 0⟩ : UT3 F4c).b = 0 from rfl))
  obtain ⟨v, hv⟩ := D.exists_toX hm₂
  rw [← hv, ← map_inv, ← map_mul, ← map_mul, ut_conj] at h1
  exact absurd (D.toX_mem_F_iff.mp h1) (show ¬ ((1 : F4c) = 0) by decide)

theorem stronglyClosed_of_not_isAlperin (hF : ¬ IsAlperinSubgroup 2 (D.T : Subgroup X) D.F) :
    ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha g hg
  have hP : zpowers a ≤ (D.T : Subgroup X) := zpowers_le.mpr (D.E_le_T ha)
  have hPg : (zpowers a).map (MulAut.conj g⁻¹).toMonoidHom ≤ (D.T : Subgroup X) := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion D.T hP hPg
  rw [← hcg a (mem_zpowers a)]
  clear hcg
  induction hc with
  | one => simpa using ha
  | @step c n Q _ hQ _ hn ih =>
    rw [show (c * n)⁻¹ * a * (c * n) = n⁻¹ * (c⁻¹ * a * c) * n⁻¹⁻¹ by group]
    rcases D.eq_of_isAlperinSubgroup hQ with rfl | rfl | rfl
    · exact D.conj_mem_E_of_normalizer_T (inv_mem hn) _ ih
    · exact (mem_normalizer_iff.mp (inv_mem hn) _).mp ih
    · exact absurd hQ hF

theorem isConj_z0_of_isAlperin
    (hE : IsAlperinSubgroup 2 (D.T : Subgroup X) D.E)
    (hF : IsAlperinSubgroup 2 (D.T : Subgroup X) D.F) {u : X} (hu : orderOf u = 2) :
    IsConj (D.toX ⟨0, 0, 1⟩) u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X D.T Q
  have huQ : u ∈ ((g • D.T : Sylow 2 X) : Subgroup X) := hQ (mem_zpowers u)
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at huQ
  obtain ⟨t, ht, htu⟩ := huQ
  rw [MulAut.smul_def, MulAut.conj_apply] at htu
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by
    have h : t = g⁻¹ * u * g := by rw [← htu]; group
    rw [h, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2, mul_one,
      inv_mul_cancel]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel] at htu
    rw [← htu, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have key : ∀ n : X, n * D.toX ⟨0, 0, 1⟩ * n⁻¹ = t → IsConj (D.toX ⟨0, 0, 1⟩) u :=
    fun n hn => isConj_iff.mpr ⟨g * n, by rw [← htu, ← hn]; group⟩
  rcases D.mem_E_or_F ht ht2 with htE | htF
  · obtain ⟨n, -, hn⟩ := D.exists_conj_eq_of_isAlperin hE htE ht1
    exact key n hn
  · have hF' : IsAlperinSubgroup 2 (D.swap.T : Subgroup X) D.swap.E := by
      rw [swap_E]
      exact hF
    obtain ⟨n, -, hn⟩ := D.swap.exists_conj_eq_of_isAlperin hF' (by rw [swap_E]; exact htF) ht1
    rw [swap_z0] at hn
    exact key n hn

theorem stronglyClosed_E_or_F
    (hX : ∃ u v : X, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v) :
    (∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E) ∨
      (∀ a ∈ D.F, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.F) := by
  by_cases hF : IsAlperinSubgroup 2 (D.T : Subgroup X) D.F
  · by_cases hE : IsAlperinSubgroup 2 (D.T : Subgroup X) D.E
    · obtain ⟨u, v, hu, hv, huv⟩ := hX
      exact absurd ((D.isConj_z0_of_isAlperin hE hF hu).symm.trans
        (D.isConj_z0_of_isAlperin hE hF hv)) huv
    · right
      have h := D.swap.stronglyClosed_of_not_isAlperin (by rw [swap_F]; exact hE)
      rw [swap_E] at h
      exact h
  · exact Or.inl (D.stronglyClosed_of_not_isAlperin hF)

end UTSylow

end CFSG.ComponentClassification.GHarris.ThmC
