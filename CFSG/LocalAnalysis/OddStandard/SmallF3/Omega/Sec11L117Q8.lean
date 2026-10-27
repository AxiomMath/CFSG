module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec11Q8 (G : Type) [Group G] (z : G) (Q : Subgroup G) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_mem : z ∈ Q
  card : Nat.card Q = 8
  el : IsElemAbelianMod z Q
  z_cent : ∀ q ∈ Q, q * z = z * q
  center : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c ∈ zpowers z

private theorem conj_eqOn_of_closure_pair {Q : Subgroup G} {s u a b : G}
    (hQ : Q = Subgroup.closure ({a, b} : Set G))
    (ha : s * a * s⁻¹ = u * a * u⁻¹) (hb : s * b * s⁻¹ = u * b * u⁻¹) :
    ∀ x ∈ Q, s * x * s⁻¹ = u * x * u⁻¹ := by
  let E : Subgroup G :=
    { carrier := {x | s * x * s⁻¹ = u * x * u⁻¹}
      one_mem' := by
        show s * 1 * s⁻¹ = u * 1 * u⁻¹
        group
      mul_mem' := by
        intro x y hx hy
        have hx' : s * x * s⁻¹ = u * x * u⁻¹ := hx
        have hy' : s * y * s⁻¹ = u * y * u⁻¹ := hy
        show s * (x * y) * s⁻¹ = u * (x * y) * u⁻¹
        calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
          _ = (u * x * u⁻¹) * (u * y * u⁻¹) := by rw [hx', hy']
          _ = u * (x * y) * u⁻¹ := by group
      inv_mem' := by
        intro x hx
        have hx' : s * x * s⁻¹ = u * x * u⁻¹ := hx
        show s * x⁻¹ * s⁻¹ = u * x⁻¹ * u⁻¹
        calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
          _ = (u * x * u⁻¹)⁻¹ := by rw [hx']
          _ = u * x⁻¹ * u⁻¹ := by group }
  have hsub : ({a, b} : Set G) ⊆ E := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hcl : Subgroup.closure ({a, b} : Set G) ≤ E := (Subgroup.closure_le E).mpr hsub
  intro x hx
  exact hcl (hQ ▸ hx)

private lemma isMulCommutative_of_card_dvd_eight {H : Subgroup G} (hdvd : Nat.card ↥H ∣ 8)
    (hlt : Nat.card ↥H < 8) : IsMulCommutative ↥H := by
  have hcases : Nat.card ↥H = 1 ∨ Nat.card ↥H = 2 ∨ Nat.card ↥H = 4 := by
    have hdvd' : Nat.card ↥H ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact hdvd
    obtain ⟨k, _hk3, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp hdvd'
    interval_cases k
    · left; rw [hk]; norm_num
    · right; left; rw [hk]; norm_num
    · right; right; rw [hk]; norm_num
    · exfalso; rw [hk] at hlt; norm_num at hlt
  rcases hcases with h1 | h2 | h4
  · haveI : IsCyclic ↥H := isCyclic_of_card_dvd_prime (p := 2) (by rw [h1]; norm_num)
    infer_instance
  · haveI : IsCyclic ↥H := isCyclic_of_prime_card (p := 2) h2
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)

theorem Sec11Q8.card_zpowers [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q) :
    Nat.card ↥(zpowers z) = 2 := by
  have h2 : z ^ 2 = 1 := by rw [pow_two]; exact h.z_sq
  rw [Nat.card_zpowers z, orderOf_eq_prime (p := 2) h2 h.z_ne]

theorem Sec11Q8.exists_not_mem [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q) :
    ∃ q ∈ Q, q ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have hle : Q ≤ zpowers z := fun q hq => hcon q hq
  have hcard := Subgroup.card_le_of_le hle
  rw [Sec11Q8.card_zpowers h, h.card] at hcard
  omega

theorem Sec11Q8.inner_of_trivial [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q) {g : G}
    (hn : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hg : ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ zpowers z) :
    ∃ k ∈ Q, ∀ q ∈ Q, g * q * g⁻¹ = k * q * k⁻¹ := by
  have hzmem : ∀ e : G, e ∈ zpowers z → e = 1 ∨ e = z := by
    intro e he
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [← hk]
    have h2 : z ^ (2 : ℤ) = 1 := by
      have h2' : z ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two, h.z_sq]
      exact h2'
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · left; rw [hk0]; exact zpow_zero z
    · right; rw [hk1]; exact zpow_one z
  obtain ⟨q1, hq1Q, hq1Z⟩ := Sec11Q8.exists_not_mem h
  have hnotc : ¬ ∀ q ∈ Q, q1 * q = q * q1 := fun hc => hq1Z (h.center q1 hq1Q hc)
  push Not at hnotc
  obtain ⟨q2, hq2Q, hq2c⟩ := hnotc
  have hc_mem : q1 * q2 * q1⁻¹ * q2⁻¹ ∈ zpowers z := (h.el q1 hq1Q q2 hq2Q).1
  have hc_eq : q1 * q2 * q1⁻¹ * q2⁻¹ = z := by
    rcases hzmem _ hc_mem with hc1 | hcz
    · exfalso
      apply hq2c
      calc q1 * q2 = (q1 * q2 * q1⁻¹ * q2⁻¹) * (q2 * q1) := by group
        _ = 1 * (q2 * q1) := by rw [hc1]
        _ = q2 * q1 := by simp
    · exact hcz
  have hab : q1 * q2 = z * q2 * q1 := by
    calc q1 * q2 = (q1 * q2 * q1⁻¹ * q2⁻¹) * (q2 * q1) := by group
      _ = z * (q2 * q1) := by rw [hc_eq]
      _ = z * q2 * q1 := by group
  have h1 : z * (q1 * q2) = q2 * q1 := by
    calc z * (q1 * q2) = z * (z * (q2 * q1)) := by rw [hab]; group
      _ = (z * z) * (q2 * q1) := by group
      _ = q2 * q1 := by rw [h.z_sq]; group
  have hba : q2 * q1 = z * q1 * q2 := by rw [← h1]; group
  have hab_a : q1 * q2 * q1⁻¹ = z * q2 := by rw [hab]; group
  have hba_b : q2 * q1 * q2⁻¹ = z * q1 := by rw [hba]; group
  have hba_a : (q2 * q1) * q1 * (q2 * q1)⁻¹ = z * q1 := by
    calc (q2 * q1) * q1 * (q2 * q1)⁻¹ = q2 * q1 * q2⁻¹ := by group
      _ = z * q1 := hba_b
  have hba_b' : (q2 * q1) * q2 * (q2 * q1)⁻¹ = z * q2 := by
    calc (q2 * q1) * q2 * (q2 * q1)⁻¹ = q2 * (q1 * q2 * q1⁻¹) * q2⁻¹ := by group
      _ = q2 * (z * q2) * q2⁻¹ := by rw [hab_a]
      _ = (q2 * z) * (q2 * q2⁻¹) := by group
      _ = q2 * z := by group
      _ = z * q2 := h.z_cent q2 hq2Q
  have hle_ab : Subgroup.closure ({q1, q2} : Set G) ≤ Q := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hq1Q
    · exact hq2Q
  have hQ : Q = Subgroup.closure ({q1, q2} : Set G) := by
    by_contra hne
    have hlt : Subgroup.closure ({q1, q2} : Set G) < Q :=
      lt_of_le_of_ne hle_ab (Ne.symm hne)
    have hdvd : Nat.card ↥(Subgroup.closure ({q1, q2} : Set G)) ∣ 8 := by
      have hh := Subgroup.card_dvd_of_le hle_ab
      rwa [h.card] at hh
    have hlt8 : Nat.card ↥(Subgroup.closure ({q1, q2} : Set G)) < 8 := by
      have hh := Subgroup.card_lt_of_lt hlt
      rwa [h.card] at hh
    have hcomm : IsMulCommutative ↥(Subgroup.closure ({q1, q2} : Set G)) :=
      isMulCommutative_of_card_dvd_eight hdvd hlt8
    have hq1H : q1 ∈ Subgroup.closure ({q1, q2} : Set G) := Subgroup.subset_closure (by simp)
    have hq2H : q2 ∈ Subgroup.closure ({q1, q2} : Set G) := Subgroup.subset_closure (by simp)
    exact hq2c
      (congrArg Subtype.val (isMulCommutative_iff.mp hcomm ⟨q1, hq1H⟩ ⟨q2, hq2H⟩))
  have hsa : g * q1 * g⁻¹ = (g * q1 * g⁻¹ * q1⁻¹) * q1 := by group
  have hsb : g * q2 * g⁻¹ = (g * q2 * g⁻¹ * q2⁻¹) * q2 := by group
  have hca : g * q1 * g⁻¹ * q1⁻¹ ∈ zpowers z := hg q1 hq1Q
  have hcb : g * q2 * g⁻¹ * q2⁻¹ ∈ zpowers z := hg q2 hq2Q
  rcases hzmem _ hca with hca1 | hcaz
  · rcases hzmem _ hcb with hcb1 | hcbz
    · refine ⟨1, Q.one_mem, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q) hQ ?_ ?_
      · rw [hsa, hca1]; group
      · rw [hsb, hcb1]; group
    · refine ⟨q1, hq1Q, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q) hQ ?_ ?_
      · rw [hsa, hca1]; group
      · rw [hsb, hcbz, hab_a]
  · rcases hzmem _ hcb with hcb1 | hcbz
    · refine ⟨q2, hq2Q, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q) hQ ?_ ?_
      · rw [hsa, hcaz, hba_b]
      · rw [hsb, hcb1]; group
    · refine ⟨q2 * q1, mul_mem hq2Q hq1Q, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q) hQ ?_ ?_
      · rw [hsa, hcaz, hba_a]
      · rw [hsb, hcbz, hba_b']

end CFSG.OddStandard.SmallF3.Omega
