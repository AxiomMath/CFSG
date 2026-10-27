module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Transv
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

@[expose] def cyc_l : GL32 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide +kernel,
    by decide +kernel⟩

theorem cyc_act_l (x : V3) : act cyc_l x = ![x 2, x 0, x 1] := by
  revert x
  decide +kernel

theorem cyc_l_pow_three : cyc_l ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one]
  exact Units.ext (by decide +kernel)

theorem cyc_l_ne_one : cyc_l ≠ 1 := fun h =>
  absurd (congrArg Units.val h) (by decide +kernel)

theorem cyc_orderOf_l : orderOf cyc_l = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime cyc_l_pow_three cyc_l_ne_one

theorem cyc_conj_l₀ {d : GL32} (hd : orderOf d = 3) :
    ∃ g : GL32, g * d * g⁻¹ = L32Insp.l₀ := by
  have hd3 : d ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd] at this
  obtain ⟨g, hg⟩ := L32Insp.exists_conj_mem_zpowers hd3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [zpow_eq_zpow_emod' k L32Insp.l₀_pow_three] at hk
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk
    exfalso
    have h1 : d = 1 := by
      have e : d = g⁻¹ * (g * d * g⁻¹) * g := by group
      rw [e, ← hk]
      group
    rw [h1, orderOf_one] at hd
    omega
  · exact ⟨g, by rw [← hk, h1, zpow_one]⟩
  · refine ⟨L32Insp.tL⁻¹ * g, ?_⟩
    have e1 : g * d * g⁻¹ = L32Insp.l₀⁻¹ := by
      rw [← hk, h2, zpow_ofNat]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact L32Insp.l₀_pow_three
    calc (L32Insp.tL⁻¹ * g) * d * (L32Insp.tL⁻¹ * g)⁻¹
        = L32Insp.tL⁻¹ * (g * d * g⁻¹) * L32Insp.tL := by group
      _ = L32Insp.tL⁻¹ * L32Insp.l₀⁻¹ * L32Insp.tL := by rw [e1]
      _ = L32Insp.tL⁻¹ * (L32Insp.tL * L32Insp.l₀ * L32Insp.tL⁻¹) * L32Insp.tL := by
        rw [L32Insp.tL_conj_l₀]
      _ = L32Insp.l₀ := by group

theorem cyc_conj_l {d : GL32} (hd : orderOf d = 3) : ∃ g : GL32, g * d * g⁻¹ = cyc_l := by
  obtain ⟨g₁, h₁⟩ := cyc_conj_l₀ hd
  obtain ⟨g₂, h₂⟩ := cyc_conj_l₀ cyc_orderOf_l
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  calc g₂⁻¹ * g₁ * d * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * d * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₂ * cyc_l * g₂⁻¹) * g₂ := by rw [h₁, h₂]
    _ = cyc_l := by group

theorem cyc_act_inj (g : GL32) {x y : V3} : act g x = act g y ↔ x = y := by
  constructor
  · intro h
    have := congrArg (act g⁻¹) h
    rwa [act_inv_act, act_inv_act] at this
  · rintro rfl
    rfl

theorem cyc_act_ne_zero (g : GL32) {x : V3} (hx : x ≠ 0) : act g x ≠ 0 :=
  fun h => hx ((act_eq_zero_iff g x).1 h)

theorem cyc_comm {g d : GL32} (hg : g * d * g⁻¹ = cyc_l) (x : V3) :
    act cyc_l (act g x) = act g (act d x) := by
  rw [← hg, act_mul, act_mul, act_inv_act]

theorem cyc_act_d {g d : GL32} (hg : g * d * g⁻¹ = cyc_l) (x : V3) :
    act d x = act g⁻¹ (act cyc_l (act g x)) := by
  rw [cyc_comm hg, act_inv_act]

theorem cyc_mem_line_iff (g : GL32) (z x y : V3) :
    act g z ∈ ({act g x, act g y, act g x + act g y} : Finset V3) ↔
      z ∈ ({x, y, x + y} : Finset V3) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, ← act_add, cyc_act_inj]

@[expose] def cyc_p₀ : V3 := ![1, 1, 0]

@[expose] def cyc_q₀ : V3 := ![0, 1, 1]

theorem cyc_p₀_ne : cyc_p₀ ≠ 0 := by decide +kernel

theorem cyc_q₀_ne : cyc_q₀ ≠ 0 := by decide +kernel

theorem cyc_pq_ne : cyc_p₀ ≠ cyc_q₀ := by decide +kernel

theorem cyc_l_p₀ : act cyc_l cyc_p₀ = cyc_q₀ := by
  rw [cyc_act_l]
  decide +kernel

theorem cyc_l_q₀ : act cyc_l cyc_q₀ = cyc_p₀ + cyc_q₀ := by
  rw [cyc_act_l]
  decide +kernel

theorem cyc_l_fixed_unique : ∀ p q : V3,
    p ≠ 0 ∧ q ≠ 0 ∧ ![p 2, p 0, p 1] = p ∧ ![q 2, q 0, q 1] = q → p = q := by
  decide +kernel

theorem cyc_l_fixed_avoid : ∀ r : V3,
    r ≠ 0 ∧ ![r 2, r 0, r 1] = r → r ≠ cyc_p₀ ∧ r ≠ cyc_q₀ ∧ r ≠ cyc_p₀ + cyc_q₀ := by
  decide +kernel

theorem cyc_l_line : ∀ x y : V3, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧
    ![x 2, x 0, x 1] ∈ ({x, y, x + y} : Finset V3) ∧
    ![y 2, y 0, y 1] ∈ ({x, y, x + y} : Finset V3) →
    ({x, y, x + y} : Finset V3) = {cyc_p₀, cyc_q₀, cyc_p₀ + cyc_q₀} := by
  decide +kernel

theorem cyc_perp_p : cyc_p₀ ⬝ᵥ cyc_p₀ = 0 := by decide +kernel

theorem cyc_perp_q : cyc_q₀ ⬝ᵥ cyc_q₀ = 0 := by decide +kernel

theorem cyc_l_eq : cyc_l =
    tvGL cyc_p₀ cyc_p₀ cyc_perp_p * tvGL cyc_q₀ cyc_q₀ cyc_perp_q := by
  apply GL32_ext
  intro x
  rw [act_mul, act_tvGL, act_tvGL, cyc_act_l]
  revert x
  decide +kernel

theorem order3_fixed_unique {d : GL32} (hd : orderOf d = 3) {p q : V3} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdp : act d p = p) (hdq : act d q = q) : p = q := by
  obtain ⟨g, hg⟩ := cyc_conj_l hd
  have h1 : act cyc_l (act g p) = act g p := by rw [cyc_comm hg, hdp]
  have h2 : act cyc_l (act g q) = act g q := by rw [cyc_comm hg, hdq]
  rw [cyc_act_l] at h1 h2
  exact (cyc_act_inj g).1
    (cyc_l_fixed_unique _ _ ⟨cyc_act_ne_zero g hp, cyc_act_ne_zero g hq, h1, h2⟩)

theorem order3_exists_invariant_pair {d : GL32} (hd : orderOf d = 3) :
    ∃ p q : V3, p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ d ∈ Spt p ⊔ Spt q ∧
      act d p ∈ ({p, q, p + q} : Finset V3) ∧ act d q ∈ ({p, q, p + q} : Finset V3) ∧
      ∀ r : V3, r ≠ 0 → act d r = r → r ≠ p ∧ r ≠ q ∧ r ≠ p + q := by
  obtain ⟨g, hg⟩ := cyc_conj_l hd
  have hd' : d = g⁻¹ * cyc_l * g := by rw [← hg]; group
  refine ⟨act g⁻¹ cyc_p₀, act g⁻¹ cyc_q₀, cyc_act_ne_zero _ cyc_p₀_ne,
    cyc_act_ne_zero _ cyc_q₀_ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact cyc_pq_ne ((cyc_act_inj g⁻¹).1 h)
  · have e : d = (g⁻¹ * tvGL cyc_p₀ cyc_p₀ cyc_perp_p * g⁻¹⁻¹) *
        (g⁻¹ * tvGL cyc_q₀ cyc_q₀ cyc_perp_q * g⁻¹⁻¹) := by
      rw [hd', cyc_l_eq]
      group
    rw [e]
    exact Subgroup.mul_mem_sup (tv_conj_mem_Spt (tv_tvGL_mem_Spt _ _ _))
      (tv_conj_mem_Spt (tv_tvGL_mem_Spt _ _ _))
  · rw [cyc_act_d hg, act_act_inv, cyc_l_p₀]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · rw [cyc_act_d hg, act_act_inv, cyc_l_q₀, act_add]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · intro r hr hdr
    have h1 : act cyc_l (act g r) = act g r := by rw [cyc_comm hg, hdr]
    rw [cyc_act_l] at h1
    obtain ⟨a, b, c⟩ := cyc_l_fixed_avoid (act g r) ⟨cyc_act_ne_zero g hr, h1⟩
    refine ⟨fun h => a ?_, fun h => b ?_, fun h => c ?_⟩
    · rw [h, act_act_inv]
    · rw [h, act_act_inv]
    · rw [h, act_add, act_act_inv, act_act_inv]

theorem order3_invariant_triple_unique {d : GL32} (hd : orderOf d = 3) {x y p q : V3}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h1 : act d x ∈ ({x, y, x + y} : Finset V3)) (h2 : act d y ∈ ({x, y, x + y} : Finset V3))
    (h3 : act d p ∈ ({p, q, p + q} : Finset V3)) (h4 : act d q ∈ ({p, q, p + q} : Finset V3)) :
    ({x, y, x + y} : Finset V3) = {p, q, p + q} := by
  obtain ⟨g, hg⟩ := cyc_conj_l hd
  have key : ∀ {x y : V3}, x ≠ 0 → y ≠ 0 → x ≠ y → act d x ∈ ({x, y, x + y} : Finset V3) →
      act d y ∈ ({x, y, x + y} : Finset V3) → ∀ z : V3, z ∈ ({x, y, x + y} : Finset V3) ↔
        act g z ∈ ({cyc_p₀, cyc_q₀, cyc_p₀ + cyc_q₀} : Finset V3) := by
    intro x y hx hy hxy h1 h2 z
    have h1' : ![(act g x) 2, (act g x) 0, (act g x) 1] ∈
        ({act g x, act g y, act g x + act g y} : Finset V3) := by
      rw [← cyc_act_l, cyc_comm hg]
      exact (cyc_mem_line_iff g _ x y).2 h1
    have h2' : ![(act g y) 2, (act g y) 0, (act g y) 1] ∈
        ({act g x, act g y, act g x + act g y} : Finset V3) := by
      rw [← cyc_act_l, cyc_comm hg]
      exact (cyc_mem_line_iff g _ x y).2 h2
    have hl := cyc_l_line (act g x) (act g y)
      ⟨cyc_act_ne_zero g hx, cyc_act_ne_zero g hy, fun h => hxy ((cyc_act_inj g).1 h), h1', h2'⟩
    rw [← cyc_mem_line_iff g z x y, hl]
  ext z
  rw [key hx hy hxy h1 h2 z, key hp hq hpq h3 h4 z]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
