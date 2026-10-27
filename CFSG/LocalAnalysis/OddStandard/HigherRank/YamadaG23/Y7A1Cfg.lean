module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B0b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

structure Y7ACfg {G : Type} [Group G] (A C0 V : Subgroup G) (a₁ b₁ a₂ b₂ z t d : G) : Prop where
  cfg : Y6Cfg A C0 (zpowers (d * t)) a₁ b₁ a₂ b₂ z t (d * t)
  hV : V = closure {z, d}
  d_ord : orderOf d = 2

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

theorem y7a_t_sq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t * t = 1 := by
  have hpow := pow_orderOf_eq_one t
  rw [h.cfg.t_ord] at hpow
  simpa [pow_two] using hpow

theorem y7a_d_sq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : d * d = 1 := by
  have hpow := pow_orderOf_eq_one d
  rw [h.d_ord] at hpow
  simpa [pow_two] using hpow

theorem y7a_z_sq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : z * z = 1 := by
  simpa [pow_two] using h.cfg.rel.z_sq

theorem y7a_d_cent (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : ∀ a ∈ A, a * d = d * a := by
  intro a ha
  have hdC0 : d ∈ C0 := by
    have hd : d = (d * t) * t := by rw [mul_assoc, y7a_t_sq h, mul_one]
    rw [hd, h.cfg.hC0]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  exact y6_C0_comm h.cfg a ha d hdC0

theorem y7a_tdt (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t * d * t⁻¹ = z * d := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
  have hd : d = (d * t) * t := by rw [mul_assoc, y7a_t_sq h, mul_one]
  have htd : t * d = (d * t)⁻¹ := by
    calc t * d = t * ((d * t) * t) := congrArg (fun w => t * w) hd
      _ = t * (d * t) * t⁻¹ := by rw [ht]; group
      _ = (d * t)⁻¹ := h.cfg.t_inv
  have h1 : t * d * t⁻¹ = (d * t)⁻¹ * t := by rw [ht, htd]
  have hu4 : (d * t) ^ 4 = 1 := by simpa [h.cfg.u_ord] using pow_orderOf_eq_one (d * t)
  have hu3 : (d * t) ^ 3 = (d * t)⁻¹ := by
    have hh : (d * t) ^ 3 * (d * t) = 1 := by
      rw [← pow_succ]
      simpa using hu4
    exact (inv_eq_of_mul_eq_one_left hh).symm
  have h2 : (d * t)⁻¹ * t = z * d := by
    rw [← hu3]
    rw [show (d * t) ^ 3 = (d * t) ^ 2 * (d * t) by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]]
    rw [h.cfg.u_sq]
    rw [mul_assoc, show (d * t) * t = d by rw [mul_assoc, y7a_t_sq h, mul_one]]
  exact h1.trans h2

theorem y7a_z_mem_A (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : z ∈ A :=
  y6_z_mem_A h.cfg

theorem y7a_z_mem_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : z ∈ V := by
  rw [h.hV]
  exact Subgroup.subset_closure (by simp)

theorem y7a_d_mem_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : d ∈ V := by
  rw [h.hV]
  exact Subgroup.subset_closure (by simp)

theorem y7a_t_mem_C0 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t ∈ C0 :=
  y6_t_mem_C0 h.cfg

theorem y7a_V_le_C0 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : V ≤ C0 := by
  rw [h.hV, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    rw [h.cfg.hC0, ← h.cfg.u_sq]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  · rw [hx]
    have hd : d = (d * t) * t := by rw [mul_assoc, y7a_t_sq h, mul_one]
    rw [hd, h.cfg.hC0]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

private lemma y7a_zpowers_two_elems {x : G} (hx : x * x = 1) :
    ∀ y ∈ zpowers x, y = 1 ∨ y = x := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [h2, one_zpow, one_mul]

private lemma y7a_z_ne_d (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : z ≠ d := by
  intro hzd
  have hzt : t * z = z * t := (h.cfg.t_cent z (y7a_z_mem_A h)).symm
  have h1 : (z * t) ^ 2 = 1 := by
    rw [pow_two]
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [y7a_z_sq h, y7a_t_sq h, one_mul]
  have h2 : (d * t) ^ 2 = 1 := by rw [← hzd]; exact h1
  rw [h.cfg.u_sq] at h2
  exact h.cfg.z_ne h2

private lemma y7a_V_eq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    V = zpowers z ⊔ zpowers d := by
  have hset : ({z, d} : Set G) = {z} ∪ {d} := by
    rw [Set.singleton_union]
  rw [h.hV, Subgroup.zpowers_eq_closure z, Subgroup.zpowers_eq_closure d, hset,
    Subgroup.closure_union]

private lemma y7a_t_conj_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {v : G} (hv : v ∈ V) :
    t * v * t⁻¹ ∈ V := by
  rw [h.hV] at hv ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hv
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have hzt : t * z = z * t := (h.cfg.t_cent z (y7a_z_mem_A h)).symm
      have hz : t * z * t⁻¹ = z := by rw [hzt]; group
      rw [hz]
      exact Subgroup.subset_closure (by simp)
    · rw [hx]
      have hd : t * d * t⁻¹ = z * d := y7a_tdt h
      rw [hd]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · simp
  · intro x y _ _ ihx ihy
    rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x _ ih
    rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ih

private lemma y7a_t_mem_normalizer (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    t ∈ normalizer (V : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact y7a_t_conj_V h hv
  · intro hv
    have hthis : t * (t * v * t⁻¹) * t⁻¹ = v := by
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
      rw [htinv, show t * (t * v * t) * t = (t * t) * v * (t * t) by group,
        y7a_t_sq h]
      simp
    have hmem := y7a_t_conj_V h hv
    rw [hthis] at hmem
    exact hmem

private lemma y7a_C0_eq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    C0 = V ⊔ zpowers t := by
  apply le_antisymm
  · rw [h.cfg.hC0, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (y7a_d_mem_V h))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    · rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  · exact sup_le (y7a_V_le_C0 h) (Subgroup.zpowers_le.mpr (y7a_t_mem_C0 h))

private lemma y7a_C0_elems (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ c ∈ C0, c ∈ V ∨ ∃ v ∈ V, c = v * t := by
  intro c hc
  have htN : zpowers t ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr (y7a_t_mem_normalizer h)
  rw [y7a_C0_eq h, sup_comm] at hc
  obtain ⟨a, ha, v, hv, rfl⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_le_normalizer htN hc
  rcases y7a_zpowers_two_elems (y7a_t_sq h) a ha with ha1 | hat
  · left
    rw [ha1, one_mul]
    exact hv
  · right
    refine ⟨t * v * t⁻¹, y7a_t_conj_V h hv, ?_⟩
    rw [hat]
    group

theorem y7a_V_elems (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ v ∈ V, v = 1 ∨ v = z ∨ v = d ∨ v = z * d := by
  intro v hv
  rw [y7a_V_eq h] at hv
  exact CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_zpowers_two (y7a_z_sq h) (y7a_d_sq h)
    (y7a_d_cent h z (y7a_z_mem_A h)) hv

theorem y7a_card_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : Nat.card ↥V = 4 := by
  rw [y7a_V_eq h]
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers d, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute z d from y7a_d_cent h z (y7a_z_mem_A h)).zpow_zpow i j).eq
  have hprod := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
    (A := zpowers z) (B := zpowers d) hcomm
  have hz : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h.cfg.rel.z_sq h.cfg.z_ne]
  have hd : Nat.card ↥(zpowers d) = 2 := by
    rw [Nat.card_zpowers, h.d_ord]
  have hinf : zpowers z ⊓ zpowers d = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases y7a_zpowers_two_elems (y7a_z_sq h) x hx.1 with h1 | hzx
    · exact h1
    · rcases y7a_zpowers_two_elems (y7a_d_sq h) x hx.2 with h1 | hdx
      · exact h1
      · exact absurd (hzx.symm.trans hdx) (y7a_z_ne_d h)
  have h4 : Nat.card ↥(zpowers z ⊔ zpowers d) = 4 := by
    have hthis := hprod
    rw [hz, hd] at hthis
    rw [hinf, Subgroup.card_bot] at hthis
    omega
  exact h4

theorem y7a_A_inf_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : A ⊓ V = zpowers z := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ A ⊓ C0 := ⟨hx.1, y7a_V_le_C0 h hx.2⟩
    rwa [y6_A_inf_C0 h.cfg] at hx'
  · exact Subgroup.zpowers_le.mpr ⟨y7a_z_mem_A h, y7a_z_mem_V h⟩

theorem y7a_card_AV (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : Nat.card ↥(A ⊔ V) = 64 := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    y6_C0_comm h.cfg a ha b (y7a_V_le_C0 h hb)
  have hprod := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
    (A := A) (B := V) hcomm
  have hinf : Nat.card ↥(A ⊓ V) = 2 := by
    rw [y7a_A_inf_V h, Nat.card_zpowers, orderOf_eq_prime h.cfg.rel.z_sq h.cfg.z_ne]
  have h4 : Nat.card ↥(A ⊔ V) = 64 := by
    have hthis := hprod
    rw [h.cfg.card_A, y7a_card_V h, hinf] at hthis
    omega
  exact h4

theorem y7a_AV_elems (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ V, ∃ a ∈ A, ∃ v ∈ V, x = a * v := by
  intro x hx
  exact CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute
    (fun a ha b hb => y6_C0_comm h.cfg a ha b (y7a_V_le_C0 h hb)) hx

theorem y7a_C1_elems (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ C0, (∃ a ∈ A, ∃ v ∈ V, x = a * v) ∨ ∃ a ∈ A, ∃ v ∈ V, x = a * t * v := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := y6_C1_elems h.cfg x hx
  rcases y7a_C0_elems h c hc with hcV | ⟨v, hv, hcv⟩
  · exact Or.inl ⟨a, ha, c, hcV, rfl⟩
  · refine Or.inr ⟨a, ha, t * v * t⁻¹, y7a_t_conj_V h hv, ?_⟩
    rw [hcv]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
    calc a * (v * t) = a * v * t := by group
      _ = a * t * (t * v * t⁻¹) := by
            rw [show a * t * (t * v * t⁻¹) = a * (t * t) * v * t⁻¹ by group,
              y7a_t_sq h, htinv]
            group

theorem y7a_C1_le_N_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    A ⊔ C0 ≤ normalizer (V : Set G) := by
  apply sup_le
  · rw [Subgroup.le_set_normalizer_iff]
    intro a ha v hv
    rw [y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)]
    simpa [mul_assoc] using hv
  · rw [y7a_C0_eq h]
    apply sup_le
    · exact Subgroup.le_normalizer
    · exact Subgroup.zpowers_le.mpr (y7a_t_mem_normalizer h)

end CFSG.OddStandard.HigherRank.YamadaG23
