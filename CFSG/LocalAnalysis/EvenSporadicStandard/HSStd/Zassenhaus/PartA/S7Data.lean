module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S5

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def PA5.s7_N₁ (a : PA5 L t E z) : Subgroup G :=
  normalizer ((a.F₀ : Subgroup G) : Set G) ⊓ Cen a.ub

theorem PA5.s7_mem_N₁ (a : PA5 L t E z) {g : G} :
    g ∈ a.s7_N₁ ↔ (∀ f, f ∈ a.F₀ ↔ g * f * g⁻¹ ∈ a.F₀) ∧ g * a.ub = a.ub * g := by
  unfold PA5.s7_N₁
  rw [mem_inf, mem_Cen, mem_normalizer_iff]

theorem PA5.s7_ub_sq (hb : PAB G L t E W z) (a : PA5 L t E z) : a.ub * a.ub = 1 :=
  (S5.ub_sq hb a.toPA0 a.ub_cases).1

theorem PA5.s7_ub_t (hb : PAB G L t E W z) (a : PA5 L t E z) : a.ub * t = t * a.ub :=
  (S5.ub_sq hb a.toPA0 a.ub_cases).2

theorem PA5.s7_t_conj_ub (hb : PAB G L t E W z) (a : PA5 L t E z) : t * a.ub * t⁻¹ = a.ub := by
  rw [mul_inv_eq_iff_eq_mul]
  exact (a.s7_ub_t hb).symm

theorem PA5.s7_ub_ne_one (a : PA5 L t E z) : a.ub ≠ 1 := by
  obtain ⟨σ, hσ, hphi⟩ := a.ub_base
  exact S5.ub_ne_one a.toPA4 (hc := a.ub_cy) hσ hphi

theorem PA5.s7_mem_F₀_iff (hb : PAB G L t E W z) (a : PA5 L t E z) (f : G) :
    f ∈ a.F₀ ↔ f = 1 ∨ f = a.ub ∨ (a.dcase = DCase.d8 ∧ (f = a.u₁ ∨ f = a.ub * a.u₁)) := by
  have hub2 := a.s7_ub_sq hb
  cases hd : a.dcase
  ·
    obtain ⟨hu₁ord, hu₁Cub, -, -, hF₀, -, -⟩ := a.d8_props hd
    have hu₁sq : a.u₁ * a.u₁ = 1 := by
      have := pow_orderOf_eq_one a.u₁
      rwa [hu₁ord, pow_two] at this
    have hcomm : a.ub * a.u₁ = a.u₁ * a.ub := (mem_Cen.1 hu₁Cub).symm
    rw [hF₀, S5.mem_V_iff hub2 hu₁sq hcomm]
    simp
  ·
    obtain ⟨hF₀, -⟩ := a.F₀_e4 hd
    rw [hF₀]
    have h := S5.mem_V_iff (t := a.ub) (u := a.ub) hub2 hub2 rfl (y := f)
    rw [sup_idem] at h
    rw [h]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · left; rw [h, hub2]
    · rintro (h | h | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd h (by decide)

theorem PA5.s7_ub_mem_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) : a.ub ∈ a.F₀ :=
  (a.s7_mem_F₀_iff hb a.ub).2 (Or.inr (Or.inl rfl))

theorem PA5.s7_F₀_comm_ub (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ f ∈ a.F₀, f * a.ub = a.ub * f := by
  intro f hf
  rcases (a.s7_mem_F₀_iff hb f).1 hf with h | h | ⟨hd, h | h⟩
  · rw [h, one_mul, mul_one]
  · rw [h]
  · obtain ⟨-, hu₁Cub, -, -, -, -, -⟩ := a.d8_props hd
    rw [h]; exact mem_Cen.1 hu₁Cub
  · obtain ⟨-, hu₁Cub, -, -, -, -, -⟩ := a.d8_props hd
    have hcomm : a.u₁ * a.ub = a.ub * a.u₁ := mem_Cen.1 hu₁Cub
    rw [h]
    calc a.ub * a.u₁ * a.ub = a.ub * (a.u₁ * a.ub) := mul_assoc _ _ _
      _ = a.ub * (a.ub * a.u₁) := by rw [hcomm]

theorem PA5.s7_F₀_isPGroup (hb : PAB G L t E W z) (a : PA5 L t E z) : IsPGroup 2 ↥a.F₀ := by
  cases hd : a.dcase
  · refine IsPGroup.of_card (n := 2) ?_
    simpa using a.F₀_card hd
  · obtain ⟨hF₀, -⟩ := a.F₀_e4 hd
    refine IsPGroup.of_card (n := 1) ?_
    rw [hF₀, Nat.card_zpowers]
    have : orderOf a.ub = 2 := a.ub_ord
    simp [this]

theorem PA5.s7_card_F₀_le (hb : PAB G L t E W z) (a : PA5 L t E z) : Nat.card a.F₀ ≤ 4 := by
  cases hd : a.dcase
  · exact (a.F₀_card hd).le
  · obtain ⟨hF₀, -⟩ := a.F₀_e4 hd
    rw [hF₀, Nat.card_zpowers, a.ub_ord]
    norm_num

theorem PA5.s7_d8_facts (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8) :
    a.u₁ * a.u₁ = 1 ∧ a.u₁ * a.ub = a.ub * a.u₁ ∧ t * a.u₁ * t⁻¹ = a.ub * a.u₁ ∧
      a.u₁ ≠ 1 ∧ a.u₁ ≠ a.ub := by
  obtain ⟨hu₁ord, hu₁Cub, -, hu₁t, -, hnm, -⟩ := a.d8_props hd
  have hu₁sq : a.u₁ * a.u₁ = 1 := by
    have := pow_orderOf_eq_one a.u₁
    rwa [hu₁ord, pow_two] at this
  refine ⟨hu₁sq, mem_Cen.1 hu₁Cub, hu₁t, ?_, ?_⟩
  · intro h
    apply hnm
    rw [h]; exact one_mem _
  · intro h
    apply hnm
    rw [h]; exact mem_zpowers _

theorem PA5.s7_t_conj_ubu₁ (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8) :
    t * (a.ub * a.u₁) * t⁻¹ = a.u₁ := by
  obtain ⟨-, -, ht1, -, -⟩ := a.s7_d8_facts hb hd
  have hub2 := a.s7_ub_sq hb
  calc t * (a.ub * a.u₁) * t⁻¹ = (t * a.ub * t⁻¹) * (t * a.u₁ * t⁻¹) := by group
    _ = a.ub * (a.ub * a.u₁) := by rw [a.s7_t_conj_ub hb, ht1]
    _ = a.u₁ := by rw [← mul_assoc, hub2, one_mul]

theorem PA5.s7_u₁_t_u₁ (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8) :
    a.u₁ * t * a.u₁ = t * a.ub := by
  obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
  have hubt := a.s7_ub_t hb
  have h1 : t * a.u₁ = a.ub * a.u₁ * t := by
    have := ht1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  calc a.u₁ * t * a.u₁ = a.u₁ * (t * a.u₁) := by simp only [mul_assoc]
    _ = a.u₁ * (a.ub * a.u₁ * t) := by rw [h1]
    _ = (a.u₁ * a.ub) * a.u₁ * t := by simp only [mul_assoc]
    _ = (a.ub * a.u₁) * a.u₁ * t := by rw [hc]
    _ = a.ub * (a.u₁ * a.u₁) * t := by simp only [mul_assoc]
    _ = a.ub * t := by rw [hsq, mul_one]
    _ = t * a.ub := hubt

theorem PA5.s7_u₁_mem_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8) :
    a.u₁ ∈ a.F₀ := (a.s7_mem_F₀_iff hb a.u₁).2 (Or.inr (Or.inr ⟨hd, Or.inl rfl⟩))

theorem PA5.s7_ubu₁_mem_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8) :
    a.ub * a.u₁ ∈ a.F₀ := a.F₀.mul_mem (a.s7_ub_mem_F₀ hb) (a.s7_u₁_mem_F₀ hb hd)

theorem PA5.s7_t_conj_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ f, f ∈ a.F₀ ↔ t * f * t⁻¹ ∈ a.F₀ := by
  have htt := hb.t_mul_t
  have key : ∀ f ∈ a.F₀, t * f * t⁻¹ ∈ a.F₀ := by
    intro f hf
    rcases (a.s7_mem_F₀_iff hb f).1 hf with h | h | ⟨hd, h | h⟩
    · rw [h]; simpa using one_mem _
    · rw [h, a.s7_t_conj_ub hb]; exact a.s7_ub_mem_F₀ hb
    · obtain ⟨-, -, ht1, -, -⟩ := a.s7_d8_facts hb hd
      rw [h, ht1]; exact a.s7_ubu₁_mem_F₀ hb hd
    · rw [h, a.s7_t_conj_ubu₁ hb hd]; exact a.s7_u₁_mem_F₀ hb hd
  intro f
  constructor
  · exact key f
  · intro h
    have := key _ h
    have e : t * (t * f * t⁻¹) * t⁻¹ = f := by
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      calc t * (t * f * t⁻¹) * t⁻¹ = (t * t) * f * (t⁻¹ * t⁻¹) := by group
        _ = f := by
          rw [htt, ← mul_inv_rev, htt, inv_one]; group
    rwa [e] at this

theorem PA5.s7_t_mem_N₁ (hb : PAB G L t E W z) (a : PA5 L t E z) : t ∈ a.s7_N₁ :=
  (a.s7_mem_N₁).2 ⟨a.s7_t_conj_F₀ hb, (a.s7_ub_t hb).symm⟩

theorem PA5.s7_F₀_le_N₁ (hb : PAB G L t E W z) (a : PA5 L t E z) : a.F₀ ≤ a.s7_N₁ := by
  intro f hf
  refine (a.s7_mem_N₁).2 ⟨fun f' => ?_, (a.s7_F₀_comm_ub hb f hf)⟩
  constructor
  · intro h
    exact a.F₀.mul_mem (a.F₀.mul_mem hf h) (a.F₀.inv_mem hf)
  · intro h
    have := a.F₀.mul_mem (a.F₀.mul_mem (a.F₀.inv_mem hf) h) hf
    simpa [mul_assoc] using this

theorem PA5.s7_cent_F₀_t (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ f ∈ a.F₀, t * f * t⁻¹ = f → f ∈ zpowers a.ub := by
  intro f hf hft
  have hub1 := a.s7_ub_ne_one
  rcases (a.s7_mem_F₀_iff hb f).1 hf with h | h | ⟨hd, h | h⟩
  · rw [h]; exact one_mem _
  · rw [h]; exact mem_zpowers _
  · exfalso
    obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
    rw [h, ht1] at hft
    apply hub1
    have : a.ub * a.u₁ = 1 * a.u₁ := by rw [one_mul]; exact hft
    exact mul_right_cancel this
  · exfalso
    rw [h, a.s7_t_conj_ubu₁ hb hd] at hft
    apply hub1
    obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
    have : 1 * a.u₁ = a.ub * a.u₁ := by rw [one_mul]; exact hft
    exact (mul_right_cancel this).symm

theorem PA5.s7_t_not_mem_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) : t ∉ a.F₀ := by
  intro hmem
  have ht1 : t ≠ 1 := by
    intro h
    have := hb.t_ord
    rw [h, orderOf_one] at this
    omega
  have hnconj : ¬ IsConj t a.ub := a.ub_nconj
  rcases (a.s7_mem_F₀_iff hb t).1 hmem with h | h | ⟨hd, h | h⟩
  · exact ht1 h
  · exact hnconj (h ▸ IsConj.refl t)
  · obtain ⟨hsq, hc, ht1', -, -⟩ := a.s7_d8_facts hb hd
    have e : t * a.u₁ * t⁻¹ = a.u₁ := by
      calc t * a.u₁ * t⁻¹ = a.u₁ * a.u₁ * a.u₁⁻¹ := congrArg (fun x : G => x * a.u₁ * x⁻¹) h
        _ = a.u₁ := by group
    rw [ht1'] at e
    apply a.s7_ub_ne_one
    have : a.ub * a.u₁ = 1 * a.u₁ := by rw [one_mul]; exact e
    exact mul_right_cancel this
  · have e : t * a.u₁ * t⁻¹ = a.u₁ := by
      calc t * a.u₁ * t⁻¹ = (a.ub * a.u₁) * a.u₁ * (a.ub * a.u₁)⁻¹ :=
            congrArg (fun x : G => x * a.u₁ * x⁻¹) h
        _ = a.u₁ := by
          obtain ⟨hsq, hc, -, -, -⟩ := a.s7_d8_facts hb hd
          have hub2 := a.s7_ub_sq hb
          have hui : a.u₁⁻¹ = a.u₁ := inv_eq_of_mul_eq_one_right hsq
          have hubi : a.ub⁻¹ = a.ub := inv_eq_of_mul_eq_one_right hub2
          rw [mul_inv_rev, hui, hubi]
          calc a.ub * a.u₁ * a.u₁ * (a.u₁ * a.ub) = a.ub * (a.u₁ * a.u₁) * (a.u₁ * a.ub) := by
                simp only [mul_assoc]
            _ = a.ub * (a.u₁ * a.ub) := by rw [hsq, mul_one]
            _ = a.ub * (a.ub * a.u₁) := by rw [hc]
            _ = a.u₁ := by rw [← mul_assoc, hub2, one_mul]
    obtain ⟨hsq, hc, ht1', -, -⟩ := a.s7_d8_facts hb hd
    rw [ht1'] at e
    apply a.s7_ub_ne_one
    have : a.ub * a.u₁ = 1 * a.u₁ := by rw [one_mul]; exact e
    exact mul_right_cancel this

theorem PA5.s7_fusion_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) (g : G)
    (hg : g * t * g⁻¹ * t⁻¹ ∈ a.F₀) :
    ∃ w : G, w * t = t * w ∧ g * w⁻¹ ∈ a.F₀ ∧ (w = g ∨ (a.dcase = DCase.d8 ∧ w = a.u₁ * g)) := by
  have htt := hb.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hubt := a.s7_ub_t hb
  have hub2 := a.s7_ub_sq hb
  have hub1 := a.s7_ub_ne_one
  obtain ⟨f, hf⟩ : ∃ f, f = g * t * g⁻¹ * t⁻¹ := ⟨_, rfl⟩
  rw [← hf] at hg
  have hh : g * t * g⁻¹ = f * t := by rw [hf]; group
  have hfm : f * (t * f * t⁻¹) = 1 := by
    rw [hf]
    calc g * t * g⁻¹ * t⁻¹ * (t * (g * t * g⁻¹ * t⁻¹) * t⁻¹)
        = g * (t * t) * g⁻¹ * (t⁻¹ * t⁻¹) := by group
      _ = 1 := by rw [htt, ← mul_inv_rev, htt, inv_one]; group
  rcases (a.s7_mem_F₀_iff hb f).1 hg with h | h | ⟨hd, h | h⟩
  · refine ⟨g, ?_, ?_, Or.inl rfl⟩
    · rw [h, one_mul] at hh
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hh]
    · simp
  · cases hd : a.dcase
    · obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
      have hui : a.u₁⁻¹ = a.u₁ := inv_eq_of_mul_eq_one_right hsq
      refine ⟨a.u₁ * g, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
      · have e1 := a.s7_u₁_t_u₁ hb hd
        rw [h] at hh
        have e3 : (a.u₁ * g) * t * (a.u₁ * g)⁻¹ = a.u₁ * (g * t * g⁻¹) * a.u₁⁻¹ := by group
        have : (a.u₁ * g) * t * (a.u₁ * g)⁻¹ = t := by
          rw [e3, hh, hui]
          calc a.u₁ * (a.ub * t) * a.u₁ = (a.u₁ * a.ub) * t * a.u₁ := by simp only [mul_assoc]
            _ = (a.ub * a.u₁) * t * a.u₁ := by rw [hc]
            _ = a.ub * (a.u₁ * t * a.u₁) := by simp only [mul_assoc]
            _ = a.ub * (t * a.ub) := by rw [e1]
            _ = (a.ub * t) * a.ub := (mul_assoc _ _ _).symm
            _ = (t * a.ub) * a.ub := by rw [hubt]
            _ = t := by rw [mul_assoc, hub2, mul_one]
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      · have : g * (a.u₁ * g)⁻¹ = a.u₁⁻¹ := by group
        rw [this]
        exact a.F₀.inv_mem (a.s7_u₁_mem_F₀ hb hd)
    · exfalso
      obtain ⟨-, hnc⟩ := a.F₀_e4 hd
      apply hnc
      rw [h] at hh
      exact isConj_iff.2 ⟨g, by
        have : g * t * g⁻¹ = a.ub * t := hh
        rw [this]; exact hubt⟩
  · exfalso
    obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
    rw [h, ht1] at hfm
    apply hub1
    calc a.ub = a.ub * (a.u₁ * a.u₁) := by rw [hsq, mul_one]
      _ = (a.ub * a.u₁) * a.u₁ := (mul_assoc _ _ _).symm
      _ = (a.u₁ * a.ub) * a.u₁ := by rw [hc]
      _ = a.u₁ * (a.ub * a.u₁) := mul_assoc _ _ _
      _ = 1 := hfm
  · exfalso
    obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
    rw [h, a.s7_t_conj_ubu₁ hb hd] at hfm
    apply hub1
    calc a.ub = a.ub * (a.u₁ * a.u₁) := by rw [hsq, mul_one]
      _ = (a.ub * a.u₁) * a.u₁ := (mul_assoc _ _ _).symm
      _ = 1 := hfm

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
