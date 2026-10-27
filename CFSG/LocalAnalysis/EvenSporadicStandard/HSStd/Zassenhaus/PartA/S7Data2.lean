module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Data

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.s7_Vsub_ub_eq (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Vsub t a.ub = Vsub t a.u := by
  have htt := hb.t_mul_t
  rcases a.ub_cases with h | h
  · rw [h]
  · rw [h]
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [zpowers_le]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (mem_zpowers a.u))
    · refine sup_le le_sup_left ?_
      rw [zpowers_le]
      have h1 : a.u = t * (t * a.u) := by rw [← mul_assoc, htt, one_mul]
      have h2 : t * (t * a.u) ∈ zpowers t ⊔ zpowers (t * a.u) :=
        mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (mem_zpowers _))
      rwa [← h1] at h2

theorem PA5.s7_cent_cent_t_mem_V' (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G}
    (hgJ : g ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G)) (hgt : g * t = t * g) :
    g ∈ Vsub t a.ub := by
  rw [a.s7_Vsub_ub_eq hb]
  exact S5.cent_cent_t_mem_V hb a.toPA0 hgJ hgt

theorem PA5.s7_mem_F₀_of_sig (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8)
    {w : G} (hw2 : w * w = 1) (hwb : w * a.ub = a.ub * w)
    (hwJ : w ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G))
    (hwt : t * w * t⁻¹ = a.ub * w) : w ∈ a.F₀ := by
  have htt := hb.t_mul_t
  have hub2 := a.s7_ub_sq hb
  have hubt := a.s7_ub_t hb
  obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
  obtain ⟨-, -, hu₁J, -, hF₀, -, -⟩ := a.d8_props hd
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hvJ : a.u₁ * w ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) :=
    mul_mem hu₁J hwJ
  have hvt : (a.u₁ * w) * t = t * (a.u₁ * w) := by
    have e : t * (a.u₁ * w) * t⁻¹ = a.u₁ * w := by
      calc t * (a.u₁ * w) * t⁻¹ = (t * a.u₁ * t⁻¹) * (t * w * t⁻¹) := by group
        _ = (a.ub * a.u₁) * (a.ub * w) := by rw [ht1, hwt]
        _ = a.ub * (a.u₁ * a.ub) * w := by simp only [mul_assoc]
        _ = a.ub * (a.ub * a.u₁) * w := by rw [hc]
        _ = (a.ub * a.ub) * a.u₁ * w := by simp only [mul_assoc]
        _ = a.u₁ * w := by rw [hub2, one_mul]
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e.symm
  have hvV := a.s7_cent_cent_t_mem_V' hb hvJ hvt
  have hwv : w = a.u₁ * (a.u₁ * w) := by rw [← mul_assoc, hsq, one_mul]
  have hu₁F : a.u₁ ∈ a.F₀ := by rw [hF₀]; exact mem_sup_right (mem_zpowers _)
  have hubF := a.s7_ub_mem_F₀ hb
  rcases (S5.mem_V_iff htt hub2 hubt.symm).1 hvV with hv | hv | hv | hv
  · rw [hwv, hv, mul_one]; exact hu₁F
  · exfalso
    rw [hwv, hv] at hw2
    have e1 := a.s7_u₁_t_u₁ hb hd
    have : a.u₁ * t * (a.u₁ * t) = a.ub := by
      calc a.u₁ * t * (a.u₁ * t) = (a.u₁ * t * a.u₁) * t := by simp only [mul_assoc]
        _ = t * a.ub * t := by rw [e1]
        _ = (t * t) * a.ub := by rw [mul_assoc, hubt, ← mul_assoc]
        _ = a.ub := by rw [htt, one_mul]
    rw [this] at hw2
    exact a.s7_ub_ne_one hw2
  · rw [hwv, hv]; exact a.F₀.mul_mem hu₁F hubF
  · exfalso
    rw [hwv, hv] at hw2
    have e1 := a.s7_u₁_t_u₁ hb hd
    have h3 : a.u₁ * (t * a.ub) * (a.u₁ * (t * a.ub)) = a.ub := by
      calc a.u₁ * (t * a.ub) * (a.u₁ * (t * a.ub))
          = (a.u₁ * t) * (a.ub * a.u₁) * (t * a.ub) := by simp only [mul_assoc]
        _ = (a.u₁ * t) * (a.u₁ * a.ub) * (t * a.ub) := by rw [hc]
        _ = (a.u₁ * t * a.u₁) * (a.ub * (t * a.ub)) := by simp only [mul_assoc]
        _ = (t * a.ub) * (a.ub * (t * a.ub)) := by rw [e1]
        _ = t * (a.ub * a.ub) * (t * a.ub) := by simp only [mul_assoc]
        _ = t * (t * a.ub) := by rw [hub2, mul_one]
        _ = a.ub := by rw [← mul_assoc, htt, one_mul]
    rw [h3] at hw2
    exact a.s7_ub_ne_one hw2

theorem PA5.s7_Abar_conj_u₁ (hb : PAB G L t E W z) (a : PA5 L t E z) (hd : a.dcase = DCase.d8)
    {y : G} (hy : y ∈ a.Abar) : y * a.u₁ * y⁻¹ ∈ a.F₀ := by
  have hub2 := a.s7_ub_sq hb
  obtain ⟨hsq, hc, ht1, -, -⟩ := a.s7_d8_facts hb hd
  obtain ⟨-, -, hu₁J, -, -, -, -⟩ := a.d8_props hd
  have hyb : y * a.ub = a.ub * y := S5.ub_comm_Abar hb a.toPA0 a.ub_cases hy
  obtain ⟨hyt, -⟩ := S5.Abar_comm hb a.toPA0 hy
  have hybc : Commute y a.ub := hyb
  have hytc : Commute y t := hyt
  apply a.s7_mem_F₀_of_sig hb hd
  · calc y * a.u₁ * y⁻¹ * (y * a.u₁ * y⁻¹) = y * (a.u₁ * a.u₁) * y⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  · have h1 : Commute a.ub (y * a.u₁ * y⁻¹) :=
      ((hybc.symm.mul_right (show Commute a.ub a.u₁ from hc.symm)).mul_right hybc.symm.inv_right)
    exact h1.eq.symm
  · rw [mem_centralizer_iff]
    intro j hj
    have hj' : y⁻¹ * j * y ∈ derivedIn a.Abar := by
      obtain ⟨c, hc', rfl⟩ := hj
      have hyA : y⁻¹ ∈ a.Abar := a.Abar.inv_mem hy
      refine ⟨⟨y⁻¹, hyA⟩ * c * ⟨y⁻¹, hyA⟩⁻¹, ?_, ?_⟩
      · exact (inferInstance : (commutator ↥a.Abar).Normal).conj_mem c hc' ⟨y⁻¹, hyA⟩
      · simp
    have h1 := mem_centralizer_iff.1 hu₁J _ hj'
    calc j * (y * a.u₁ * y⁻¹) = y * ((y⁻¹ * j * y) * a.u₁) * y⁻¹ := by group
      _ = y * (a.u₁ * (y⁻¹ * j * y)) * y⁻¹ := by rw [h1]
      _ = (y * a.u₁ * y⁻¹) * j := by group
  · have e1 : t * y * t⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact hyt.symm
    have e2 : t * y⁻¹ * t⁻¹ = y⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]; exact hytc.inv_left.eq.symm
    calc t * (y * a.u₁ * y⁻¹) * t⁻¹
        = (t * y * t⁻¹) * (t * a.u₁ * t⁻¹) * (t * y⁻¹ * t⁻¹) := by group
      _ = y * (a.ub * a.u₁) * y⁻¹ := by rw [e1, e2, ht1]
      _ = (y * a.ub * y⁻¹) * (y * a.u₁ * y⁻¹) := by group
      _ = a.ub * (y * a.u₁ * y⁻¹) := by rw [hyb]; group

theorem PA5.s7_Abar_le_N₁ (hb : PAB G L t E W z) (a : PA5 L t E z) : a.Abar ≤ a.s7_N₁ := by
  intro x hx
  have hub2 := a.s7_ub_sq hb
  have hxub : x * a.ub = a.ub * x := S5.ub_comm_Abar hb a.toPA0 a.ub_cases hx
  refine (a.s7_mem_N₁).2 ⟨?_, hxub⟩
  have key : ∀ y ∈ a.Abar, ∀ f ∈ a.F₀, y * f * y⁻¹ ∈ a.F₀ := by
    intro y hy f hf
    have hyub : y * a.ub = a.ub * y := S5.ub_comm_Abar hb a.toPA0 a.ub_cases hy
    rcases (a.s7_mem_F₀_iff hb f).1 hf with h | h | ⟨hd, h | h⟩
    · rw [h]; simpa using one_mem _
    · rw [h]
      have : y * a.ub * y⁻¹ = a.ub := by rw [hyub]; group
      rw [this]; exact a.s7_ub_mem_F₀ hb
    · rw [h]; exact a.s7_Abar_conj_u₁ hb hd hy
    · have e : y * (a.ub * a.u₁) * y⁻¹ = a.ub * (y * a.u₁ * y⁻¹) := by
        calc y * (a.ub * a.u₁) * y⁻¹ = (y * a.ub * y⁻¹) * (y * a.u₁ * y⁻¹) := by group
          _ = a.ub * (y * a.u₁ * y⁻¹) := by rw [hyub]; group
      rw [h, e]
      exact a.F₀.mul_mem (a.s7_ub_mem_F₀ hb) (a.s7_Abar_conj_u₁ hb hd hy)
  intro f
  constructor
  · intro hf
    exact key x hx f hf
  · intro hf
    have := key x⁻¹ (a.Abar.inv_mem hx) _ hf
    simpa [mul_assoc] using this

theorem PA5.s7_J_le_N₁ (hb : PAB G L t E W z) (a : PA5 L t E z) : derivedIn a.Abar ≤ a.s7_N₁ :=
  (derivedIn_le _).trans (a.s7_Abar_le_N₁ hb)

theorem PA5.s7_odd_cent_F₀ (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G} (hg : g ∈ a.s7_N₁)
    (hodd : Odd (orderOf g)) : ∀ f ∈ a.F₀, g * f = f * g := by
  obtain ⟨hnorm, hgub⟩ := (a.s7_mem_N₁).1 hg
  have hub2 := a.s7_ub_sq hb
  have hsq : ∀ x : G, g * g * x = x * (g * g) → g * x = x * g := by
    intro x hx
    obtain ⟨m, hm⟩ := hodd
    have hpow : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
    have hg' : g = (g * g) ^ (m + 1) := by
      calc g = g ^ (2 * m + 2) := by
            calc g = g ^ (2 * m + 1) * g := by rw [hpow, one_mul]
              _ = g ^ (2 * m + 2) := by rw [← pow_succ]
        _ = (g * g) ^ (m + 1) := by rw [← pow_two, ← pow_mul]; rfl
    have hc : Commute (g * g) x := hx
    rw [hg']
    exact (hc.pow_left (m + 1)).eq
  have hD : a.dcase = DCase.d8 → g * a.u₁ = a.u₁ * g := by
    intro hd
    obtain ⟨hsq1, hc, ht1, hne1, hne2⟩ := a.s7_d8_facts hb hd
    have hu₁F : a.u₁ ∈ a.F₀ := by
      obtain ⟨-, -, -, -, hF₀, -, -⟩ := a.d8_props hd
      rw [hF₀]; exact mem_sup_right (mem_zpowers _)
    have hconj : g * a.u₁ * g⁻¹ ∈ a.F₀ := (hnorm a.u₁).1 hu₁F
    have hcg : g⁻¹ * a.ub * g = a.ub := by
      calc g⁻¹ * a.ub * g = g⁻¹ * (a.ub * g) := mul_assoc _ _ _
        _ = g⁻¹ * (g * a.ub) := by rw [hgub]
        _ = a.ub := inv_mul_cancel_left g a.ub
    apply hsq
    rcases (a.s7_mem_F₀_iff hb _).1 hconj with h' | h' | ⟨-, h' | h'⟩
    · exfalso
      apply hne1
      calc a.u₁ = g⁻¹ * (g * a.u₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    · exfalso
      apply hne2
      calc a.u₁ = g⁻¹ * (g * a.u₁ * g⁻¹) * g := by group
        _ = g⁻¹ * a.ub * g := by rw [h']
        _ = a.ub := hcg
    · rw [mul_inv_eq_iff_eq_mul] at h'
      calc g * g * a.u₁ = g * (g * a.u₁) := mul_assoc _ _ _
        _ = g * (a.u₁ * g) := by rw [h']
        _ = (g * a.u₁) * g := (mul_assoc _ _ _).symm
        _ = (a.u₁ * g) * g := by rw [h']
        _ = a.u₁ * (g * g) := mul_assoc _ _ _
    · have h2 : g * (a.ub * a.u₁) * g⁻¹ = a.u₁ := by
        calc g * (a.ub * a.u₁) * g⁻¹ = (g * a.ub * g⁻¹) * (g * a.u₁ * g⁻¹) := by group
          _ = a.ub * (a.ub * a.u₁) := by
            rw [h', show g * a.ub * g⁻¹ = a.ub by rw [hgub]; group]
          _ = a.u₁ := by rw [← mul_assoc, hub2, one_mul]
      have h3 : g * g * a.u₁ * (g * g)⁻¹ = a.u₁ := by
        calc g * g * a.u₁ * (g * g)⁻¹ = g * (g * a.u₁ * g⁻¹) * g⁻¹ := by group
          _ = g * (a.ub * a.u₁) * g⁻¹ := by rw [h']
          _ = a.u₁ := h2
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
  intro f hf
  rcases (a.s7_mem_F₀_iff hb f).1 hf with h | h | ⟨hd, h | h⟩
  · rw [h, mul_one, one_mul]
  · rw [h]; exact hgub
  · rw [h]; exact hD hd
  · rw [h]
    calc g * (a.ub * a.u₁) = (g * a.ub) * a.u₁ := (mul_assoc _ _ _).symm
      _ = (a.ub * g) * a.u₁ := by rw [hgub]
      _ = a.ub * (g * a.u₁) := mul_assoc _ _ _
      _ = a.ub * (a.u₁ * g) := by rw [hD hd]
      _ = (a.ub * a.u₁) * g := (mul_assoc _ _ _).symm

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
