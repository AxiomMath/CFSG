module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoB
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwo

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

omit [Finite X] in
private theorem comm_of_mem_closure' {s : Set X} (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    {x y : X} (hx : x ∈ closure s) (hy : y ∈ closure s) : x * y = y * x := by
  have h1 : ∀ a ∈ s, ∀ y ∈ closure s, Commute a y := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | one => exact Commute.one_right a
    | mul b c _ _ hb hc => exact hb.mul_right hc
    | inv b _ hb => exact hb.inv_right
  have h2 : Commute x y := by
    induction hx using Subgroup.closure_induction with
    | mem a ha => exact h1 a ha y hy
    | one => exact Commute.one_left y
    | mul b c _ _ hb hc => exact hb.mul_left hc
    | inv b _ hb => exact hb.inv_left
  exact h2

namespace LocalDatum

variable {Δ : LocalDatum X A}

theorem db_da_ne (h8 : 8 ≤ Nat.card Δ.D) : Δ.db * Δ.da ≠ Δ.da * Δ.db := by
  intro h
  have hsq : (Δ.db * Δ.da) ^ 2 = 1 := by
    rw [← Δ.dE_mul, sr_mul_r, ← Δ.dE_pow, sr_sq, Δ.dE_one]
  rw [(show Commute Δ.db Δ.da from h).mul_pow, Δ.db_sq, one_mul, Δ.da_sq h8] at hsq
  exact Δ.dz_ne_one hsq

variable {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

include h2 φ in
theorem TwoB_false_of_comm_field (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {u : X}
    (huS : u ∈ Δ.S) (huD : ∀ d ∈ Δ.D, u * d = d * u) (huQ : ∀ q ∈ Δ.Q, u * q = q * u)
    (huk : Δ.ψe u * k ∈ Δ.Dbar) : False := by
  have h8 := h2.2.2.2.2.1
  set s : Set X := (Δ.Q : Set X) ∪ {Δ.dz, u}
  have hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    have hzQ : ∀ q ∈ Δ.Q, Δ.dz * q = q * Δ.dz := fun q hq =>
      (Δ.commute_of_mem_Q_D hq Δ.dz_mem).symm
    have hzu : Δ.dz * u = u * Δ.dz := (huD _ Δ.dz_mem).symm
    rintro a (ha | ha) b (hb | hb)
    · exact Δ.commute_Q ha hb
    · rcases hb with rfl | rfl
      · exact (hzQ a ha).symm
      · exact (huQ a ha).symm
    · rcases ha with rfl | rfl
      · exact hzQ b hb
      · exact huQ b hb
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hzu
      · exact hzu.symm
      · rfl
  have hmem : ∀ c ∈ Δ.S, (∀ d ∈ Δ.D, c * d = d * c) → c ∈ closure s := by
    intro c hc hcD
    have hQs : ∀ q ∈ Δ.Q, q ∈ closure s := fun q hq => subset_closure (Or.inl hq)
    have hzs : Δ.dz ∈ closure s := subset_closure (Or.inr (Or.inl rfl))
    have hus : u ∈ closure s := subset_closure (Or.inr (Or.inr rfl))
    rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R hc) (Δ.commute_Dbar hc hcD) with h | h
    · obtain ⟨q, hq, hcq | hcq⟩ := Δ.mem_Qz_of_centralizes h8 hc hcD h
      · rw [hcq]; exact hQs q hq
      · rw [hcq]; exact mul_mem (hQs q hq) hzs
    · have hcu : Δ.ψe (c * u⁻¹) ∈ Δ.Dbar := by
        rw [Δ.ψe_mul hc (inv_mem huS), Δ.ψe_inv huS]
        have := mul_mem h (inv_mem huk)
        simpa [mul_assoc] using this
      have hcuD : ∀ d ∈ Δ.D, c * u⁻¹ * d = d * (c * u⁻¹) := fun d hd => by
        have h' : u⁻¹ * d = d * u⁻¹ := by
          calc u⁻¹ * d = u⁻¹ * (d * u) * u⁻¹ := by group
            _ = u⁻¹ * (u * d) * u⁻¹ := by rw [huD d hd]
            _ = d * u⁻¹ := by group
        rw [mul_assoc, h', ← mul_assoc, hcD d hd, mul_assoc]
      obtain ⟨q, hq, hcq⟩ := Δ.mem_Qz_of_centralizes h8 (mul_mem hc (inv_mem huS)) hcuD hcu
      have hc' : c = c * u⁻¹ * u := by group
      rcases hcq with h' | h'
      · rw [hc', h']
        exact mul_mem (hQs q hq) hus
      · rw [hc', h']
        exact mul_mem (mul_mem (hQs q hq) hzs) hus
  have hb := hmem _ (φ.conj_mem _ (Δ.D_le Δ.db_mem)) fun d hd =>
    (TwoB_commute φ hD1 hd Δ.db_mem).symm
  have ha := hmem _ (φ.conj_mem _ (Δ.D_le Δ.da_mem)) fun d hd =>
    (TwoB_commute φ hD1 hd Δ.da_mem).symm
  have hc := comm_of_mem_closure' hs hb ha
  apply db_da_ne h8
  have : φ.x * (Δ.db * Δ.da) * φ.x⁻¹ = φ.x * (Δ.da * Δ.db) * φ.x⁻¹ := by
    calc φ.x * (Δ.db * Δ.da) * φ.x⁻¹ = (φ.x * Δ.db * φ.x⁻¹) * (φ.x * Δ.da * φ.x⁻¹) := by group
      _ = (φ.x * Δ.da * φ.x⁻¹) * (φ.x * Δ.db * φ.x⁻¹) := hc
      _ = φ.x * (Δ.da * Δ.db) * φ.x⁻¹ := by group
  simpa using this

include h2 φ in
theorem TwoB_center_eq (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {v : X}
    (hvS : v ∈ Δ.S) (hvc : ∀ s ∈ Δ.S, s * v = v * s) (hvx : φ.x * v * φ.x⁻¹ = v)
    (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1) : v = Δ.t * Δ.dz := by
  have h8 := h2.2.2.2.2.1
  have hxz := TwoB_conj_dz h2 φ hD1
  have hxt := TwoB_conj_t h2 φ hD1
  have hvD : ∀ d ∈ Δ.D, v * d = d * v := fun d hd => (hvc d (Δ.D_le hd)).symm
  rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R hvS) (Δ.commute_Dbar hvS hvD) with h | h
  · have htz : Δ.t ≠ Δ.dz := fun h => Δ.t_not_mem_D (h ▸ Δ.dz_mem)
    obtain ⟨q, hq, rfl | rfl⟩ := Δ.mem_Qz_of_centralizes h8 hvS hvD h
    · exfalso
      have := Δ.eq_t_of_mem_Q hq hv2 hv1
      subst this
      rw [hxt] at hvx
      exact htz hvx.symm
    · have hq2 : q ^ 2 = 1 := by
        rw [(show Commute q Δ.dz from Δ.commute_of_mem_Q_D hq Δ.dz_mem).mul_pow, Δ.dz_sq,
          mul_one] at hv2
        exact hv2
      by_cases hq1 : q = 1
      · exfalso
        subst hq1
        rw [one_mul, hxz] at hvx
        exact htz hvx
      · rw [Δ.eq_t_of_mem_Q hq hq2 hq1]
  · exact (TwoB_false_of_comm_field h2 φ hD1 hvS hvD (fun q hq => (hvc q (Δ.Q_le hq)).symm)
      h).elim

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
