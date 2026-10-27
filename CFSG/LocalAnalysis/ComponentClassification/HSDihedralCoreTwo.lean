module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreCaseOne

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (HaradaInput ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

omit [Finite X] in
theorem mem_map_conj_iff {H : Subgroup X} {x u : X} :
    u ∈ H.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * u * x ∈ H := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  · intro h
    exact ⟨x⁻¹ * u * x, h, by simp [MulAut.conj_apply, mul_assoc]⟩

namespace LocalDatum

variable (Δ : LocalDatum X A)

@[expose] def CoreOut : Prop :=
  Δ.Q = zpowers Δ.t ∧ ∃ w ∈ Δ.S, w ^ 2 = 1 ∧ (∀ d ∈ Δ.Dbar, Δ.ψe w * d = d * Δ.ψe w) ∧
    Δ.ψe w ∉ Δ.Dbar

omit [Finite X] in
theorem commute_Dbar {c : X} (hc : c ∈ Δ.S) (hcD : ∀ d ∈ Δ.D, c * d = d * c) :
    ∀ d ∈ Δ.Dbar, Δ.ψe c * d = d * Δ.ψe c := fun d hd => by
  obtain ⟨d', hd', rfl⟩ := (Δ.mem_Dbar_iff).mp hd
  exact (Δ.commute_iff hc hd').mp (hcD d' hd')

theorem dz_comm_S (h8 : 8 ≤ Nat.card Δ.D) {s : X} (hs : s ∈ Δ.S) : s * Δ.dz = Δ.dz * s := by
  have hm : s * Δ.dz * s⁻¹ ∈ Δ.D := Δ.conj_mem_D s hs _ Δ.dz_mem
  have hc : ∀ d ∈ Δ.D, s * Δ.dz * s⁻¹ * d = d * (s * Δ.dz * s⁻¹) := by
    intro d hd
    have h := Δ.dz_comm (Δ.conj_mem_D s⁻¹ (inv_mem hs) d hd)
    calc s * Δ.dz * s⁻¹ * d = s * (Δ.dz * (s⁻¹ * d * s⁻¹⁻¹)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * d * s⁻¹⁻¹) * Δ.dz) * s⁻¹ := by rw [h]
      _ = d * (s * Δ.dz * s⁻¹) := by group
  rcases Δ.eq_dz_of_central h8 hm hc with h | h
  · exfalso
    apply Δ.dz_ne_one
    calc Δ.dz = s⁻¹ * (s * Δ.dz * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  · calc s * Δ.dz = s * Δ.dz * s⁻¹ * s := by group
      _ = Δ.dz * s := by rw [h]

theorem eq_of_central_Dbar (h8 : 8 ≤ Nat.card Δ.D) {y : A} (hy : y ∈ Δ.Dbar)
    (hyc : ∀ d ∈ Δ.Dbar, y * d = d * y) : y = 1 ∨ y = Δ.ψe Δ.dz := by
  obtain ⟨d, hd, rfl⟩ := (Δ.mem_Dbar_iff).mp hy
  have hdc : ∀ d' ∈ Δ.D, d * d' = d' * d := fun d' hd' => Δ.eq_of_ψe_eq (mul_mem hd hd')
    (mul_mem hd' hd) (by
      rw [Δ.ψe_mul (Δ.D_le hd) (Δ.D_le hd'), Δ.ψe_mul (Δ.D_le hd') (Δ.D_le hd)]
      exact hyc _ (Δ.ψe_mem_Dbar hd'))
  rcases Δ.eq_dz_of_central h8 hd hdc with rfl | rfl
  · exact Or.inl Δ.ψe_one
  · exact Or.inr rfl

theorem mem_Qz_of_centralizes (h8 : 8 ≤ Nat.card Δ.D) {c : X} (hc : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) (hcDbar : Δ.ψe c ∈ Δ.Dbar) :
    ∃ q ∈ Δ.Q, c = q ∨ c = q * Δ.dz := by
  obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hc hcDbar
  have hdc : ∀ d' ∈ Δ.D, d * d' = d' * d := fun d' hd' =>
    commute_of_mul_commute (Δ.commute_of_mem_Q_D hq hd') (hcD d' hd')
  rcases Δ.eq_dz_of_central h8 hd hdc with rfl | rfl
  · exact ⟨q, hq, Or.inl (mul_one q)⟩
  · exact ⟨q, hq, Or.inr rfl⟩

omit [Finite X] in
theorem conj_mem_Dbar {s : X} (hs : s ∈ Δ.S) {y : A} (hy : y ∈ Δ.Dbar) :
    Δ.ψe s * y * (Δ.ψe s)⁻¹ ∈ Δ.Dbar := by
  obtain ⟨d, hd, rfl⟩ := (Δ.mem_Dbar_iff).mp hy
  rw [← Δ.ψe_conj hs (Δ.D_le hd)]
  exact Δ.ψe_mem_Dbar (Δ.conj_mem_D s hs d hd)

theorem conj_k {k : A} (h2 : Δ.CaseTwo k) {s : X} (hs : s ∈ Δ.S) :
    Δ.ψe s * k * (Δ.ψe s)⁻¹ = k ∨ Δ.ψe s * k * (Δ.ψe s)⁻¹ = Δ.ψe Δ.dz * k := by
  obtain ⟨hkR, hkD, hkn, hk2, h8, hC⟩ := h2
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hk2])
  set g := Δ.ψe s
  have hcomm : ∀ d ∈ Δ.Dbar, g * k * g⁻¹ * d = d * (g * k * g⁻¹) := by
    intro d hd
    have hd' : g⁻¹ * d * g⁻¹⁻¹ ∈ Δ.Dbar := by
      rw [← Δ.ψe_inv hs]
      exact Δ.conj_mem_Dbar (inv_mem hs) hd
    have h := hkD _ hd'
    calc g * k * g⁻¹ * d = g * (k * (g⁻¹ * d * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d * g⁻¹⁻¹) * k) * g⁻¹ := by rw [h]
      _ = d * (g * k * g⁻¹) := by group
  have hmemR : g * k * g⁻¹ ∈ Δ.R := mul_mem (mul_mem (Δ.ψe_mem_R hs) hkR)
    (inv_mem (Δ.ψe_mem_R hs))
  rcases hC _ hmemR hcomm with h | h
  · exfalso
    apply hkn
    have := Δ.conj_mem_Dbar (inv_mem hs) h
    rw [Δ.ψe_inv hs] at this
    simpa [g, mul_assoc] using this
  · have hc' : ∀ d ∈ Δ.Dbar, g * k * g⁻¹ * k * d = d * (g * k * g⁻¹ * k) := fun d hd => by
      rw [mul_assoc, hkD d hd, ← mul_assoc, hcomm d hd, mul_assoc]
    rcases Δ.eq_of_central_Dbar h8 h hc' with h' | h'
    · left
      calc g * k * g⁻¹ = g * k * g⁻¹ * k * k⁻¹ := by group
        _ = k := by rw [h', one_mul, hkinv]
    · right
      calc g * k * g⁻¹ = g * k * g⁻¹ * k * k⁻¹ := by group
        _ = Δ.ψe Δ.dz * k := by rw [h', hkinv]

theorem Q_eq_zpowers (hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t) : Δ.Q = zpowers Δ.t := by
  refine le_antisymm (fun q hq => ?_) (zpowers_le.mpr Δ.t_mem_Q)
  rcases hQ q hq with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

theorem out_or_sqrt {k : A} (h2 : Δ.CaseTwo k) :
    Δ.CoreOut ∨ ∃ c ∈ Δ.S, (∀ d ∈ Δ.D, c * d = d * c) ∧ c ^ 2 = Δ.t := by
  obtain ⟨w, hwS, hwk⟩ := (Δ.mem_R_iff).mp h2.1
  have hwD : ∀ d ∈ Δ.D, w * d = d * w := fun d hd =>
    (Δ.commute_iff hwS hd).mpr (by rw [hwk]; exact h2.2.1 _ (Δ.ψe_mem_Dbar hd))
  by_cases hy : ∃ y ∈ Δ.Q, y ≠ 1 ∧ y ≠ Δ.t
  · obtain ⟨y, hy, hy1, hyt⟩ := hy
    obtain ⟨q, hq, hqt⟩ := Δ.exists_sq_eq_t hy hy1 hyt
    exact Or.inr ⟨q, Δ.Q_le hq, fun d hd => Δ.commute_of_mem_Q_D hq hd, hqt⟩
  · push Not at hy
    have hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t := fun q hq => by
      by_cases h1 : q = 1
      · exact Or.inl h1
      · exact Or.inr (hy q hq h1)
    rcases hQ _ (Δ.sq_mem_Q_of_caseTwo h2 hwS hwD) with h | h
    · left
      refine ⟨Δ.Q_eq_zpowers hQ, w, hwS, h, ?_, ?_⟩
      · rw [hwk]; exact h2.2.1
      · rw [hwk]; exact h2.2.2.1
    · exact Or.inr ⟨w, hwS, hwD, h⟩

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
