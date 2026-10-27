module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.LemmaQ

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaQ

open Subgroup CFSG.EvenSmallLie.UnitarySix.LemmaQ
open scoped commutatorElement

variable {G : Type*} [Group G]

structure ConfigN (Y D X Q J W E : Subgroup G) (t : G) : Prop where
  t_sq : t * t = 1
  D_le : D ≤ Y
  D_comm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a
  D_sq : ∀ d ∈ D, d * d = 1
  t_normD : t ∈ normalizer (D : Set G)
  D_conj : ∀ d ∈ D, d * t = t * d → ∃ d' ∈ D, d'⁻¹ * t * d' = d * t
  normD_of_norm : ∀ y ∈ Y, y ∈ normalizer (centInvSup D t : Set G) →
    y ∈ normalizer (D : Set G)
  Q_le : Q ≤ Y
  t_memQ : t ∈ Q
  Q_pGroup : IsPGroup 2 Q
  Q_le_norm : Q ≤ normalizer (centInvSup D t : Set G)
  Q_max : ∀ R : Subgroup G, IsPGroup 2 R → Q ≤ R → R ≤ Y →
    R ≤ normalizer (centInvSup D t : Set G) → R = Q
  Q_not_sylow : ∃ R : Subgroup G, R ≤ Y ∧ IsPGroup 2 R ∧ Nat.card Q < Nat.card R
  normD_of_normQ : ∀ y ∈ Y, y ∈ normalizer (Q : Set G) → y ∈ normalizer (D : Set G)
  normW_of_normQ : ∀ y ∈ Y, y ∈ normalizer (Q : Set G) → y ∈ normalizer (W : Set G)
  fusion : ∀ y ∈ Y, y ∈ normalizer (Q : Set G) → y⁻¹ * t * y ∈ Q →
    ∃ x ∈ X, ∃ d ∈ D, y⁻¹ * t * y = x * d * t
  J_le : J ≤ Y
  J_comm : ∀ j ∈ J, j * t = t * j
  J_normX : J ≤ normalizer (X : Set G)
  J_normD : J ≤ normalizer (D : Set G)
  J_trans : ∀ a ∈ X, ∀ b ∈ X, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j⁻¹ * a * j = b
  W_le : W ≤ D
  E_le : E ≤ Y
  E_t : ∀ u ∈ E, ∃ x ∈ X, ∃ d ∈ D, u⁻¹ * t * u = x * d * t
  E_normW : ∀ j ∈ J, ∀ u ∈ E, j * u * j⁻¹ ∈ normalizer (W : Set G)
  normW_cent : ∀ j ∈ J, ∀ c ∈ Y, c * t = t * c → j * c * j⁻¹ ∈ normalizer (W : Set G) →
    c ∈ normalizer (centInvSup D t : Set G)

variable {Y D X Q J W E : Subgroup G} {t : G}

namespace ConfigN

theorem exists_moving [Finite G] (h : ConfigN Y D X Q J W E t) :
    ∃ x₀ ∈ Y, x₀ ∈ normalizer (D : Set G) ∧ x₀ ∈ normalizer (W : Set G) ∧
      ∃ x₁ ∈ X, x₁ ≠ 1 ∧ ∃ d₀ ∈ D, x₀⁻¹ * t * x₀ = x₁ * d₀ * t := by
  obtain ⟨R, hRY, hR2, hcard⟩ := h.Q_not_sylow
  obtain ⟨P, hPY, hP2, hQP⟩ := exists_pGroup_gt h.Q_le h.Q_pGroup hRY hR2 hcard
  obtain ⟨x₀, hx₀P, hx₀N, hx₀Q⟩ := exists_mem_normalizer_not_mem hP2 hQP
  have hx₀Y : x₀ ∈ Y := hPY hx₀P
  have hx₀D := h.normD_of_normQ x₀ hx₀Y hx₀N
  have htQ : x₀⁻¹ * t * x₀ ∈ Q := (mem_normalizer_iff''.mp hx₀N t).mp h.t_memQ
  obtain ⟨x₁, hx₁, d₀, hd₀, hx₀t⟩ := h.fusion x₀ hx₀Y hx₀N htQ
  refine ⟨x₀, hx₀Y, hx₀D, h.normW_of_normQ x₀ hx₀Y hx₀N, x₁, hx₁, ?_, d₀, hd₀, hx₀t⟩
  rintro rfl
  rw [one_mul] at hx₀t
  have hx₀A := mem_normalizer_centInvSup h.t_sq h.D_comm h.D_sq hx₀D hd₀ hx₀t
  have hR' : Q ⊔ zpowers x₀ = Q :=
    h.Q_max _ (hP2.to_le (sup_le hQP.le (zpowers_le.mpr hx₀P))) le_sup_left
      (sup_le h.Q_le (zpowers_le.mpr hx₀Y)) (sup_le h.Q_le_norm (zpowers_le.mpr hx₀A))
  exact hx₀Q (hR' ▸ mem_sup_right (mem_zpowers x₀))

theorem exists_conj_coset [Finite G] (h : ConfigN Y D X Q J W E t) {x' : G} (hx' : x' ∈ X) :
    ∃ j ∈ J, ∃ s ∈ Y, s ∈ normalizer (D : Set G) ∧ j * s * j⁻¹ ∈ normalizer (W : Set G) ∧
      ∃ d ∈ D, s⁻¹ * t * s = x' * d * t := by
  by_cases h1 : x' = 1
  · exact ⟨1, one_mem _, 1, one_mem _, one_mem _, by simp, 1, one_mem _, by simp [h1]⟩
  obtain ⟨x₀, hx₀Y, hx₀D, hx₀W, x₁, hx₁, hx₁1, d₀, hd₀, hx₀t⟩ := h.exists_moving
  obtain ⟨j, hj, hjx⟩ := h.J_trans x₁ hx₁ x' hx' hx₁1 h1
  have hjD : j ∈ normalizer (D : Set G) := h.J_normD hj
  refine ⟨j, hj, j⁻¹ * x₀ * j, ?_, ?_, ?_, j⁻¹ * d₀ * j, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem (h.J_le hj)) hx₀Y) (h.J_le hj)
  · exact mul_mem (mul_mem (inv_mem hjD) hx₀D) hjD
  · simpa [mul_assoc] using hx₀W
  · exact (mem_normalizer_iff''.mp hjD d₀).mp hd₀
  · have hjt : j⁻¹ * t * j = t := by rw [mul_assoc, ← h.J_comm j hj]; group
    calc (j⁻¹ * x₀ * j)⁻¹ * t * (j⁻¹ * x₀ * j)
        = j⁻¹ * (x₀⁻¹ * (j * t * j⁻¹) * x₀) * j := by group
      _ = j⁻¹ * (x₁ * d₀ * t) * j := by
          rw [show j * t * j⁻¹ = t by rw [h.J_comm j hj]; group, hx₀t]
      _ = (j⁻¹ * x₁ * j) * (j⁻¹ * d₀ * j) * (j⁻¹ * t * j) := by group
      _ = x' * (j⁻¹ * d₀ * j) * t := by rw [hjx, hjt]

theorem le_normalizer [Finite G] (h : ConfigN Y D X Q J W E t) : E ≤ normalizer (D : Set G) := by
  intro u hu
  obtain ⟨x', hx', d', hd', hut⟩ := h.E_t u hu
  obtain ⟨j, hj, s, hsY, hsD, hsW, d₀, hd₀, hst⟩ := h.exists_conj_coset hx'
  have hδ : t⁻¹ * (d₀⁻¹ * d') * t ∈ D := by
    exact (mem_normalizer_iff''.mp h.t_normD (d₀⁻¹ * d')).mp (mul_mem (inv_mem hd₀) hd')
  set δ := t⁻¹ * (d₀⁻¹ * d') * t with hδdef
  have he : s * δ * s⁻¹ ∈ D := (mem_normalizer_iff.mp hsD δ).mp hδ
  set e := s * δ * s⁻¹ with hedef
  have key : (u * s⁻¹)⁻¹ * t * (u * s⁻¹) = t * e := by
    calc (u * s⁻¹)⁻¹ * t * (u * s⁻¹) = s * (u⁻¹ * t * u) * s⁻¹ := by group
      _ = s * ((x' * d₀ * t) * δ) * s⁻¹ := by rw [hut, hδdef]; group
      _ = s * ((s⁻¹ * t * s) * δ) * s⁻¹ := by rw [hst]
      _ = t * e := by rw [hedef]; group
  have hsq : (e * t) * (e * t) = 1 := by
    calc (e * t) * (e * t) = t⁻¹ * ((t * e) * (t * e)) * t := by group
      _ = t⁻¹ * ((u * s⁻¹)⁻¹ * (t * t) * (u * s⁻¹)) * t := by rw [← key]; group
      _ = 1 := by rw [h.t_sq]; group
  have hcomm : e * t = t * e := comm_of_mul_sq h.t_sq (h.D_sq e he) hsq
  obtain ⟨d₁, hd₁, hd₁t⟩ := h.D_conj e he hcomm
  have hcY : u * s⁻¹ * d₁⁻¹ ∈ Y :=
    mul_mem (mul_mem (h.E_le hu) (inv_mem hsY)) (inv_mem (h.D_le hd₁))
  have hct : (u * s⁻¹ * d₁⁻¹) * t = t * (u * s⁻¹ * d₁⁻¹) := by
    have h2 : (u * s⁻¹ * d₁⁻¹)⁻¹ * t * (u * s⁻¹ * d₁⁻¹) = t := by
      calc (u * s⁻¹ * d₁⁻¹)⁻¹ * t * (u * s⁻¹ * d₁⁻¹)
          = d₁ * ((u * s⁻¹)⁻¹ * t * (u * s⁻¹)) * d₁⁻¹ := by group
        _ = d₁ * (d₁⁻¹ * t * d₁) * d₁⁻¹ := by rw [key, ← hcomm, hd₁t]
        _ = t := by group
    calc (u * s⁻¹ * d₁⁻¹) * t
        = (u * s⁻¹ * d₁⁻¹) * ((u * s⁻¹ * d₁⁻¹)⁻¹ * t * (u * s⁻¹ * d₁⁻¹)) := by rw [h2]
      _ = t * (u * s⁻¹ * d₁⁻¹) := by group
  have hcW : j * (u * s⁻¹ * d₁⁻¹) * j⁻¹ ∈ normalizer (W : Set G) := by
    have h1 := h.E_normW j hj u hu
    have h2 : j * s⁻¹ * j⁻¹ ∈ normalizer (W : Set G) := by
      simpa [mul_assoc] using inv_mem hsW
    have h3 : j * d₁⁻¹ * j⁻¹ ∈ normalizer (W : Set G) :=
      mem_normalizer_of_le_comm h.D_comm h.W_le
        ((mem_normalizer_iff.mp (h.J_normD hj) _).mp (inv_mem hd₁))
    have := mul_mem (mul_mem h1 h2) h3
    simpa [mul_assoc] using this
  have hcD := h.normD_of_norm _ hcY (h.normW_cent j hj _ hcY hct hcW)
  have hu' : u = (u * s⁻¹ * d₁⁻¹) * d₁ * s := by group
  rw [hu']
  exact mul_mem (mul_mem hcD (Subgroup.le_normalizer hd₁)) hsD

theorem lemmaQ [Finite G] (h : ConfigN Y D X Q J W E t) {V : Subgroup G} (hVD : V ≤ D)
    (hVE : V ≤ E) (hEV : E ≤ normalizer (V : Set G)) (hJV : J ≤ normalizer (V : Set G))
    (hJ : ∀ d ∈ D, ∀ j ∈ J, ⁅d, j⁆ ∈ V) (hE : E ≤ ⁅E, J⁆ ⊔ V) :
    E ≤ normalizer (D : Set G) ∧ D ≤ normalizer (E : Set G) ∧ ⁅D, E⁆ ≤ V := by
  have hED := h.le_normalizer
  have hc := commutator_le_of_normalizer h.D_comm hVD hED hEV h.J_normD hJV hJ hE
  exact ⟨hED, le_normalizer_of_commutator_le hc hVE, hc⟩

end ConfigN

end CFSG.EvenSmallLie.UnitarySix.YamadaQ
