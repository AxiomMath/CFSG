module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Inv
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Act
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

private lemma y6_conj_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    t * v * t⁻¹ = v⁻¹ := by
  rw [h.hV] at hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← conj_zpow (a := t) (b := u) (i := k), h.t_inv, inv_zpow]

private lemma y6_A_comm_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a v : G}
    (ha : a ∈ A) (hv : v ∈ V) : a * v = v * a :=
  y6_C0_comm h a ha v (y6_V_le_C0 h hv)

private lemma y6_sq_atv (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a v : G}
    (ha : a ∈ A) (hv : v ∈ V) : (a * t * v) ^ 2 = a ^ 2 := by
  have ht2 : t ^ 2 = 1 := by simpa [h.t_ord] using pow_orderOf_eq_one t
  have hvt : v * t = t * v⁻¹ := by
    have h2 := y6_conj_V h (V.inv_mem hv)
    calc v * t = (t * v⁻¹ * t⁻¹) * t := by rw [h2]; group
      _ = t * v⁻¹ := by group
  have htv2 : (t * v) ^ 2 = 1 := by
    calc (t * v) ^ 2 = t * (v * t) * v := by rw [pow_two]; group
      _ = t * (t * v⁻¹) * v := by rw [hvt]
      _ = 1 := by rw [← mul_assoc t t v⁻¹, ← pow_two, ht2]; group
  have hatv : Commute a (t * v) :=
    Commute.mul_right (h.t_cent a ha) (y6_A_comm_V h ha hv)
  calc (a * t * v) ^ 2 = (a * (t * v)) ^ 2 := by group
    _ = a ^ 2 * (t * v) ^ 2 := Commute.mul_pow hatv 2
    _ = a ^ 2 := by rw [htv2, mul_one]

theorem y6_trans_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G))
    (hxA : ∀ a ∈ A, ⁅a, x⁆ ∈ V) : t⁻¹ * (x * t * x⁻¹) ∈ V := by
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← h.hA]; exact h.card_A
  have memA : ∀ {a : G}, a ∈ A → a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
    intro a ha; rw [← h.hA]; exact ha
  have ht_up : t ∈ y6Up A V t := by
    refine ⟨1, A.one_mem, ?_, 1, V.one_mem, ?_⟩
    · simp
    · group
  obtain ⟨a₀, ha₀, ha₀sq, v₀, hv₀, hxt_eq⟩ := y6_conj_Up h hx1 hx2 t ht_up
  have hcomm : ∀ b ∈ A, b ^ 2 = 1 → a₀ * b = b * a₀ := by
    intro b hb hb2
    set v₁ := (⁅b, x⁆)⁻¹ with hv₁_def
    have hv₁ : v₁ ∈ V := by rw [hv₁_def]; exact V.inv_mem (hxA b hb)
    have hbt : (b * t) ^ 2 = 1 := by
      have ht2 : t ^ 2 = 1 := by simpa [h.t_ord] using pow_orderOf_eq_one t
      rw [Commute.mul_pow (h.t_cent b hb) 2, hb2, ht2, mul_one]
    have hb1 : x * b * x⁻¹ = b * v₁ := by
      have hbc : x * b * x⁻¹ = (⁅b, x⁆)⁻¹ * b := by
        simp only [commutatorElement_def]; group
      rw [hbc, ← hv₁_def, (y6_A_comm_V h hb hv₁).symm]
    have hvt : v₁ * t = t * v₁⁻¹ := by
      have h2 := y6_conj_V h (V.inv_mem hv₁)
      calc v₁ * t = (t * v₁⁻¹ * t⁻¹) * t := by rw [h2]; group
        _ = t * v₁⁻¹ := by group
    have hform : x * (b * t) * x⁻¹ = (b * a₀) * t * (v₁⁻¹ * v₀) := by
      have h1 : x * (b * t) * x⁻¹ = (x * b * x⁻¹) * (x * t * x⁻¹) := by group
      rw [h1, hb1, hxt_eq]
      calc (b * v₁) * (a₀ * t * v₀) = b * (v₁ * a₀) * t * v₀ := by group
        _ = b * (a₀ * v₁) * t * v₀ := by rw [← y6_A_comm_V h ha₀ hv₁]
        _ = (b * a₀) * (v₁ * t) * v₀ := by group
        _ = (b * a₀) * (t * v₁⁻¹) * v₀ := by rw [hvt]
        _ = (b * a₀) * t * (v₁⁻¹ * v₀) := by group
    have hsq1 : (x * (b * t) * x⁻¹) ^ 2 = (b * a₀) ^ 2 := by
      rw [hform]
      exact y6_sq_atv h (A.mul_mem hb ha₀) (V.mul_mem (V.inv_mem hv₁) hv₀)
    have hsq2 : (x * (b * t) * x⁻¹) ^ 2 = 1 := by
      rw [conj_pow (a := x) (b := b * t) (i := 2), hbt]
      group
    have hba2 : (b * a₀) ^ 2 = 1 := by rw [← hsq1]; exact hsq2
    have h2 := y6q8_sq_mul h.rel b (memA hb) a₀ (memA ha₀)
    rw [hba2, hb2, ha₀sq] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using h2.symm)
  have hcomm_sq1 : ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a ^ 2 = 1 →
      a₀ * a = a * a₀ := by
    intro a ha ha2
    exact hcomm a (by rw [h.hA]; exact ha) ha2
  have ha₀V : a₀ ∈ V := by
    rcases y6q8_comm_sq1 h.rel h.z_ne hA32 (memA ha₀) hcomm_sq1 with h1 | h1
    · rw [h1]; exact V.one_mem
    · rw [h1]; exact y6_z_mem_V h
  rw [hxt_eq]
  have hta : t⁻¹ * a₀ = a₀ * t⁻¹ := (Commute.inv_right (h.t_cent a₀ ha₀)).eq.symm
  have hkey : t⁻¹ * (a₀ * t * v₀) = a₀ * v₀ := by
    calc t⁻¹ * (a₀ * t * v₀) = (t⁻¹ * a₀) * t * v₀ := by group
      _ = (a₀ * t⁻¹) * t * v₀ := by rw [hta]
      _ = a₀ * v₀ := by group
  rw [hkey]
  exact V.mul_mem ha₀V hv₀

theorem y6_trans (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G))
    (hxAV : ∀ w ∈ A ⊔ V, ⁅w, x⁆ ∈ V) :
    x ∈ CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V := by
  have hU : (((A ⊔ V : Subgroup G) : Set G) ∪ {t}) ⊆ (A ⊔ C0 : Subgroup G) := by
    intro y hy
    rcases hy with hy | hy
    · exact sup_le le_sup_left (le_sup_of_le_right (y6_V_le_C0 h)) hy
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_sup_right (y6_t_mem_C0 h)
  have hgen : closure ((((A ⊔ V : Subgroup G) : Set G) ∪ {t}) ∪ (V : Set G)) =
      A ⊔ C0 := by
    apply le_antisymm
    · rw [closure_le]
      intro y hy
      rcases hy with (hy | hy) | hy
      · exact sup_le le_sup_left (le_sup_of_le_right (y6_V_le_C0 h)) hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_sup_right (y6_t_mem_C0 h)
      · exact le_sup_of_le_right (y6_V_le_C0 h) hy
    · apply sup_le
      · intro a ha
        exact subset_closure (Or.inl (Or.inl (Subgroup.mem_sup_left ha)))
      · rw [h.hC0, closure_le]
        intro y hy
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy
        · rw [hy]
          exact subset_closure (Or.inr (by rw [h.hV]; exact Subgroup.mem_zpowers u))
        · rw [hy]
          exact subset_closure (Or.inl (Or.inr (Set.mem_singleton t)))
  refine (y6_mem_centSec_iff (C := A ⊔ C0) (V := V)
    (U := ((A ⊔ V : Subgroup G) : Set G) ∪ {t})
    (le_trans (y6_V_le_C0 h) le_sup_right) (y6_C1_le_N_V h) hU hgen hx1 hx2).mpr ?_
  intro y hy
  rcases hy with hy | hy
  · convert hxAV y⁻¹ (inv_mem hy) using 1
    simp only [commutatorElement_def, inv_inv]
    group
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact y6_trans_t h hx1 hx2 (fun a ha => hxAV a (Subgroup.mem_sup_left ha))

end CFSG.OddStandard.HigherRank.YamadaG23
