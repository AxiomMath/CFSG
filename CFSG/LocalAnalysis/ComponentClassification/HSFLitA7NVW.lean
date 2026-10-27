module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NMu
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NAct

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def three : List V4 := [(1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 0, 0)]

@[expose] def sigCols (p q : V4) : Fin 4 → V4 := ![p, q, (0, 0, 1, 0), (0, 0, 0, 1)]

@[expose] def dCols : Fin 4 → V4 := sigCols (0, 1, 0, 0) (1, 1, 0, 0)

@[expose] def xCols : Fin 4 → V4 := sigCols (1, 0, 0, 0) (1, 1, 0, 0)

@[expose] def tCols (e f p q a : Fin 2) : Fin 4 → V4 :=
  ![(1, 0, 0, 0), (p, 1, 0, q), (e, 0, 1, f), (a, 0, 0, 1)]

theorem key_v : ∀ a p q : Fin 2,
    (∃ σ₁ ∈ three, ∃ σ₂ ∈ three, ∀ i : Fin 4,
      lin dCols (tCols 0 1 p q a i) = lin (tCols 0 1 p q a) (sigCols σ₁ σ₂ i)) →
    a = 0 ∧ q = 0 := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

theorem Sec6Hyp.exists_conj_T₁ (H : S.Sec6Hyp T₁) {b : X} (hb : b ∈ S.B)
    (hcb : ConjTo S.t b) : ∃ g ∈ T₁, g * S.t * g⁻¹ = b := by
  have htB : S.t ∈ S.B := subset_closure (by simp)
  set O₁ : Set X := {b | ∃ g ∈ T₁, g * S.t * g⁻¹ = b} with hO₁
  have hidx := relIndex_inf_centralizer_eq_ncard T₁ S.t
  have hT₁C : T₁ ⊓ centralizer ({S.t} : Set X) = S.data.T :=
    S.eq_T_of_le' (H.isPGroup.to_le inf_le_left) (le_inf H.le S.data.T_le_centralizer)
      inf_le_right
  rw [hT₁C] at hidx
  have hrel : S.data.T.relIndex T₁ * Nat.card S.data.T = Nat.card T₁ := by
    have := relIndex_mul_card (H := S.data.T) (K := T₁)
    rwa [inf_of_le_left H.le] at this
  have hO₁4 : O₁.ncard = 4 := by
    rw [← hidx]
    have hpos : 0 < Nat.card S.data.T := Nat.card_pos
    rw [H.card] at hrel
    exact Nat.eq_of_mul_eq_mul_right hpos hrel
  have hO₁sub : O₁ ⊆ ({S.t, S.t * S.z, S.t * S.k, S.t * S.z * S.k} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    have hb' := S.conj_mem_B (H.le_normalizer hg) htB
    rcases (H.fus _ hb').mp ⟨g, rfl⟩ with h | h | h | h <;> simp [h]
  have hO₁eq : O₁ = ({S.t, S.t * S.z, S.t * S.k, S.t * S.z * S.k} : Set X) := by
    refine Set.eq_of_subset_of_ncard_le hO₁sub ?_ (Set.toFinite _)
    rw [hO₁4]
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  have hbO : b ∈ O₁ := by
    rw [hO₁eq]
    rcases (H.fus b hb).mp hcb with h | h | h | h <;> simp [h]
  exact hbO

namespace Inst

variable (I : S.Inst)

theorem wV_mem_B_iff (w : V4) : I.wV w ∈ S.B ↔ w.2.1 = 0 := by
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  obtain ⟨a, b, c, d⟩ := w
  simp only
  constructor
  · intro h
    rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
    · rfl
    · exfalso
      apply I.yi_not_mem_B
      have e : I.yi =
          (S.z ^ (a : ℕ))⁻¹ * I.wV (a, 1, c, d) * (S.t ^ (c : ℕ) * I.ki ^ (d : ℕ))⁻¹ := by
        simp only [wV, Fin.val_one, pow_one]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (pow_mem hzB _)) h)
        (inv_mem (mul_mem (pow_mem htB _) (pow_mem I.ki_mem_B _)))
  · rintro rfl
    simp only [wV, Fin.val_zero, pow_zero, mul_one]
    exact mul_mem (mul_mem (pow_mem hzB _) (pow_mem htB _)) (pow_mem I.ki_mem_B _)

theorem cols_of_mem_NC (hO : S.Fus) (s : normalizer (I.E : Set X))
    (hs : (s : X) ∈ centralizer ({S.t} : Set X)) :
    ∃ σ₁ ∈ three, ∃ σ₂ ∈ three, σ₁ ≠ σ₂ ∧ ∀ i, I.μ s (bas i) = sigCols σ₁ σ₂ i := by
  have hsNC : (s : X) ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X) := ⟨s.2, hs⟩
  have hthree : ∀ e : X, (e = S.z ∨ e = I.yi ∨ e = S.z * I.yi) →
      ∃ σ ∈ three, (s : X) * e * (s : X)⁻¹ = I.wV σ := by
    intro e he
    rcases I.conj_mem_three hO hsNC he with h | h | h
    · exact ⟨(1, 0, 0, 0), by simp [three], by rw [h]; simp [wV]⟩
    · exact ⟨(0, 1, 0, 0), by simp [three], by rw [h]; simp [wV]⟩
    · exact ⟨(1, 1, 0, 0), by simp [three], by rw [h]; simp [wV]⟩
  obtain ⟨σ₁, h₁, e₁⟩ := hthree S.z (Or.inl rfl)
  obtain ⟨σ₂, h₂, e₂⟩ := hthree I.yi (Or.inr (Or.inl rfl))
  refine ⟨σ₁, h₁, σ₂, h₂, fun h12 => ?_, I.μ_bas_of e₁ e₂ ?_ ?_⟩
  · have : (s : X) * S.z * (s : X)⁻¹ = (s : X) * I.yi * (s : X)⁻¹ := by rw [e₁, e₂, h12]
    have hzy : S.z = I.yi := by simpa using this
    have := I.wV_injective ((show I.wV (1, 0, 0, 0) = S.z by simp [wV]).trans
      (hzy.trans (show I.yi = I.wV (0, 1, 0, 0) by simp [wV])))
    simp at this
  · have : (s : X) * S.t * (s : X)⁻¹ = S.t := by
      rw [mem_centralizer_singleton_iff.mp hs]; group
    rw [this]; simp [sigCols, wV]
  · rw [I.conj_ki_of_mem_NC hsNC]; simp [sigCols, wV]

theorem μ_mul_bas (n m : normalizer (I.E : Set X)) (i : Fin 4) :
    I.μ (n * m) (bas i) = lin (fun j => I.μ n (bas j)) (I.μ m (bas i)) := by
  rw [I.μ_mul, I.μ_eq_lin]

theorem x_cols (hx : S.x ∈ normalizer (I.E : Set X)) (i : Fin 4) :
    I.μ ⟨S.x, hx⟩ (bas i) = xCols i := by
  have hxT := S.x_mem.1
  have hc : ∀ {g : X}, g ∈ S.B → S.x * g * S.x⁻¹ = g := fun hg => by
    rw [← S.central_of_mem_B hg hxT]; group
  refine I.μ_bas_of ?_ ?_ ?_ ?_ i
  · rw [hc (subset_closure (by simp))]; simp [xCols, sigCols, wV]
  · rw [I.x_conj_yi]; simp [xCols, sigCols, wV]
  · rw [hc (subset_closure (by simp))]; simp [xCols, sigCols, wV]
  · rw [hc I.ki_mem_B]; simp [xCols, sigCols, wV]

theorem exists_tCols (H : S.Sec6Hyp T₁) {g : X} (hg : g ∈ T₁) {e f : Fin 2}
    (ht : g * S.t * g⁻¹ = I.wV (e, 0, 1, f)) :
    ∃ p q a : Fin 2, ∀ i, I.μ ⟨g, I.T₁_le H hg⟩ (bas i) = tCols e f p q a i := by
  have hgN := H.le_normalizer hg
  have hgE := I.T₁_le H hg
  have hz : g * S.z * g⁻¹ = S.z := S.conj_z_eq hgN
  have hk : ∃ a : Fin 2, g * I.ki * g⁻¹ = I.wV (a, 0, 0, 1) := by
    obtain ⟨w, hw⟩ := I.eq_wV (I.conj_wV_mem hgE (0, 0, 0, 1))
    have hkw : I.wV (0, 0, 0, 1) = I.ki := by simp [wV]
    rw [hkw] at hw
    have hB : I.wV w ∈ S.B := hw ▸ S.conj_mem_B hgN I.ki_mem_B
    have hnc : ¬ ConjTo S.t (I.wV w) := by
      rw [← hw, conjTo_conj_iff, ← hkw, I.conjTo_wV_iff H.fus]
      decide
    rw [I.wV_mem_B_iff] at hB
    rw [I.conjTo_wV_iff H.fus] at hnc
    obtain ⟨a, b, c, d⟩ := w
    simp only at hB hnc
    subst hB
    have hc : c = 0 := by
      rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
      · rfl
      · exact absurd rfl hnc
    subst hc
    have hd : d = 1 := by
      rcases Fin.exists_fin_two.mp ⟨d, rfl⟩ with rfl | rfl
      · exfalso
        have hza : I.wV (a, 0, 0, 0) = S.z ^ (a : ℕ) := by simp [wV]
        have hz' : g⁻¹ * S.z * g = S.z := by simpa using S.conj_z_eq (inv_mem hgN)
        have hza' : g⁻¹ * S.z ^ (a : ℕ) * g = S.z ^ (a : ℕ) := by
          have : g⁻¹ * S.z ^ (a : ℕ) * g = (g⁻¹ * S.z * g) ^ (a : ℕ) := by
            rw [show g⁻¹ * S.z * g = MulAut.conj g⁻¹ S.z by simp, ← map_pow]
            simp
          rw [this, hz']
        have h1 : I.ki = I.wV (a, 0, 0, 0) := by
          calc I.ki = g⁻¹ * (g * I.ki * g⁻¹) * g := by group
            _ = I.wV (a, 0, 0, 0) := by rw [hw, hza, hza']
        have h2 := I.wV_injective (hkw.trans h1)
        simp at h2
      · rfl
    subst hd
    exact ⟨a, hw⟩
  have hy : ∃ p q : Fin 2, g * I.yi * g⁻¹ = I.wV (p, 1, 0, q) := by
    obtain ⟨w, hw⟩ := I.eq_wV (I.conj_wV_mem hgE (0, 1, 0, 0))
    have hyw : I.wV (0, 1, 0, 0) = I.yi := by simp [wV]
    rw [hyw] at hw
    have hnB : I.wV w ∉ S.B := by
      intro h
      apply I.yi_not_mem_B
      have := S.conj_mem_B (inv_mem hgN) (hw ▸ h)
      simpa [mul_assoc] using this
    have hnc : ¬ ConjTo S.t (I.wV w) := by
      rw [← hw, conjTo_conj_iff, ← hyw, I.conjTo_wV_iff H.fus]
      decide
    rw [I.wV_mem_B_iff] at hnB
    rw [I.conjTo_wV_iff H.fus] at hnc
    obtain ⟨p, b, c, q⟩ := w
    simp only at hnB hnc
    have hb : b = 1 := by
      rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
      · exact absurd rfl hnB
      · rfl
    have hc : c = 0 := by
      rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
      · rfl
      · exact absurd rfl hnc
    subst hb hc
    exact ⟨p, q, hw⟩
  obtain ⟨a, hka⟩ := hk
  obtain ⟨p, q, hyq⟩ := hy
  refine ⟨p, q, a, I.μ_bas_of ?_ hyq ht hka⟩
  rw [hz]; simp [tCols, wV]

theorem conj_of_cols {n : normalizer (I.E : Set X)} {c : Fin 4 → V4}
    (hc : ∀ i, I.μ n (bas i) = c i) :
    (n : X) * S.z * (n : X)⁻¹ = I.wV (c 0) ∧ (n : X) * I.yi * (n : X)⁻¹ = I.wV (c 1) ∧
      (n : X) * S.t * (n : X)⁻¹ = I.wV (c 2) ∧ (n : X) * I.ki * (n : X)⁻¹ = I.wV (c 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← I.wV_bas_zero, I.conj_wV, hc]
  · rw [← I.wV_bas_one, I.conj_wV, hc]
  · rw [← I.wV_bas_two, I.conj_wV, hc]
  · rw [← I.wV_bas_three, I.conj_wV, hc]

theorem conj_wV_of_fix {g : X} (hz : g * S.z * g⁻¹ = S.z) (hy : g * I.yi * g⁻¹ = I.yi)
    (hk : g * I.ki * g⁻¹ = I.ki) (a b d : Fin 2) :
    g * I.wV (a, b, 0, d) * g⁻¹ = I.wV (a, b, 0, d) := by
  have hc : ∀ e : X, g * e * g⁻¹ = MulAut.conj g e := fun e => rfl
  simp only [wV, Fin.val_zero, pow_zero, mul_one]
  rw [hc, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc, ← hc, ← hc, hz, hy, hk]

theorem exists_v (H : S.Sec6Hyp T₁) : ∃ v ∈ T₁, v * S.t * v⁻¹ = S.t * I.ki ∧
    v * S.z * v⁻¹ = S.z ∧ v * I.yi * v⁻¹ = I.yi ∧ v * I.ki * v⁻¹ = I.ki := by
  have htk : S.t * I.ki = I.wV (0, 0, 1, 1) := by simp [wV]
  have htkB : S.t * I.ki ∈ S.B := mul_mem (subset_closure (by simp)) I.ki_mem_B
  have htkc : ConjTo S.t (S.t * I.ki) := by rw [htk, I.conjTo_wV_iff H.fus]
  obtain ⟨v₀, hv₀, hv₀t⟩ := H.exists_conj_T₁ htkB htkc
  rw [htk] at hv₀t
  obtain ⟨p, q, a, hc⟩ := I.exists_tCols H hv₀ hv₀t
  obtain ⟨d, hd, hdz, hdy⟩ := I.exists_d
  set V₀ : normalizer (I.E : Set X) := ⟨v₀, I.T₁_le H hv₀⟩ with hV₀
  set D : normalizer (I.E : Set X) := ⟨d, hd.1⟩ with hD
  have hdt : d * S.t * d⁻¹ = S.t := by rw [mem_centralizer_singleton_iff.mp hd.2]; group
  have hdcols : ∀ i, I.μ D (bas i) = dCols i := by
    refine I.μ_bas_of ?_ ?_ ?_ ?_
    · show d * S.z * d⁻¹ = _
      rw [hdz]; simp [dCols, sigCols, wV]
    · show d * I.yi * d⁻¹ = _
      rw [hdy]; simp [dCols, sigCols, wV]
    · show d * S.t * d⁻¹ = _
      rw [hdt]; simp [dCols, sigCols, wV]
    · show d * I.ki * d⁻¹ = _
      rw [I.conj_ki_of_mem_NC hd]; simp [dCols, sigCols, wV]
  set D' : normalizer (I.E : Set X) := V₀⁻¹ * D * V₀ with hD'
  have hD'C : (D' : X) ∈ centralizer ({S.t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : v₀ * S.t * v₀⁻¹ = S.t * I.ki := by rw [hv₀t, htk]
    have h2 : d * (S.t * I.ki) * d⁻¹ = S.t * I.ki := by
      rw [show d * (S.t * I.ki) * d⁻¹ = (d * S.t * d⁻¹) * (d * I.ki * d⁻¹) by group,
        I.conj_ki_of_mem_NC hd, mem_centralizer_singleton_iff.mp hd.2]
      group
    change v₀⁻¹ * d * v₀ * S.t = S.t * (v₀⁻¹ * d * v₀)
    calc v₀⁻¹ * d * v₀ * S.t = v₀⁻¹ * (d * (v₀ * S.t * v₀⁻¹) * d⁻¹) * (d * v₀) := by group
      _ = v₀⁻¹ * (v₀ * S.t * v₀⁻¹) * (d * v₀) := by rw [h1, h2]
      _ = S.t * (v₀⁻¹ * d * v₀) := by group
  obtain ⟨σ₁, h₁, σ₂, h₂, -, hσ⟩ := I.cols_of_mem_NC H.fus D' hD'C
  have hcomm : D * V₀ = V₀ * D' := by rw [hD']; group
  have key : ∀ i, lin dCols (tCols 0 1 p q a i) = lin (tCols 0 1 p q a) (sigCols σ₁ σ₂ i) := by
    intro i
    have h : I.μ (D * V₀) (bas i) = I.μ (V₀ * D') (bas i) := by rw [hcomm]
    rw [I.μ_mul_bas, I.μ_mul_bas, hc i, hσ i] at h
    have e1 : (fun j => I.μ D (bas j)) = dCols := funext hdcols
    have e2 : (fun j => I.μ V₀ (bas j)) = tCols 0 1 p q a := funext hc
    rwa [e1, e2] at h
  obtain ⟨rfl, rfl⟩ := key_v a p q ⟨σ₁, h₁, σ₂, h₂, key⟩
  obtain ⟨hz, hy, ht, hk⟩ := I.conj_of_cols hc
  simp only [tCols, wV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at hz hy ht hk
  have hxT := S.x_mem.1
  have hxB : ∀ {g : X}, g ∈ S.B → S.x * g * S.x⁻¹ = g := fun hg => by
    rw [← S.central_of_mem_B hg hxT]; group
  have hxt : S.x * S.t * S.x⁻¹ = S.t := hxB (subset_closure (by simp))
  have hxz : S.x * S.z * S.x⁻¹ = S.z := hxB (subset_closure (by simp))
  have hxk : S.x * I.ki * S.x⁻¹ = I.ki := hxB I.ki_mem_B
  rcases Fin.exists_fin_two.mp ⟨p, rfl⟩ with rfl | rfl
  · refine ⟨v₀, hv₀, ?_, ?_, ?_, ?_⟩
    · simpa [wV] using ht
    · simpa using hz
    · simpa using hy
    · simpa using hk
  · refine ⟨v₀ * S.x, mul_mem hv₀ (H.le hxT), ?_, ?_, ?_, ?_⟩
    · calc v₀ * S.x * S.t * (v₀ * S.x)⁻¹ = v₀ * (S.x * S.t * S.x⁻¹) * v₀⁻¹ := by group
        _ = S.t * I.ki := by rw [hxt]; simpa [wV] using ht
    · calc v₀ * S.x * S.z * (v₀ * S.x)⁻¹ = v₀ * (S.x * S.z * S.x⁻¹) * v₀⁻¹ := by group
        _ = S.z := by rw [hxz]; simpa using hz
    · have hz' : v₀ * S.z * v₀⁻¹ = S.z := by simpa using hz
      have hy' : v₀ * I.yi * v₀⁻¹ = S.z * I.yi := by simpa using hy
      calc v₀ * S.x * I.yi * (v₀ * S.x)⁻¹ = v₀ * (S.x * I.yi * S.x⁻¹) * v₀⁻¹ := by group
        _ = (v₀ * S.z * v₀⁻¹) * (v₀ * I.yi * v₀⁻¹) := by rw [I.x_conj_yi]; group
        _ = I.yi := by
            rw [hz', hy', ← mul_assoc, ← pow_two, S.z_sq, one_mul]
    · calc v₀ * S.x * I.ki * (v₀ * S.x)⁻¹ = v₀ * (S.x * I.ki * S.x⁻¹) * v₀⁻¹ := by group
        _ = I.ki := by rw [hxk]; simpa using hk

@[expose] def CaseI : Prop := ∃ n ∈ normalizer (I.E : Set X),
    n * S.t * n⁻¹ = S.t * S.z ∧ n * S.z * n⁻¹ = S.z ∧ n * I.yi * n⁻¹ = I.yi ∧
      n * I.ki * n⁻¹ = I.ki

@[expose] def Realizes (g : X) (a b d : Fin 2) : Prop :=
  g ∈ normalizer (I.E : Set X) ∧ g * S.z * g⁻¹ = S.z ∧ g * I.yi * g⁻¹ = I.yi ∧
    g * I.ki * g⁻¹ = I.ki ∧ g * S.t * g⁻¹ = S.t * I.wV (a, b, 0, d)

theorem Realizes.mul {g₁ g₂ : X} {a₁ b₁ d₁ a₂ b₂ d₂ : Fin 2} (h₁ : I.Realizes g₁ a₁ b₁ d₁)
    (h₂ : I.Realizes g₂ a₂ b₂ d₂) : I.Realizes (g₁ * g₂) (a₁ + a₂) (b₁ + b₂) (d₁ + d₂) := by
  obtain ⟨hn₁, hz₁, hy₁, hk₁, ht₁⟩ := h₁
  obtain ⟨hn₂, hz₂, hy₂, hk₂, ht₂⟩ := h₂
  refine ⟨mul_mem hn₁ hn₂, ?_, ?_, ?_, ?_⟩
  · calc g₁ * g₂ * S.z * (g₁ * g₂)⁻¹ = g₁ * (g₂ * S.z * g₂⁻¹) * g₁⁻¹ := by group
      _ = S.z := by rw [hz₂, hz₁]
  · calc g₁ * g₂ * I.yi * (g₁ * g₂)⁻¹ = g₁ * (g₂ * I.yi * g₂⁻¹) * g₁⁻¹ := by group
      _ = I.yi := by rw [hy₂, hy₁]
  · calc g₁ * g₂ * I.ki * (g₁ * g₂)⁻¹ = g₁ * (g₂ * I.ki * g₂⁻¹) * g₁⁻¹ := by group
      _ = I.ki := by rw [hk₂, hk₁]
  · calc g₁ * g₂ * S.t * (g₁ * g₂)⁻¹ = g₁ * (g₂ * S.t * g₂⁻¹) * g₁⁻¹ := by group
      _ = (g₁ * S.t * g₁⁻¹) * (g₁ * I.wV (a₂, b₂, 0, d₂) * g₁⁻¹) := by rw [ht₂]; group
      _ = S.t * I.wV (a₁, b₁, 0, d₁) * I.wV (a₂, b₂, 0, d₂) := by
          rw [ht₁, I.conj_wV_of_fix hz₁ hy₁ hk₁]
      _ = S.t * I.wV (a₁ + a₂, b₁ + b₂, 0, d₁ + d₂) := by
          rw [mul_assoc, ← I.wV_add]
          rfl

theorem d_rels {d : X} (hd : d ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X))
    (hdz : d * S.z * d⁻¹ = I.yi) (hdy : d * I.yi * d⁻¹ = S.z * I.yi) :
    d⁻¹ * I.yi * d = S.z ∧ d⁻¹ * S.z * d = S.z * I.yi ∧ d * (S.z * I.yi) * d⁻¹ = S.z ∧
      d * S.t * d⁻¹ = S.t ∧ d⁻¹ * S.t * d = S.t ∧ d⁻¹ * I.ki * d = I.ki ∧
      d * I.ki * d⁻¹ = I.ki := by
  have hzy : S.z * I.yi = I.yi * S.z := S.z_comm_of_mem_T I.yi_mem.1
  have hdk := I.conj_ki_of_mem_NC hd
  have hdt : d * S.t * d⁻¹ = S.t := by rw [mem_centralizer_singleton_iff.mp hd.2]; group
  have h3 : d * (S.z * I.yi) * d⁻¹ = S.z := by
    calc d * (S.z * I.yi) * d⁻¹ = d * S.z * d⁻¹ * (d * I.yi * d⁻¹) := by group
      _ = I.yi * I.yi * S.z := by rw [hdz, hdy, hzy, mul_assoc]
      _ = S.z := by rw [← pow_two, I.yi_sq, one_mul]
  refine ⟨?_, ?_, h3, hdt, ?_, ?_, hdk⟩
  · calc d⁻¹ * I.yi * d = d⁻¹ * (d * S.z * d⁻¹) * d := by rw [hdz]
      _ = S.z := by group
  · calc d⁻¹ * S.z * d = d⁻¹ * (d * (S.z * I.yi) * d⁻¹) * d := by rw [h3]
      _ = S.z * I.yi := by group
  · calc d⁻¹ * S.t * d = d⁻¹ * (d * S.t * d⁻¹) * d := by rw [hdt]
      _ = S.t := by group
  · calc d⁻¹ * I.ki * d = d⁻¹ * (d * I.ki * d⁻¹) * d := by rw [hdk]
      _ = I.ki := by group

theorem caseI_of_realizes {g : X} {a b : Fin 2} (h : I.Realizes g a b 0) (hab : a = 1 ∨ b = 1) :
    I.CaseI := by
  obtain ⟨d, hd, hdz, hdy⟩ := I.exists_d
  obtain ⟨hdyi, hdzi, hdzy, hdt, hdti, hdki, hdk⟩ := I.d_rels hd hdz hdy
  obtain ⟨hn, hz, hy, hk, ht⟩ := h
  have hfix := I.conj_wV_of_fix hz hy hk
  have hdN := hd.1
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · simp at hab
  ·
    have ht' : g * S.t * g⁻¹ = S.t * I.yi := by rw [ht]; simp [wV]
    refine ⟨d⁻¹ * g * d, mul_mem (mul_mem (inv_mem hdN) hn) hdN, ?_, ?_, ?_, ?_⟩
    · calc d⁻¹ * g * d * S.t * (d⁻¹ * g * d)⁻¹ = d⁻¹ * (g * (d * S.t * d⁻¹) * g⁻¹) * d := by
            group
        _ = (d⁻¹ * S.t * d) * (d⁻¹ * I.yi * d) := by rw [hdt, ht']; group
        _ = S.t * S.z := by rw [hdti, hdyi]
    · calc d⁻¹ * g * d * S.z * (d⁻¹ * g * d)⁻¹ = d⁻¹ * (g * (d * S.z * d⁻¹) * g⁻¹) * d := by
            group
        _ = S.z := by rw [hdz, hy, hdyi]
    · calc d⁻¹ * g * d * I.yi * (d⁻¹ * g * d)⁻¹ = d⁻¹ * (g * (d * I.yi * d⁻¹) * g⁻¹) * d := by
            group
        _ = d⁻¹ * (g * S.z * g⁻¹ * (g * I.yi * g⁻¹)) * d := by rw [hdy]; group
        _ = (d⁻¹ * S.z * d) * (d⁻¹ * I.yi * d) := by rw [hz, hy]; group
        _ = I.yi := by
            rw [hdzi, hdyi, mul_assoc, ← S.z_comm_of_mem_T I.yi_mem.1, ← mul_assoc, ← pow_two,
              S.z_sq, one_mul]
    · calc d⁻¹ * g * d * I.ki * (d⁻¹ * g * d)⁻¹ = d⁻¹ * (g * (d * I.ki * d⁻¹) * g⁻¹) * d := by
            group
        _ = I.ki := by rw [hdk, hk, hdki]
  ·
    refine ⟨g, hn, ?_, hz, hy, hk⟩
    rw [ht]; simp [wV]
  ·
    have ht' : g * S.t * g⁻¹ = S.t * (S.z * I.yi) := by rw [ht]; simp [wV]
    refine ⟨d * g * d⁻¹, mul_mem (mul_mem hdN hn) (inv_mem hdN), ?_, ?_, ?_, ?_⟩
    · calc d * g * d⁻¹ * S.t * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * S.t * d) * g⁻¹) * d⁻¹ := by
            group
        _ = (d * S.t * d⁻¹) * (d * (S.z * I.yi) * d⁻¹) := by rw [hdti, ht']; group
        _ = S.t * S.z := by rw [hdt, hdzy]
    · calc d * g * d⁻¹ * S.z * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * S.z * d) * g⁻¹) * d⁻¹ := by
            group
        _ = d * (g * S.z * g⁻¹ * (g * I.yi * g⁻¹)) * d⁻¹ := by rw [hdzi]; group
        _ = S.z := by rw [hz, hy, hdzy]
    · calc d * g * d⁻¹ * I.yi * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * I.yi * d) * g⁻¹) * d⁻¹ := by
            group
        _ = I.yi := by rw [hdyi, hz, hdz]
    · calc d * g * d⁻¹ * I.ki * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * I.ki * d) * g⁻¹) * d⁻¹ := by
            group
        _ = I.ki := by rw [hdki, hk, hdk]

theorem conj_t_eq (hO : S.Fus) {n : X} (hn : n ∈ normalizer (I.E : Set X)) :
    ∃ a b d : Fin 2, n * S.t * n⁻¹ = S.t * I.wV (a, b, 0, d) := by
  obtain ⟨w, hw⟩ := I.eq_wV (I.conj_wV_mem hn (0, 0, 1, 0))
  have htw : I.wV (0, 0, 1, 0) = S.t := by simp [wV]
  rw [htw] at hw
  have hc : ConjTo S.t (I.wV w) := hw ▸ ⟨n, rfl⟩
  rw [I.conjTo_wV_iff hO] at hc
  obtain ⟨a, b, c, d⟩ := w
  simp only at hc
  subst hc
  refine ⟨a, b, d, ?_⟩
  rw [hw, show ((a, b, (1 : Fin 2), d) : V4) = addV (0, 0, 1, 0) (a, b, 0, d) by
    simp [addV], I.wV_add, htw]

theorem conj_E0 (hO : S.Fus) {n : X} (hn : n ∈ normalizer (I.E : Set X)) (a b d : Fin 2) :
    ∃ a' b' d' : Fin 2, n * I.wV (a, b, 0, d) * n⁻¹ = I.wV (a', b', 0, d') := by
  obtain ⟨w, hw⟩ := I.eq_wV (I.conj_wV_mem hn (a, b, 0, d))
  have hc : ¬ ConjTo S.t (I.wV w) := by
    rw [← hw, conjTo_conj_iff, I.conjTo_wV_iff hO]
    simp
  rw [I.conjTo_wV_iff hO] at hc
  obtain ⟨a', b', c, d'⟩ := w
  simp only at hc
  have : c = 0 := by
    rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
    · rfl
    · exact absurd rfl hc
  subst this
  exact ⟨a', b', d', hw⟩

theorem k_fixed (H : S.Sec6Hyp T₁) {n : X} (hn : n ∈ normalizer (I.E : Set X)) :
    n * I.ki * n⁻¹ = I.ki := by
  obtain ⟨v, hvT, hvt, hvz, hvy, hvk⟩ := I.exists_v H
  have hvN := I.T₁_le H hvT
  have hv : I.Realizes v 0 0 1 := ⟨hvN, hvz, hvy, hvk, by rw [hvt]; simp [wV]⟩
  by_cases hI : I.CaseI
  · obtain ⟨g, hg, hgt, hgz, hgy, hgk⟩ := hI
    have hgR : I.Realizes g 1 0 0 := ⟨hg, hgz, hgy, hgk, by rw [hgt]; simp [wV]⟩
    obtain ⟨d, hd, hdz, hdy⟩ := I.exists_d
    obtain ⟨hdyi, hdzi, hdzy, hdt, hdti, hdki, hdk⟩ := I.d_rels hd hdz hdy
    have hyR : I.Realizes (d * g * d⁻¹) 0 1 0 := by
      refine ⟨mul_mem (mul_mem hd.1 hg) (inv_mem hd.1), ?_, ?_, ?_, ?_⟩
      · calc d * g * d⁻¹ * S.z * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * S.z * d) * g⁻¹) * d⁻¹ := by
              group
          _ = d * (g * S.z * g⁻¹ * (g * I.yi * g⁻¹)) * d⁻¹ := by rw [hdzi]; group
          _ = S.z := by rw [hgz, hgy, hdzy]
      · calc d * g * d⁻¹ * I.yi * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * I.yi * d) * g⁻¹) * d⁻¹ := by
              group
          _ = I.yi := by rw [hdyi, hgz, hdz]
      · calc d * g * d⁻¹ * I.ki * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * I.ki * d) * g⁻¹) * d⁻¹ := by
              group
          _ = I.ki := by rw [hdki, hgk, hdk]
      · calc d * g * d⁻¹ * S.t * (d * g * d⁻¹)⁻¹ = d * (g * (d⁻¹ * S.t * d) * g⁻¹) * d⁻¹ := by
              group
          _ = (d * S.t * d⁻¹) * (d * S.z * d⁻¹) := by rw [hdti, hgt]; group
          _ = S.t * I.wV (0, 1, 0, 0) := by rw [hdt, hdz]; simp [wV]
    have hall : ∀ a b c : Fin 2, ∃ g', I.Realizes g' a b c := by
      intro a b c
      have h1 : ∀ a : Fin 2, ∃ g', I.Realizes g' a 0 0 := fun a => by
        rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
        · exact ⟨1, one_mem _, by group, by group, by group, by simp [wV]⟩
        · exact ⟨g, hgR⟩
      have h2 : ∀ b : Fin 2, ∃ g', I.Realizes g' 0 b 0 := fun b => by
        rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
        · exact ⟨1, one_mem _, by group, by group, by group, by simp [wV]⟩
        · exact ⟨_, hyR⟩
      have h3 : ∀ c : Fin 2, ∃ g', I.Realizes g' 0 0 c := fun c => by
        rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
        · exact ⟨1, one_mem _, by group, by group, by group, by simp [wV]⟩
        · exact ⟨v, hv⟩
      obtain ⟨g₁, hg₁⟩ := h1 a
      obtain ⟨g₂, hg₂⟩ := h2 b
      obtain ⟨g₃, hg₃⟩ := h3 c
      have := (hg₁.mul I hg₂).mul I hg₃
      simp only [add_zero, zero_add] at this
      exact ⟨_, this⟩
    obtain ⟨a, b, c, hnt⟩ := I.conj_t_eq H.fus hn
    obtain ⟨g', hn', hz', hy', hk', ht'⟩ := hall a b c
    have hm : g'⁻¹ * n ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X) := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hn') hn, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hfix := I.conj_wV_of_fix hz' hy' hk' a b c
      have : g'⁻¹ * (S.t * I.wV (a, b, 0, c)) * g' = S.t := by
        have e1 : g'⁻¹ * S.t * g' = S.t * I.wV (a, b, 0, c) := by
          calc g'⁻¹ * S.t * g' = g'⁻¹ * (S.t * I.wV (a, b, 0, c) * I.wV (a, b, 0, c)) * g' := by
                rw [mul_assoc S.t, ← pow_two, I.sq_eq_one (I.wV_mem _), mul_one]
            _ = g'⁻¹ * (g' * S.t * g'⁻¹ * (g' * I.wV (a, b, 0, c) * g'⁻¹)) * g' := by
                rw [ht', hfix]
            _ = S.t * I.wV (a, b, 0, c) := by group
        have e2 : g'⁻¹ * I.wV (a, b, 0, c) * g' = I.wV (a, b, 0, c) := by
          calc g'⁻¹ * I.wV (a, b, 0, c) * g' = g'⁻¹ * (g' * I.wV (a, b, 0, c) * g'⁻¹) * g' := by
                rw [hfix]
            _ = I.wV (a, b, 0, c) := by group
        calc g'⁻¹ * (S.t * I.wV (a, b, 0, c)) * g' =
            (g'⁻¹ * S.t * g') * (g'⁻¹ * I.wV (a, b, 0, c) * g') := by group
          _ = S.t := by
              rw [e1, e2, mul_assoc, ← pow_two, I.sq_eq_one (I.wV_mem _), mul_one]
      calc g'⁻¹ * n * S.t = g'⁻¹ * (n * S.t * n⁻¹) * g' * (g'⁻¹ * n) := by group
        _ = S.t * (g'⁻¹ * n) := by rw [hnt, this]
    have := I.conj_ki_of_mem_NC hm
    calc n * I.ki * n⁻¹ = g' * ((g'⁻¹ * n) * I.ki * (g'⁻¹ * n)⁻¹) * g'⁻¹ := by group
      _ = I.ki := by rw [this, hk']
  ·
    obtain ⟨p₁, p₂, p₄, hf⟩ := I.conj_E0 H.fus hn 0 0 1
    have hkw : I.wV (0, 0, 0, 1) = I.ki := by simp [wV]
    rw [hkw] at hf
    have hR : I.Realizes (n * v * n⁻¹) p₁ p₂ p₄ := by
      have hfixv := I.conj_wV_of_fix hvz hvy hvk
      have hE0 : ∀ a b d : Fin 2, n * v * n⁻¹ * I.wV (a, b, 0, d) * (n * v * n⁻¹)⁻¹ =
          I.wV (a, b, 0, d) := by
        intro a b d
        obtain ⟨a', b', d', h'⟩ := I.conj_E0 H.fus (inv_mem hn) a b d
        simp only [inv_inv] at h'
        calc n * v * n⁻¹ * I.wV (a, b, 0, d) * (n * v * n⁻¹)⁻¹ =
            n * (v * (n⁻¹ * I.wV (a, b, 0, d) * n) * v⁻¹) * n⁻¹ := by group
          _ = I.wV (a, b, 0, d) := by rw [h', hfixv, ← h']; group
      refine ⟨mul_mem (mul_mem hn hvN) (inv_mem hn), ?_, ?_, ?_, ?_⟩
      · have := hE0 1 0 0; simpa [wV] using this
      · have := hE0 0 1 0; simpa [wV] using this
      · have := hE0 0 0 1; simpa [wV] using this
      · obtain ⟨a, b, d, hnt⟩ := I.conj_t_eq H.fus (inv_mem hn)
        simp only [inv_inv] at hnt
        calc n * v * n⁻¹ * S.t * (n * v * n⁻¹)⁻¹ = n * (v * (n⁻¹ * S.t * n) * v⁻¹) * n⁻¹ := by
              group
          _ = n * (v * S.t * v⁻¹ * (v * I.wV (a, b, 0, d) * v⁻¹)) * n⁻¹ := by rw [hnt]; group
          _ = n * (S.t * I.wV (a, b, 0, d)) * n⁻¹ * (n * I.ki * n⁻¹) := by
              rw [hvt, hfixv]
              have hc : I.ki * I.wV (a, b, 0, d) = I.wV (a, b, 0, d) * I.ki :=
                I.comm I.ki_mem_E (I.wV_mem _)
              rw [mul_assoc S.t, hc]; group
          _ = S.t * I.wV (p₁, p₂, 0, p₄) := by
              rw [← hnt, hf]; group
    by_contra hne
    have hp : p₁ = 1 ∨ p₂ = 1 := by
      by_contra hp
      push Not at hp
      have h1 : p₁ = 0 := by
        rcases Fin.exists_fin_two.mp ⟨p₁, rfl⟩ with rfl | rfl
        · rfl
        · exact absurd rfl hp.1
      have h2 : p₂ = 0 := by
        rcases Fin.exists_fin_two.mp ⟨p₂, rfl⟩ with rfl | rfl
        · rfl
        · exact absurd rfl hp.2
      subst h1 h2
      rcases Fin.exists_fin_two.mp ⟨p₄, rfl⟩ with rfl | rfl
      · have : n * I.ki * n⁻¹ = 1 := by rw [hf]; simp [wV]
        apply (show I.ki ≠ 1 from fun h1 => by
          have := I.wV_injective (hkw.trans (h1.trans I.wV_zero.symm))
          simp at this)
        calc I.ki = n⁻¹ * (n * I.ki * n⁻¹) * n := by group
          _ = 1 := by rw [this]; group
      · exact hne (by rw [hf, hkw])
    have hR' : I.Realizes (n * v * n⁻¹ * v ^ (p₄ : ℕ)) p₁ p₂ 0 := by
      rcases Fin.exists_fin_two.mp ⟨p₄, rfl⟩ with rfl | rfl
      · simpa using hR
      · have := hR.mul I hv
        simpa using this
    exact hI (I.caseI_of_realizes hR' hp)

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
