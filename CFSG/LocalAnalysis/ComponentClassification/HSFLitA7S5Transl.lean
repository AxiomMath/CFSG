module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Orbit

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def transCols (a b : Fin 2) : Fin 4 → V4 :=
  ![(1, 0, 0, 0), (0, 1, 0, 0), (a, b, 1, 0), (0, 0, 0, 1)]

@[expose] def cls5 (a b : Fin 2) (σ₁ σ₂ : V4) : Fin 4 → V4 :=
  comp (transCols a b) (sigCols σ₁ σ₂)

theorem dCols_pow_three : ∀ i, comp dCols (comp dCols dCols) i = bas i := by decide

theorem transCols_sq : ∀ a b : Fin 2, ∀ i, comp (transCols a b) (transCols a b) i = bas i := by
  decide

theorem transCols_conj_d : ∀ i, comp (comp dCols (transCols 1 0)) (comp dCols dCols) i =
    transCols 0 1 i := by decide

theorem transCols_pw : ∀ a b : Fin 2, ∀ i,
    comp (pw (transCols 1 0) a) (pw (transCols 0 1) b) i = transCols a b i := by decide

theorem transCols_t : ∀ a b : Fin 2, lin (transCols a b) (a, b, 1, 0) = (0, 0, 1, 0) := by decide

theorem cls5_three : ∀ a b : Fin 2, ∀ σ₁ σ₂ : V4, cls5 a b σ₁ σ₂ 3 = (0, 0, 0, 1) := by decide

theorem fixed_d_tz : ∀ v : V4, lin dCols v ≠ v ∨ lin (transCols 1 0) v ≠ v ∨
    v = (0, 0, 0, 0) ∨ v = (0, 0, 0, 1) := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem T₂of_le_normalizer (I : S.Inst) : S.T₂of T₁ ≤ normalizer (I.E : Set X) := by
  intro g hg
  rcases I.yi_or with h | h
  · show g ∈ normalizer (S.E I.yi : Set X)
    rw [h]; exact H.T₂of_le_normalizer_E₂ hg
  · show g ∈ normalizer (S.E I.yi : Set X)
    rw [h]; exact (mem_inf.mp hg).2

theorem conj_ki_w₀ (I : S.Inst) {w₀ : X} (hw₀ : w₀ ∈ S.T₂of T₁) (hw₀T : w₀ ∉ S.data.T) :
    w₀ * I.ki * w₀⁻¹ = I.ki := by
  have hw₀N := H.le_normalizer (T₂of_le hw₀)
  have hwt := H.conj_w₀_t hw₀ hw₀T
  have hwz : w₀ * S.z * w₀⁻¹ = S.z := S.conj_z_eq hw₀N
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB := I.ki_mem_B
  have hki := S.conj_mem_B hw₀N hkB
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hnc : ¬ ConjTo S.t (w₀ * I.ki * w₀⁻¹) := by
    rw [conjTo_conj_iff, show I.ki = I.wV (0, 0, 0, 1) by simp [Inst.wV], I.conjTo_wV_iff H.fus]
    decide
  obtain ⟨v, hv⟩ := I.eq_wV (I.conj_wV_mem (H.T₂of_le_normalizer I hw₀) (0, 0, 0, 1))
  rw [show I.wV (0, 0, 0, 1) = I.ki by simp [Inst.wV]] at hv
  have hvB : I.wV v ∈ S.B := hv ▸ hki
  rw [I.wV_mem_B_iff] at hvB
  rw [hv, I.conjTo_wV_iff H.fus] at hnc
  obtain ⟨a, b, c, e⟩ := v
  simp only at hvB hnc
  subst hvB
  have hc : c = 0 := by
    rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
    · rfl
    · exact absurd rfl hnc
  subst hc
  have he : e = 1 := by
    rcases Fin.exists_fin_two.mp ⟨e, rfl⟩ with rfl | rfl
    · exfalso
      have h1 : I.ki = w₀⁻¹ * I.wV (a, 0, 0, 0) * w₀ := by rw [← hv]; group
      have h2 : w₀⁻¹ * I.wV (a, 0, 0, 0) * w₀ = I.wV (a, 0, 0, 0) := by
        have : I.wV (a, 0, 0, 0) = S.z ^ (a : ℕ) := by simp [Inst.wV]
        rw [this]
        calc w₀⁻¹ * S.z ^ (a : ℕ) * w₀ = w₀⁻¹ * (w₀ * S.z * w₀⁻¹) ^ (a : ℕ) * w₀ := by rw [hwz]
          _ = S.z ^ (a : ℕ) := by rw [conj_pow]; group
      rw [h2, show I.ki = I.wV (0, 0, 0, 1) by simp [Inst.wV]] at h1
      have := I.wV_injective h1
      simp at this
    · rfl
  subst he
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
  · rw [hv]; simp [Inst.wV]
  · exfalso
    have hfix : w₀ * (S.t * I.ki) * w₀⁻¹ = S.t * I.ki := by
      have e1 : w₀ * (S.t * I.ki) * w₀⁻¹ = (w₀ * S.t * w₀⁻¹) * (w₀ * I.ki * w₀⁻¹) := by group
      rw [e1, hwt, hv]
      simp only [Inst.wV, Fin.val_one, pow_one, Fin.val_zero, pow_zero, mul_one]
      calc S.t * S.z * (S.z * I.ki) = S.t * (S.z * S.z) * I.ki := by group
        _ = S.t * I.ki := by rw [← pow_two, S.z_sq, mul_one]
    have htkB : S.t * I.ki ∈ S.B := mul_mem htB hkB
    have htkc : ConjTo S.t (S.t * I.ki) := by
      rw [show S.t * I.ki = I.wV (0, 0, 1, 1) by simp [Inst.wV], I.conjTo_wV_iff H.fus]
    obtain ⟨h, hh, hht⟩ := H.exists_conj_T₁ htkB htkc
    have hhN := H.le_normalizer hh
    have hC : h⁻¹ * w₀ * h ∈ T₁ ⊓ centralizer ({S.t} : Set X) := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hh) (T₂of_le hw₀)) hh, ?_⟩
      rw [mem_centralizer_singleton_iff]
      calc h⁻¹ * w₀ * h * S.t = h⁻¹ * (w₀ * (h * S.t * h⁻¹) * w₀⁻¹) * w₀ * h := by group
        _ = h⁻¹ * (h * S.t * h⁻¹) * w₀ * h := by rw [hht, hfix]
        _ = S.t * (h⁻¹ * w₀ * h) := by group
    rw [H.inf_centralizer] at hC
    apply hw₀T
    have := S.data.conj_mem_T hhN hC
    simpa [mul_assoc] using this

theorem conj_E00 (I : S.Inst) {n : X} (hn : n ∈ normalizer (I.E : Set X)) (a b : Fin 2) :
    ∃ a' b' : Fin 2, n * I.wV (a, b, 0, 0) * n⁻¹ = I.wV (a', b', 0, 0) := by
  have hO : ∀ v : V4, v.2.2.1 = 1 → v.2.2.2 = 0 →
      ∃ v' : V4, v'.2.2.1 = 1 ∧ v'.2.2.2 = 0 ∧ n * I.wV v * n⁻¹ = I.wV v' := by
    intro v h1 h2
    have hv : I.wV v ∈ I.orbitN := (H.mem_orbitN_iff I v).mpr ⟨h1, h2⟩
    obtain ⟨v', hv', he⟩ := I.eq_wV_of_mem_orbitN H.fus (I.conj_mem_orbitN hn hv)
    exact ⟨v', hv', ((H.mem_orbitN_iff I v').mp (he ▸ I.conj_mem_orbitN hn hv)).2, he⟩
  obtain ⟨p, hp1, hp2, hp⟩ := hO (0, 0, 1, 0) rfl rfl
  obtain ⟨q, hq1, hq2, hq⟩ := hO (a, b, 1, 0) rfl rfl
  have e : I.wV (a, b, 0, 0) = I.wV (0, 0, 1, 0) * I.wV (a, b, 1, 0) := by
    rw [← I.wV_add]; simp [addV]
  refine ⟨p.1 + q.1, p.2.1 + q.2.1, ?_⟩
  have e2 : n * I.wV (a, b, 0, 0) * n⁻¹ =
      (n * I.wV (0, 0, 1, 0) * n⁻¹) * (n * I.wV (a, b, 1, 0) * n⁻¹) := by rw [e]; group
  rw [e2, hp, hq, ← I.wV_add]
  obtain ⟨p1, p2, p3, p4⟩ := p
  obtain ⟨q1, q2, q3, q4⟩ := q
  simp only at hp1 hp2 hq1 hq2
  subst hp1 hp2 hq1 hq2
  simp [addV]

theorem exists_tz (I : S.Inst) : ∃ w ∈ S.T₂of T₁, w ∉ S.data.T ∧ I.Mat w (transCols 1 0) := by
  obtain ⟨w₀, hw₀, hw₀T⟩ := H.exists_w₀
  have hw₀N := H.le_normalizer (T₂of_le hw₀)
  have hw₀E := H.T₂of_le_normalizer I hw₀
  have hwt := H.conj_w₀_t hw₀ hw₀T
  have hwz : w₀ * S.z * w₀⁻¹ = S.z := S.conj_z_eq hw₀N
  have hwk := H.conj_ki_w₀ I hw₀ hw₀T
  obtain ⟨a', b', hy⟩ := H.conj_E00 I hw₀E 0 1
  rw [show I.wV (0, 1, 0, 0) = I.yi by simp [Inst.wV]] at hy
  have hyB : w₀ * I.yi * w₀⁻¹ ∉ S.B := fun h => I.yi_not_mem_B (by
    have := S.conj_mem_B (inv_mem hw₀N) h
    simpa [mul_assoc] using this)
  rw [hy, I.wV_mem_B_iff] at hyB
  have hb' : b' = 1 := by
    rcases Fin.exists_fin_two.mp ⟨b', rfl⟩ with rfl | rfl
    · exact absurd rfl hyB
    · rfl
  subst hb'
  have htz : S.t * S.z = I.wV (1, 0, 1, 0) := by
    simp [Inst.wV, S.z_comm_of_mem_T S.data.t_mem_T]
  have hxN : S.x ∈ S.T₂of T₁ := H.T_le_T₂of S.x_mem.1
  have hxT : S.x ∈ S.data.T := S.x_mem.1
  have hxt : S.x * S.t * S.x⁻¹ = S.t := by rw [S.data.commute_t hxT]; group
  have hxz : S.x * S.z * S.x⁻¹ = S.z := by rw [← S.z_comm_of_mem_T hxT]; group
  have hxk : S.x * I.ki * S.x⁻¹ = I.ki := by rw [← S.central_of_mem_B I.ki_mem_B hxT]; group
  rcases Fin.exists_fin_two.mp ⟨a', rfl⟩ with rfl | rfl
  · refine ⟨w₀, hw₀, hw₀T, Inst.Mat.mk (I := I) hw₀E ?_ ?_ ?_ ?_⟩
    · rw [hwz]; simp [transCols, Inst.wV]
    · rw [hy]; rfl
    · rw [hwt, htz]; rfl
    · rw [hwk]; simp [transCols, Inst.wV]
  · refine ⟨w₀ * S.x, mul_mem hw₀ hxN, fun h => hw₀T ?_, Inst.Mat.mk (I := I) (mul_mem hw₀E
      (H.T₂of_le_normalizer I hxN)) ?_ ?_ ?_ ?_⟩
    · have := mul_mem h (inv_mem hxT)
      rwa [mul_inv_cancel_right] at this
    · calc w₀ * S.x * S.z * (w₀ * S.x)⁻¹ = w₀ * (S.x * S.z * S.x⁻¹) * w₀⁻¹ := by group
        _ = I.wV (transCols 1 0 0) := by rw [hxz, hwz]; simp [transCols, Inst.wV]
    · calc w₀ * S.x * I.yi * (w₀ * S.x)⁻¹ = w₀ * (S.x * I.yi * S.x⁻¹) * w₀⁻¹ := by group
        _ = (w₀ * S.z * w₀⁻¹) * (w₀ * I.yi * w₀⁻¹) := by rw [I.x_conj_yi]; group
        _ = I.wV (transCols 1 0 1) := by
            rw [hwz, hy, show S.z = I.wV (1, 0, 0, 0) by simp [Inst.wV], ← I.wV_add]
            rfl
    · calc w₀ * S.x * S.t * (w₀ * S.x)⁻¹ = w₀ * (S.x * S.t * S.x⁻¹) * w₀⁻¹ := by group
        _ = I.wV (transCols 1 0 2) := by rw [hxt, hwt, htz]; rfl
    · calc w₀ * S.x * I.ki * (w₀ * S.x)⁻¹ = w₀ * (S.x * I.ki * S.x⁻¹) * w₀⁻¹ := by group
        _ = I.wV (transCols 1 0 3) := by rw [hxk, hwk]; simp [transCols, Inst.wV]

theorem exists_transl (I : S.Inst) : ∀ a b : Fin 2, ∃ τ, I.Mat τ (transCols a b) := by
  obtain ⟨w, -, -, hw⟩ := H.exists_tz I
  obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
  have hdM : I.Mat d dCols := ⟨hd.1, hdc⟩
  have hdi : I.Mat d⁻¹ (comp dCols dCols) := hdM.inv dCols_pow_three
  have hw' : I.Mat (d * w * d⁻¹) (transCols 0 1) := by
    have := (hdM.mul hw).mul hdi
    rwa [show comp (comp dCols (transCols 1 0)) (comp dCols dCols) = transCols 0 1 from
      funext transCols_conj_d] at this
  intro a b
  have h := (hw.pw a).mul (hw'.pw b)
  rw [show comp (pw (transCols 1 0) a) (pw (transCols 0 1) b) = transCols a b from
    funext (transCols_pw a b)] at h
  exact ⟨_, h⟩

theorem classify (I : S.Inst) {n : X} (hn : n ∈ normalizer (I.E : Set X)) :
    ∃ a b : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three, σ₁ ≠ σ₂ ∧ I.Mat n (cls5 a b σ₁ σ₂) := by
  have htO : n * S.t * n⁻¹ ∈ I.orbitN := ⟨n, hn, rfl⟩
  obtain ⟨v, hv1, hv⟩ := I.eq_wV_of_mem_orbitN H.fus htO
  have hv2 := ((H.mem_orbitN_iff I v).mp (hv ▸ htO)).2
  obtain ⟨a, b, c, e⟩ := v
  simp only at hv1 hv2
  subst hv1 hv2
  obtain ⟨τ, hτ⟩ := H.exists_transl I a b
  have hτi : I.Mat τ⁻¹ (transCols a b) := hτ.inv (transCols_sq a b)
  have hs : τ⁻¹ * n ∈ normalizer (I.E : Set X) := mul_mem hτi.1 hn
  have hst : τ⁻¹ * n ∈ centralizer ({S.t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have e1 : τ⁻¹ * n * S.t * (τ⁻¹ * n)⁻¹ = S.t := by
      calc τ⁻¹ * n * S.t * (τ⁻¹ * n)⁻¹ = τ⁻¹ * (n * S.t * n⁻¹) * τ⁻¹⁻¹ := by group
        _ = S.t := by
            rw [hv, hτi.conj, transCols_t]
            simp [Inst.wV]
    calc τ⁻¹ * n * S.t = τ⁻¹ * n * S.t * (τ⁻¹ * n)⁻¹ * (τ⁻¹ * n) := by group
      _ = S.t * (τ⁻¹ * n) := by rw [e1]
  obtain ⟨σ₁, h₁, σ₂, h₂, h12, hσ⟩ := I.cols_of_mem_NC H.fus ⟨_, hs⟩ hst
  refine ⟨a, b, σ₁, h₁, σ₂, h₂, h12, ?_⟩
  have := hτ.mul (⟨hs, hσ⟩ : I.Mat (τ⁻¹ * n) (sigCols σ₁ σ₂))
  rwa [mul_inv_cancel_left] at this

theorem k_fixed (I : S.Inst) {n : X} (hn : n ∈ normalizer (I.E : Set X)) :
    n * I.ki * n⁻¹ = I.ki := by
  obtain ⟨a, b, σ₁, -, σ₂, -, -, hM⟩ := H.classify I hn
  rw [hM.conj_ki, cls5_three]
  simp [Inst.wV]

theorem zy_normal (I : S.Inst) {n : X} (hn : n ∈ normalizer (I.E : Set X)) :
    n * S.z * n⁻¹ ∈ closure {S.z, I.yi} ∧ n * I.yi * n⁻¹ ∈ closure {S.z, I.yi} := by
  have hmem : ∀ a b : Fin 2, I.wV (a, b, 0, 0) ∈ closure {S.z, I.yi} := fun a b => by
    simp only [Inst.wV, Fin.val_zero, pow_zero, mul_one]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
  obtain ⟨p, q, hp⟩ := H.conj_E00 I hn 1 0
  obtain ⟨p', q', hq⟩ := H.conj_E00 I hn 0 1
  rw [show I.wV (1, 0, 0, 0) = S.z by simp [Inst.wV]] at hp
  rw [show I.wV (0, 1, 0, 0) = I.yi by simp [Inst.wV]] at hq
  rw [hp, hq]
  exact ⟨hmem p q, hmem p' q'⟩

theorem eq_of_fixed (I : S.Inst) {e : X} (he : e ∈ I.E)
    (hfix : ∀ n ∈ normalizer (I.E : Set X), n * e * n⁻¹ = e) : e = 1 ∨ e = I.ki := by
  obtain ⟨v, rfl⟩ := I.eq_wV he
  obtain ⟨w, -, -, hw⟩ := H.exists_tz I
  obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
  have hdM : I.Mat d dCols := ⟨hd.1, hdc⟩
  have h1 : lin dCols v = v := I.wV_injective (by rw [← hdM.conj]; exact hfix d hd.1)
  have h2 : lin (transCols 1 0) v = v := I.wV_injective (by rw [← hw.conj]; exact hfix w hw.1)
  rcases (((fixed_d_tz v).resolve_left (not_not.mpr h1)).resolve_left (not_not.mpr h2)) with
    h | h <;> rw [h]
  · left; simp [Inst.wV]
  · right; simp [Inst.wV]

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
