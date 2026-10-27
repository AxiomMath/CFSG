module

public import CFSG.GH74.GLS.Stage4.T2P71BothB
public import CFSG.GH74.GLS.IVK.Proofs2.NatModFinal
public import CFSG.GH74.GLS.Stage4.RestX2Q3
public import CFSG.GH74.GLS.Stage4.T2P71Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement Pointwise
open CFSG.GH74.GLS.Stage4.Rest.T6 CFSG.GH74.GLS.Stage4.Rest.T6.P71

section Aux

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem relIndex_eq_of_card (h : T6Ctx N u p) {m : ℕ} (hn : N.q₂ = p ^ m)
    (hcard : Nat.card ↥(R₂ N p) = N.q₂ ^ 3) : N.X₂.relIndex (R₂ N p) = p ^ (2 * m) := by
  have h1 := Subgroup.relIndex_mul_card N.X₂ (R₂ N p)
  rw [inf_eq_left.2 (X₂_le_R₂ h), h.sec5.loc.card_X₂, hcard] at h1
  have hq : 0 < N.q₂ := by have := h.sec5.loc.q₂_ge; omega
  have h2 : N.X₂.relIndex (R₂ N p) = N.q₂ ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [h1]; ring
  rw [h2, hn, ← pow_mul, mul_comm]

omit [Finite G] in
theorem winv_conj {K : Subgroup G} {w z : G} (hw : w ∈ K) (hsq : w * w = z)
    (hz : ∀ x ∈ K, x * z = z * x) : ∀ x ∈ K, w⁻¹ * x * w = w * x * w⁻¹ := by
  intro x hx
  have hc : w * x * w⁻¹ ∈ K := K.mul_mem (K.mul_mem hw hx) (K.inv_mem hw)
  have e : w⁻¹ * x * w = (w * w)⁻¹ * (w * x * w⁻¹) * (w * w) := by group
  rw [e, hsq]
  have := hz _ hc
  have hz1 : z⁻¹ * (w * x * w⁻¹) * z = w * x * w⁻¹ := by
    calc z⁻¹ * (w * x * w⁻¹) * z = z⁻¹ * ((w * x * w⁻¹) * z) := by group
      _ = z⁻¹ * (z * (w * x * w⁻¹)) := by rw [this]
      _ = w * x * w⁻¹ := by group
  exact hz1

end Aux

theorem p71Both_proved : P71Both := by
  intro G _ _ Gs _ n N u hE hnotsyl hc1 hc2 hD1 hD2
  have h := hE.ctx
  have h' := hE.swap.ctx
  have h11b : IVK_11_1b_nat := ivk_11_1b_nat
  have hq : N.q₁ = N.q₂ := hE.q₁.trans hE.q₂.symm
  have hloc := h.sec5.loc
  obtain ⟨hz2, hu2, hzu, -⟩ := T6.zu_facts h
  obtain ⟨v, hv, hYC⟩ := T6.P71.exists_Y h hq hc1 hD1
  have hYcard : Nat.card ↥(T6.R₂ N 3 ⊓ Subgroup.centralizer {v}) = N.q₂ := by
    rcases hv with hv | hv <;> rw [hv]
    · exact (T6.P71.Yv_card h hc1).1
    · exact (T6.P71.Yv_card h hc1).2
  obtain ⟨hYinv, hYab, hYH, hYp⟩ := T6.P71.Yv_facts h hv
  obtain ⟨b, hb1, hb2, hbH, hbw⟩ := T6.P71.exists_vb h hv
  set Y : Subgroup G := T6.R₂ N 3 ⊓ Subgroup.centralizer {v} with hYdef
  have hYR : Y ≤ T6.R₂ N 3 := inf_le_left
  have hYv : ∀ y ∈ Y, y * v = v * y := fun y hy => Subgroup.mem_centralizer_singleton_iff.1 hy.2
  have hYX₂ : ∀ y ∈ Y, ∀ x ∈ N.X₂, x * y = y * x := by
    intro y hy x hx
    have := T6.R₂_cent h y hy.1 x hx
    calc x * y = (y * x * y⁻¹) * y := by rw [this]
      _ = y * x := by group
  have hYR' : Y ≤ T6.R₂ N.swap 3 := by
    refine T6.R_le_R₂' h' hYp (fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => hYC y hy x hx) ?_
    intro r hr
    have : N.z * r * N.z⁻¹ = r⁻¹ := hYinv r hr
    show N.z * r * N.z⁻¹ * r ∈ N.X₁
    rw [this, inv_mul_cancel]
    exact N.X₁.one_mem
  have hrel₂ : N.X₂.relIndex (T6.R₂ N 3) = 3 ^ (2 * n) := relIndex_eq_of_card h hE.q₂ hc1
  have hrel₁ : N.swap.X₂.relIndex (T6.R₂ N.swap 3) = 3 ^ (2 * n) :=
    relIndex_eq_of_card h' (show N.swap.q₂ = 3 ^ n from hE.q₁) hc2
  have hYX : ∀ y ∈ Y, y ∈ N.X₂ → y = 1 := fun y hy hyX => (T6.P71.v_fix_X h hv).2 y hyX (hYv y hy).symm
  have hYX' : ∀ y ∈ Y, y ∈ N.swap.X₂ → y = 1 := fun y hy hyX =>
    (T6.P71.v_fix_X h hv).1 y hyX (hYv y hy).symm
  have hN₂ := T6.P71.R₂_norm_E h11b h (m := n) hE.q₁ hrel₂ hYR hYC hYX (hYcard.trans hq.symm)
  have hN₁ := T6.P71.R₂_norm_E h11b h' (m := n) (show N.swap.q₁ = 3 ^ n from hE.q₂) hrel₁ hYR'
    (fun y hy x hx => hYX₂ y hy x hx) hYX' hYcard
  set E : Subgroup G := (N.X₁ ⊔ N.X₂) ⊔ Y with hEdef
  have hEswap : (N.swap.X₁ ⊔ N.swap.X₂) ⊔ Y = E := by
    show (N.X₂ ⊔ N.X₁) ⊔ Y = (N.X₁ ⊔ N.X₂) ⊔ Y
    rw [sup_comm N.X₂ N.X₁]
  have hN₁' : ∀ r ∈ T6.R₂ N.swap 3, ∀ e ∈ E, r * e * r⁻¹ ∈ E := by
    intro r hr e he
    have := hN₁ r hr e (by rw [hEswap]; exact he)
    rwa [hEswap] at this
  set M : Subgroup G := Subgroup.normalizer (E : Set G) with hMdef
  have hMmem : ∀ g : G, (∀ e ∈ E, g * e * g⁻¹ ∈ E) → g ∈ M := fun g hg =>
    Subgroup.mem_normalizer_fintype hg
  have hMuse : ∀ g ∈ M, ∀ e ∈ E, g * e * g⁻¹ ∈ E := fun g hg e he =>
    (Subgroup.mem_normalizer_iff.1 hg e).1 he
  have hHM : ∀ k ∈ N.H, k ∈ M := fun k hk => hMmem k (T6.P71.H_norm_E h hYH k hk)
  have hR₂M : ∀ r ∈ T6.R₂ N 3, r ∈ M := fun r hr => hMmem r (hN₂ r hr)
  have hR₁M : ∀ r ∈ T6.R₂ N.swap 3, r ∈ M := fun r hr => hMmem r (hN₁' r hr)
  have hwY : ∀ w : G, (w = N.w₁ ∨ w = N.w₂) → ∀ y ∈ Y, w * y * w⁻¹ ∈ M := by
    intro w hw y hy
    rcases hw with rfl | rfl
    · exact hR₂M _ (T6.R₂_norm N 3 (T6.K₁_le_M₂ h hloc.w₁_mem) hy.1)
    · exact hR₁M _ (T6.R₂_norm N.swap 3 (T6.K₁_le_M₂ h' (show N.w₂ ∈ N.swap.K₁ from hloc.w₂_mem))
        (hYR' hy))
  have hAmem : ∀ x, x ∈ Y.map (MulAut.conj b).toMonoidHom ↔ ∃ y ∈ Y, b * y * b⁻¹ = x := by
    intro x
    simp [Subgroup.mem_map]
  have hclaim : ∀ w : G, (w = N.w₁ ∨ w = N.w₂) → ∀ x ∈ Y.map (MulAut.conj b).toMonoidHom,
      b * (w * x * w⁻¹) * b⁻¹ ∈ M := by
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := (hAmem x).1 hx
    obtain ⟨k, hk, hkw⟩ := hbw w hw
    have e : b * (w * (b * y * b⁻¹) * w⁻¹) * b⁻¹ = k * (w * y * w⁻¹) * k⁻¹ := by
      calc b * (w * (b * y * b⁻¹) * w⁻¹) * b⁻¹ = (b * w * b) * y * (b * w * b)⁻¹ := by group
        _ = (k * w) * y * (k * w)⁻¹ := by rw [hkw]
        _ = k * (w * y * w⁻¹) * k⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (hHM k hk) (hwY w hw y hy)) (M.inv_mem (hHM k hk))
  have case_step : ∀ (K A A' : Subgroup G) (w w' : G), (w = N.w₁ ∨ w = N.w₂) → (w' = N.w₁ ∨ w' = N.w₂) →
      K = A ⊔ A' → w ∈ K → A ≤ K → A' ≤ K → (∀ x ∈ A', w * x * w⁻¹ ∈ A) →
      (∀ x ∈ K, w⁻¹ * x * w = w * x * w⁻¹) → (∀ x ∈ K, w' * x * w'⁻¹ = x) →
      (∀ x ∈ A, x ∈ Y.map (MulAut.conj b).toMonoidHom) → b * w * b⁻¹ ∈ M := by
    intro K A A' w w' hw hw' hK hwK hAK hA'K hswap hinv hw'K hAY
    have := weyl_step (Z := M.comap (MulAut.conj b).toMonoidHom) (K := K) (A := A) (A' := A') (w := w)
      (w' := w') hK hwK (fun x hx => by rw [hinv x (hA'K hx)]; exact hswap x hx)
      (fun x hx => hw'K x (hAK hx)) (fun x hx => hclaim w hw x (hAY x hx))
      (fun x hx => hclaim w' hw' x (hAY x hx))
    exact this
  have hX₁K : N.X₁ ≤ N.K₁ := T6.X₁_le_K₁ h
  have hX₁'K : N.X₁' ≤ N.K₁ := by rw [hloc.K₁_eq]; exact le_sup_right
  have hX₂K : N.X₂ ≤ N.K₂ := T6.X₂_le_K₂ h
  have hX₂'K : N.X₂' ≤ N.K₂ := by rw [hloc.K₂_eq]; exact le_sup_right
  have hK₁le : N.K₁ ≤ N.K₁ ⊔ N.K₂ := le_sup_left
  have hK₂le : N.K₂ ≤ N.K₁ ⊔ N.K₂ := le_sup_right
  have hinv₁ := winv_conj hloc.w₁_mem hloc.w₁_sq (fun x hx => h.zK x (hK₁le hx))
  have hinv₂ := winv_conj hloc.w₂_mem hloc.w₂_sq (fun x hx => h.zK x (hK₂le hx))
  have hc₁₂ : ∀ x ∈ N.K₁, N.w₂ * x * N.w₂⁻¹ = x := by
    intro x hx
    have := hloc.K_comm x hx N.w₂ hloc.w₂_mem
    calc N.w₂ * x * N.w₂⁻¹ = (x * N.w₂) * N.w₂⁻¹ := by rw [this]
      _ = x := by group
  have hc₂₁ : ∀ x ∈ N.K₂, N.w₁ * x * N.w₁⁻¹ = x := by
    intro x hx
    have := hloc.K_comm N.w₁ hloc.w₁_mem x hx
    calc N.w₁ * x * N.w₁⁻¹ = (x * N.w₁) * N.w₁⁻¹ := by rw [← this]
      _ = x := by group
  obtain ⟨w, hw, hwM⟩ : ∃ w : G, (w = N.w₁ ∨ w = N.w₂) ∧ b * w * b⁻¹ ∈ M := by
    rcases T6.P71.Yv_pos h hq hv hb1 hb2 hbH hYcard with hA | hA | hA | hA
    · exact ⟨N.w₁, Or.inl rfl, case_step N.K₁ N.X₁ N.X₁' N.w₁ N.w₂ (Or.inl rfl) (Or.inr rfl) hloc.K₁_eq
        hloc.w₁_mem hX₁K hX₁'K hloc.w₁_swap' hinv₁ hc₁₂ (fun x hx => by rw [hA]; exact hx)⟩
    · exact ⟨N.w₁, Or.inl rfl, case_step N.K₁ N.X₁' N.X₁ N.w₁ N.w₂ (Or.inl rfl) (Or.inr rfl)
        (by rw [hloc.K₁_eq, sup_comm]) hloc.w₁_mem hX₁'K hX₁K hloc.w₁_swap hinv₁ hc₁₂
        (fun x hx => by rw [hA]; exact hx)⟩
    · exact ⟨N.w₂, Or.inr rfl, case_step N.K₂ N.X₂ N.X₂' N.w₂ N.w₁ (Or.inr rfl) (Or.inl rfl) hloc.K₂_eq
        hloc.w₂_mem hX₂K hX₂'K hloc.w₂_swap' hinv₂ hc₂₁ (fun x hx => by rw [hA]; exact hx)⟩
    · exact ⟨N.w₂, Or.inr rfl, case_step N.K₂ N.X₂' N.X₂ N.w₂ N.w₁ (Or.inr rfl) (Or.inl rfl)
        (by rw [hloc.K₂_eq, sup_comm]) hloc.w₂_mem hX₂'K hX₂K hloc.w₂_swap hinv₂ hc₂₁
        (fun x hx => by rw [hA]; exact hx)⟩
  have hzv : N.z * v = v * N.z := by
    rcases hv with hv | hv <;> rw [hv]
    · exact hzu
    · calc N.z * (N.z * u) = u := by rw [← mul_assoc, hz2, one_mul]
        _ = (N.z * u) * N.z := by
          calc u = u * (N.z * N.z) := by rw [hz2, mul_one]
            _ = (u * N.z) * N.z := by group
            _ = (N.z * u) * N.z := by rw [hzu]
  have hwz : w * N.z * w⁻¹ = N.z := by
    have hwK : w ∈ N.K₁ ⊔ N.K₂ := by
      rcases hw with rfl | rfl
      · exact hK₁le hloc.w₁_mem
      · exact hK₂le hloc.w₂_mem
    have := h.zK w hwK
    calc w * N.z * w⁻¹ = (N.z * w) * w⁻¹ := by rw [← this]
      _ = N.z := by group
  have hwu : w * u * w⁻¹ = u * N.z := by
    rcases hw with rfl | rfl
    · exact hloc.w₁_u
    · exact hloc.w₂_u
  have hwv : w * v * w⁻¹ = N.z * v := by
    rcases hv with hv | hv <;> rw [hv]
    · rw [hwu, hzu]
    · calc w * (N.z * u) * w⁻¹ = (w * N.z * w⁻¹) * (w * u * w⁻¹) := by group
        _ = N.z * (u * N.z) := by rw [hwz, hwu]
        _ = N.z * (N.z * u) := by rw [hzu]
  have hgz : (b * w * b⁻¹) * N.z * (b * w * b⁻¹)⁻¹ = v := by
    have e1 : b⁻¹ * N.z * b = v := by
      calc b⁻¹ * N.z * b = b⁻¹ * (b * v * b⁻¹) * b := by rw [hb1]
        _ = v := by group
    calc (b * w * b⁻¹) * N.z * (b * w * b⁻¹)⁻¹ = b * w * (b⁻¹ * N.z * b) * w⁻¹ * b⁻¹ := by group
      _ = b * (w * v * w⁻¹) * b⁻¹ := by rw [e1]; group
      _ = b * (N.z * v) * b⁻¹ := by rw [hwv]
      _ = (b * N.z * b⁻¹) * (b * v * b⁻¹) := by group
      _ = (N.z * v) * N.z := by rw [hb2, hb1]
      _ = (v * N.z) * N.z := by rw [hzv]
      _ = v * (N.z * N.z) := by group
      _ = v := by rw [hz2, mul_one]
  exact T6.P71.final_contra h hq hv hYC hYX₂ hYv hYcard (hMuse _ hwM) hgz

end CFSG.GH74.GLS.Stage4.Rest
