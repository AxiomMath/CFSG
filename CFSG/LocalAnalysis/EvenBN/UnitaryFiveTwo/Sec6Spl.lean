module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6U

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem V₃_cen_MY_lin (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    ∀ x ∈ d.V₃, ∀ q ∈ d.M ⊔ d.Y, q * x * q⁻¹ * x⁻¹ ∈ d.Y := by
  have step1 : ∀ m ∈ d.M, d.V₃ ≤ centModSub d.Y m := by
    intro m hm
    rw [h.V₃_eq hK]
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · obtain ⟨hx3, hx2⟩ := Subgroup.mem_inf.1 hx
      have hx1 : x ∈ d.D₁ ⊓ d.D₂ := by rwa [← h.D₃_inf_D₂_eq]
      have hxN : x ∈ normalizer (d.Y : Set G) := mem_normalizer_fintype fun y hy => by
        have e : x * y = y * x := (Data.Hyp.D₂_comm_Y' hx2 hy).symm.symm
        rw [e, mul_inv_cancel_right]
        exact hy
      refine ⟨hxN, d.W_le_Y ?_⟩
      exact h.D₁_commutator_mem_W hK (Subgroup.mem_inf.1 hx1).1 (Subgroup.mem_inf.1 hm).1
    · refine ⟨d.Y.le_normalizer hy, ?_⟩
      have := (mem_normalizer_iff.1 (hKY m hm) y⁻¹).1 (inv_mem hy)
      rw [show y * m * y⁻¹ * m⁻¹ = y * (m * y⁻¹ * m⁻¹) by group]
      exact d.Y.mul_mem hy this
  have hMc : d.M ≤ cenMod d.Y d.V₃ := fun m hm => by
    refine ⟨hKY m hm, fun x hx => ?_⟩
    have := (step1 m hm hx).2
    have hinv := d.Y.inv_mem this
    rwa [show (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ by group] at hinv
  have hYc : d.Y ≤ cenMod d.Y d.V₃ := fun y hy => by
    refine ⟨d.Y.le_normalizer hy, fun x hx => ?_⟩
    have hx2 : x ∈ d.D₂ := h.V₃_le_D₂ hK hx
    have e : x * y = y * x := (Data.Hyp.D₂_comm_Y' hx2 hy).symm.symm
    rw [show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) by group]
    have e' : x * y⁻¹ = y⁻¹ * x := (Data.Hyp.D₂_comm_Y' hx2 (inv_mem hy)).symm.symm
    rw [e']
    simpa using d.Y.one_mem
  have hMYc : d.M ⊔ d.Y ≤ cenMod d.Y d.V₃ := sup_le hMc hYc
  intro x hx q hq
  exact (hMYc hq).2 x hx

theorem MY_le_normDY_lin (h : d.Hyp) (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G))
    (hD : d.D₁ ≤ normalizer (d.D₂ : Set G)) : d.M ⊔ d.Y ≤ ModSplit.normDY d.D₂ d.Y := by
  refine sup_le (fun m hm => ?_) (fun y hy => ?_)
  · exact Subgroup.mem_inf.2 ⟨hD (Subgroup.mem_inf.1 hm).1, hKY m hm⟩
  · exact Subgroup.mem_inf.2 ⟨d.D₂.le_normalizer (h.Y_le_D₂ hy), d.Y.le_normalizer hy⟩

omit [Finite G] in
theorem conj_inv_mem_D₂_iff {D : Subgroup G} {g : G} (hg : g ∈ normalizer (D : Set G)) {x : G} :
    g⁻¹ * x * g ∈ D ↔ x ∈ D := by
  constructor
  · intro hx
    have := (mem_normalizer_iff.1 hg (g⁻¹ * x * g)).1 hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  · intro hx
    have hg' := inv_mem hg
    have := (mem_normalizer_iff.1 hg' x).1 hx
    rwa [inv_inv] at this

theorem map_conj_V₃_eq (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {w y₀ : G} (hw : w ∈ normalizer (d.D₂ : Set G)) (hy₀ : y₀ ∈ d.Y) (hv : d.v = y₀ * w) :
    d.V₃.map (MulAut.conj d.v).toMonoidHom = d.V₃.map (MulAut.conj w).toMonoidHom := by
  have hvN : d.v ∈ normalizer (d.D₂ : Set G) := h.v_mem_normalizer_D₂
  have key : ∀ x ∈ d.D₂, d.v⁻¹ * x * d.v = w⁻¹ * x * w := fun x hx => by
    have hc : x * y₀ = y₀ * x := Data.Hyp.D₂_comm_Y' hx hy₀
    rw [hv]
    calc (y₀ * w)⁻¹ * x * (y₀ * w) = w⁻¹ * (y₀⁻¹ * x * y₀) * w := by group
      _ = w⁻¹ * x * w := by
        congr 2
        rw [mul_assoc, hc]
        group
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff]
  constructor
  · intro hx
    have hxD : x ∈ d.D₂ := (conj_inv_mem_D₂_iff hvN).1 (h.V₃_le_D₂ hK hx)
    rwa [← key x hxD]
  · intro hx
    have hxD : x ∈ d.D₂ := (conj_inv_mem_D₂_iff hw).1 (h.V₃_le_D₂ hK hx)
    rwa [key x hxD]

theorem liftFixG_U_eq_V₃_lin (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G))
    (hD : d.D₁ ≤ normalizer (d.D₂ : Set G))
    {Γ₁ Γ₂ U₁ U₂ : Subgroup G} {w₁ w₂ y₀ : G}
    (hΓ₁ : Γ₁ ≤ ModSplit.normDY d.D₂ d.Y) (hΓ₂ : Γ₂ ≤ ModSplit.normDY d.D₂ d.Y)
    (hU₁ : U₁ ≤ d.M ⊔ d.Y) (hU₂ : U₂ ≤ d.M ⊔ d.Y)
    (hw₁ : w₁ ∈ Γ₁) (hw₂ : w₂ ∈ Γ₂) (hw₁sq : w₁ * w₁ = 1) (hw₂sq : w₂ * w₂ = 1)
    (hcomm : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a)
    (hU₁Γ : U₁ ≤ Γ₁) (hU₂Γ : U₂ ≤ Γ₂)
    (hgen₁ : Γ₁ ≤ U₁ ⊔ U₁.map (MulAut.conj w₁).toMonoidHom)
    (hgen₂ : Γ₂ ≤ U₂ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom)
    (hfix : ∀ x ∈ d.D₂, (∀ g ∈ Γ₁, g * x * g⁻¹ * x⁻¹ ∈ d.Y) →
      (∀ g ∈ Γ₂, g * x * g⁻¹ * x⁻¹ ∈ d.Y) → x ∈ d.Y)
    (hy₀ : y₀ ∈ d.Y) (hv : d.v = y₀ * (w₁ * w₂)) :
    ModSplit.liftFixG d.D₂ d.Y (U₁ ⊔ U₂) = d.V₃ := by
  set S : Subgroup G := U₁ ⊔ U₂ with hSdef
  set w : G := w₁ * w₂ with hwdef
  have hS : S ≤ ModSplit.normDY d.D₂ d.Y :=
    (sup_le hU₁ hU₂).trans (h.MY_le_normDY_lin hKY hD)
  have hSMY : S ≤ d.M ⊔ d.Y := sup_le hU₁ hU₂
  have hw₁N := (ModSplit.mem_normDY _ _).1 (hΓ₁ hw₁)
  have hw₂N := (ModSplit.mem_normDY _ _).1 (hΓ₂ hw₂)
  have hwD : w ∈ normalizer (d.D₂ : Set G) := mul_mem hw₁N.1 hw₂N.1
  have hwY : w ∈ normalizer (d.Y : Set G) := mul_mem hw₁N.2 hw₂N.2
  have hmap := h.map_conj_V₃_eq hK hwD hy₀ hv
  have hge : d.V₃ ≤ ModSplit.liftFixG d.D₂ d.Y S := fun x hx => by
    rw [ModSplit.mem_liftFixG_iff _ _ hS]
    exact ⟨h.V₃_le_D₂ hK hx, fun g hg => h.V₃_cen_MY_lin hK hKY x hx g (hSMY hg)⟩
  refine le_antisymm (fun x hx => ?_) hge
  have hxmem := (ModSplit.mem_liftFixG_iff _ _ hS).1 hx
  have hxD := hxmem.1
  have hN : d.V₃.map (MulAut.conj w).toMonoidHom ≤ normalizer (d.V₃ : Set G) := by
    rw [← hmap]
    exact (h.conj_V₃_le_D₂ hK).trans h.D₂_le_normalizer_V₃
  have hxsup : x ∈ d.V₃.map (MulAut.conj w).toMonoidHom ⊔ d.V₃ := by
    rw [← hmap, sup_comm, ← h.D₂_eq_V₃_sup hK]
    exact hxD
  obtain ⟨b, hb, a, ha, hxba⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer hN hxsup
  have hbL : b ∈ ModSplit.liftFixG d.D₂ d.Y S := by
    have : b = x * a⁻¹ := by rw [hxba]; group
    rw [this]
    exact (ModSplit.liftFixG d.D₂ d.Y S).mul_mem hx
      ((ModSplit.liftFixG d.D₂ d.Y S).inv_mem (hge ha))
  have hbfix := ((ModSplit.mem_liftFixG_iff _ _ hS).1 hbL).2
  have hb₀ : w⁻¹ * b * w ∈ d.V₃ := (mem_map_conj_iff _ _ _).1 hb
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀ : G, b₀ = w⁻¹ * b * w := ⟨_, rfl⟩
  rw [← hb₀def] at hb₀
  have hCbS : S ≤ centModSub d.Y b₀ := fun g hg =>
    ⟨(hS hg).2, h.V₃_cen_MY_lin hK hKY b₀ hb₀ g (hSMY hg)⟩
  have hCbSv : ∀ s ∈ S, w⁻¹ * s * w ∈ centModSub d.Y b₀ := by
    intro s hs
    refine ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem hwY) (hS hs).2) hwY
    · have e : (w⁻¹ * s * w) * b₀ * (w⁻¹ * s * w)⁻¹ * b₀⁻¹ =
          w⁻¹ * (s * b * s⁻¹ * b⁻¹) * w := by
        rw [hb₀def]
        group
      rw [e]
      have := (mem_normalizer_iff.1 (inv_mem hwY) _).1 (hbfix s hs)
      rwa [inv_inv] at this
  have hinv₁ : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hw₁sq
  have hinv₂ : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hw₂sq
  have hconj₁ : ∀ u ∈ Γ₁, w⁻¹ * u * w = w₁ * u * w₁⁻¹ := by
    intro u hu
    have hu' : w₁⁻¹ * u * w₁ ∈ Γ₁ := Γ₁.mul_mem (Γ₁.mul_mem (Γ₁.inv_mem hw₁) hu) hw₁
    have hc := hcomm _ hu' _ hw₂
    calc w⁻¹ * u * w = w₂⁻¹ * (w₁⁻¹ * u * w₁) * w₂ := by rw [hwdef]; group
      _ = w₁⁻¹ * u * w₁ := by rw [mul_assoc, hc]; group
      _ = w₁ * u * w₁⁻¹ := by rw [hinv₁]
  have hconj₂ : ∀ u ∈ Γ₂, w⁻¹ * u * w = w₂ * u * w₂⁻¹ := by
    intro u hu
    have hc : w₁ * u = u * w₁ := hcomm _ hw₁ _ hu
    calc w⁻¹ * u * w = w₂⁻¹ * (w₁⁻¹ * u * w₁) * w₂ := by rw [hwdef]; group
      _ = w₂⁻¹ * u * w₂ := by
        rw [show w₁⁻¹ * u * w₁ = u by rw [mul_assoc, ← hc]; group]
      _ = w₂ * u * w₂⁻¹ := by rw [hinv₂]
  have hΛ₁ : Γ₁ ≤ centModSub d.Y b₀ := by
    refine hgen₁.trans (sup_le (le_sup_left.trans hCbS) ?_)
    rintro _ ⟨u, hu, rfl⟩
    show w₁ * u * w₁⁻¹ ∈ centModSub d.Y b₀
    rw [← hconj₁ u (hU₁Γ hu)]
    exact hCbSv u (mem_sup_left hu)
  have hΛ₂ : Γ₂ ≤ centModSub d.Y b₀ := by
    refine hgen₂.trans (sup_le (le_sup_right.trans hCbS) ?_)
    rintro _ ⟨u, hu, rfl⟩
    show w₂ * u * w₂⁻¹ ∈ centModSub d.Y b₀
    rw [← hconj₂ u (hU₂Γ hu)]
    exact hCbSv u (mem_sup_right hu)
  have hb₀Y : b₀ ∈ d.Y :=
    hfix b₀ (h.V₃_le_D₂ hK hb₀) (fun g hg => (hΛ₁ hg).2) (fun g hg => (hΛ₂ hg).2)
  have hbY : b ∈ d.Y := by
    have : b = w * b₀ * w⁻¹ := by rw [hb₀def]; group
    rw [this]
    exact (mem_normalizer_iff.1 hwY b₀).1 hb₀Y
  rw [hxba]
  exact d.V₃.mul_mem (h.Y_le_V₃ hbY) ha

theorem splitting_D₂_lin (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G))
    (hD : d.D₁ ≤ normalizer (d.D₂ : Set G))
    {Γ₁ Γ₂ U₁ U₂ : Subgroup G} {w₁ w₂ y₀ : G}
    (e₁ : ↥Γ₁ ≃* Matrix.SpecialLinearGroup (Fin 2) CFSG.Fischer.F4)
    (e₂ : ↥Γ₂ ≃* Matrix.SpecialLinearGroup (Fin 2) CFSG.Fischer.F4)
    (hU : U₁.map (MulAut.conj d.t).toMonoidHom = U₂)
    (hp₁ : IsPGroup 2 ↥U₁) (hp₂ : IsPGroup 2 ↥U₂)
    (hΓ₁ : Γ₁ ≤ ModSplit.normDY d.D₂ d.Y) (hΓ₂ : Γ₂ ≤ ModSplit.normDY d.D₂ d.Y)
    (hU₁ : U₁ ≤ d.M ⊔ d.Y) (hU₂ : U₂ ≤ d.M ⊔ d.Y)
    (hw₁ : w₁ ∈ Γ₁) (hw₂ : w₂ ∈ Γ₂) (hw₁sq : w₁ * w₁ = 1) (hw₂sq : w₂ * w₂ = 1)
    (hcomm : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a)
    (hU₁Γ : U₁ ≤ Γ₁) (hU₂Γ : U₂ ≤ Γ₂)
    (hgen₁ : Γ₁ ≤ U₁ ⊔ U₁.map (MulAut.conj w₁).toMonoidHom)
    (hgen₂ : Γ₂ ≤ U₂ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom)
    (hfix : ∀ x ∈ d.D₂, (∀ g ∈ Γ₁, g * x * g⁻¹ * x⁻¹ ∈ d.Y) →
      (∀ g ∈ Γ₂, g * x * g⁻¹ * x⁻¹ ∈ d.Y) → x ∈ d.Y)
    (hy₀ : y₀ ∈ d.Y) (hv : d.v = y₀ * (w₁ * w₂)) :
    Nat.card (ModSplit.liftFixG d.D₂ d.Y Γ₁) = 2 ^ 12 ∧
      Nat.card (ModSplit.liftFixG d.D₂ d.Y Γ₂) = 2 ^ 12 ∧
      ModSplit.liftFixG d.D₂ d.Y Γ₁ ⊔ ModSplit.liftFixG d.D₂ d.Y Γ₂ = d.D₂ ∧
      ModSplit.liftFixG d.D₂ d.Y Γ₁ ⊓ ModSplit.liftFixG d.D₂ d.Y Γ₂ = d.Y := by
  have htY : d.t ∈ normalizer (d.Y : Set G) := mem_normalizer_fintype fun y hy => by
    have := h.t_conj_mem_Y hy
    rw [h.t_inv]
    exact this
  have hLU := h.liftFixG_U_eq_V₃_lin hK hKY hD hΓ₁ hΓ₂ hU₁ hU₂ hw₁ hw₂ hw₁sq hw₂sq hcomm hU₁Γ
    hU₂Γ hgen₁ hgen₂ hfix hy₀ hv
  have hwD : w₁ * w₂ ∈ normalizer (d.D₂ : Set G) :=
    mul_mem ((ModSplit.mem_normDY _ _).1 (hΓ₁ hw₁)).1 ((ModSplit.mem_normDY _ _).1 (hΓ₂ hw₂)).1
  refine ModSplit.splittingG d.D₂ d.Y h.Y_le_D₂ (fun x hx y hy => h.D₂_commutator_mem_Y hK hx hy)
    h.card_D₂ h.card_Y (k := CFSG.Fischer.F4)
    (by rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card])
    d.t ⟨h.t_mem_normalizer_D₂, htY⟩ h.t_mul_t Γ₁ Γ₂ U₁ U₂ w₁ w₂ hΓ₁ hΓ₂ e₂ e₁ hU hcomm hU₁Γ hU₂Γ
    hw₁ hw₂ hp₁ hp₂ hgen₁ hgen₂ hfix ?_ ?_
  · rw [hLU, h.card_V₃ hK]
  · rw [hLU, ← h.map_conj_V₃_eq hK hwD hy₀ hv]
    exact h.V₃_inf_conj_V₃ hK

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
