module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Lift

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit

open Subgroup

section Transport

variable {G : Type*} [Group G]

theorem map_conj_subgroupOf (M U : Subgroup G) {g : G} (hg : g ∈ M) :
    (U.map (MulAut.conj g).toMonoidHom).subgroupOf M =
      (U.subgroupOf M).map (MulAut.conj (⟨g, hg⟩ : M)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    have hu' : g⁻¹ * (x : G) * g = u := by
      rw [← hux]
      show g⁻¹ * (g * u * g⁻¹) * g = u
      group
    have huM : u ∈ M := by
      rw [← hu']
      exact M.mul_mem (M.mul_mem (M.inv_mem hg) x.2) hg
    exact Subgroup.mem_map.2 ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.2 hu,
      Subtype.ext (by simpa [MulAut.conj_apply] using hux)⟩
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_subgroupOf.2
      (Subgroup.mem_map.2 ⟨(u : G), Subgroup.mem_subgroupOf.1 hu, rfl⟩)

end Transport

section Lift

variable {G : Type*} [Group G] (D Y : Subgroup G) [(Y.subgroupOf D).Normal]

theorem eq_one_of_fixed {Γ₁ Γ₂ : Subgroup G} (hΓ₁ : Γ₁ ≤ normDY D Y) (hΓ₂ : Γ₂ ≤ normDY D Y)
    (hfix : ∀ x ∈ D, (∀ g ∈ Γ₁, g * x * g⁻¹ * x⁻¹ ∈ Y) →
      (∀ g ∈ Γ₂, g * x * g⁻¹ * x⁻¹ ∈ Y) → x ∈ Y)
    (v : D ⧸ Y.subgroupOf D)
    (h₁ : ∀ g ∈ Γ₁.subgroupOf (normDY D Y), actQuot D Y g v = v)
    (h₂ : ∀ g ∈ Γ₂.subgroupOf (normDY D Y), actQuot D Y g v = v) : v = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rw [mk_eq_one_iff D Y x]
  refine hfix (x : G) x.2 (fun g hg => ?_) (fun g hg => ?_)
  · exact (actQuot_mk_eq_iff D Y ⟨g, hΓ₁ hg⟩ x).1 (h₁ ⟨g, hΓ₁ hg⟩ (Subgroup.mem_subgroupOf.2 hg))
  · exact (actQuot_mk_eq_iff D Y ⟨g, hΓ₂ hg⟩ x).1 (h₂ ⟨g, hΓ₂ hg⟩ (Subgroup.mem_subgroupOf.2 hg))

theorem fixSub_disjoint_of_liftFix (hYD : Y ≤ D) (hY : 0 < Nat.card Y)
    (S : Subgroup (normDY D Y)) (g : normDY D Y)
    (h : liftFix D Y S ⊓ (liftFix D Y S).map (MulAut.conj (g : G)).toMonoidHom = Y) :
    fixSub (actQuot D Y) S ⊓ (fixSub (actQuot D Y) S).map (actQuot D Y g).toMonoidHom = ⊥ := by
  have hsup : liftFix D Y (S ⊔ S.map (MulAut.conj g).toMonoidHom) = Y := by
    rw [← liftFix_inf, liftFix_map_conj]
    exact h
  have hcard : Nat.card (fixSub (actQuot D Y) (S ⊔ S.map (MulAut.conj g).toMonoidHom)) = 1 := by
    have h1 := card_liftFix D Y hYD (S ⊔ S.map (MulAut.conj g).toMonoidHom)
    rw [hsup] at h1
    apply Nat.eq_of_mul_eq_mul_left hY
    rw [mul_one]
    exact h1.symm
  rw [← fixSub_map_conj, ← fixSub_sup]
  exact Subgroup.eq_bot_of_card_eq _ hcard

end Lift

theorem splittingG {G : Type*} [Group G] [Finite G] (D Y : Subgroup G) [(Y.subgroupOf D).Normal]
    (hYD : Y ≤ D) (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Y)
    (hDcard : Nat.card D = 2 ^ 16) (hYcard : Nat.card Y = 2 ^ 8)
    {k : Type*} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 4)
    (t : G) (ht : t ∈ normDY D Y) (htt : t * t = 1)
    (Γ₁ Γ₂ U₁ U₂ : Subgroup G) (w₁ w₂ : G)
    (hΓ₁ : Γ₁ ≤ normDY D Y) (hΓ₂ : Γ₂ ≤ normDY D Y)
    (e₂ : Γ₂ ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    (e₁ : Γ₁ ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    (hU : U₁.map (MulAut.conj t).toMonoidHom = U₂)
    (hcommΓ : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a)
    (hU₁ : U₁ ≤ Γ₁) (hU₂ : U₂ ≤ Γ₂) (hw₁ : w₁ ∈ Γ₁) (hw₂ : w₂ ∈ Γ₂)
    (hp₁ : IsPGroup 2 U₁) (hp₂ : IsPGroup 2 U₂)
    (hgen₁ : Γ₁ ≤ U₁ ⊔ U₁.map (MulAut.conj w₁).toMonoidHom)
    (hgen₂ : Γ₂ ≤ U₂ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom)
    (hfix : ∀ x ∈ D, (∀ g ∈ Γ₁, g * x * g⁻¹ * x⁻¹ ∈ Y) →
      (∀ g ∈ Γ₂, g * x * g⁻¹ * x⁻¹ ∈ Y) → x ∈ Y)
    (hplus : Nat.card (liftFixG D Y (U₁ ⊔ U₂)) = 2 ^ 12)
    (hdisj : liftFixG D Y (U₁ ⊔ U₂) ⊓
      (liftFixG D Y (U₁ ⊔ U₂)).map (MulAut.conj (w₁ * w₂)).toMonoidHom = Y) :
    Nat.card (liftFixG D Y Γ₁) = 2 ^ 12 ∧ Nat.card (liftFixG D Y Γ₂) = 2 ^ 12 ∧
      liftFixG D Y Γ₁ ⊔ liftFixG D Y Γ₂ = D ∧ liftFixG D Y Γ₁ ⊓ liftFixG D Y Γ₂ = Y := by
  have hN₁ : U₁ ≤ normDY D Y := hU₁.trans hΓ₁
  have hN₂ : U₂ ≤ normDY D Y := hU₂.trans hΓ₂
  have hw₁N : w₁ ∈ normDY D Y := hΓ₁ hw₁
  have hw₂N : w₂ ∈ normDY D Y := hΓ₂ hw₂
  have hYpos : 0 < Nat.card Y := by rw [hYcard]; norm_num
  have hV : Nat.card (D ⧸ Y.subgroupOf D) = 2 ^ 8 := by
    have h : 2 ^ 16 = Nat.card (D ⧸ Y.subgroupOf D) * 2 ^ 8 := by
      rw [← hDcard, ← hYcard]
      exact card_D_eq D Y hYD
    have h' : Nat.card (D ⧸ Y.subgroupOf D) * 2 ^ 8 = 2 ^ 8 * 2 ^ 8 := by
      rw [← h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have hcomm : ∀ a b : D ⧸ Y.subgroupOf D, a * b = b * a := quot_comm D Y hDcomm
  have hU' : (U₁.subgroupOf (normDY D Y)).map (MulAut.conj (⟨t, ht⟩ : normDY D Y)).toMonoidHom =
      U₂.subgroupOf (normDY D Y) := by
    rw [← map_conj_subgroupOf (normDY D Y) U₁ ht, hU]
  have hcommΓ' : ∀ a ∈ Γ₁.subgroupOf (normDY D Y), ∀ b ∈ Γ₂.subgroupOf (normDY D Y),
      a * b = b * a := fun a ha b hb =>
    Subtype.ext (hcommΓ (a : G) (Subgroup.mem_subgroupOf.1 ha) (b : G)
      (Subgroup.mem_subgroupOf.1 hb))
  have hU₁' : U₁.subgroupOf (normDY D Y) ≤ Γ₁.subgroupOf (normDY D Y) :=
    Subgroup.subgroupOf_mono _ hU₁
  have hU₂' : U₂.subgroupOf (normDY D Y) ≤ Γ₂.subgroupOf (normDY D Y) :=
    Subgroup.subgroupOf_mono _ hU₂
  have hw₁' : (⟨w₁, hw₁N⟩ : normDY D Y) ∈ Γ₁.subgroupOf (normDY D Y) :=
    Subgroup.mem_subgroupOf.2 hw₁
  have hw₂' : (⟨w₂, hw₂N⟩ : normDY D Y) ∈ Γ₂.subgroupOf (normDY D Y) :=
    Subgroup.mem_subgroupOf.2 hw₂
  have hp₁' : IsPGroup 2 ↥(U₁.subgroupOf (normDY D Y)) :=
    hp₁.of_equiv (Subgroup.subgroupOfEquivOfLe hN₁).symm
  have hp₂' : IsPGroup 2 ↥(U₂.subgroupOf (normDY D Y)) :=
    hp₂.of_equiv (Subgroup.subgroupOfEquivOfLe hN₂).symm
  have hN₁w₁ : U₁.map (MulAut.conj w₁).toMonoidHom ≤ normDY D Y := by
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hw₁N (hN₁ hu)) (inv_mem hw₁N)
  have hN₂w₂ : U₂.map (MulAut.conj w₂).toMonoidHom ≤ normDY D Y := by
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hw₂N (hN₂ hu)) (inv_mem hw₂N)
  have hgen₁' : Γ₁.subgroupOf (normDY D Y) ≤ U₁.subgroupOf (normDY D Y) ⊔
      (U₁.subgroupOf (normDY D Y)).map (MulAut.conj (⟨w₁, hw₁N⟩ : normDY D Y)).toMonoidHom := by
    rw [← map_conj_subgroupOf (normDY D Y) U₁ hw₁N, ← Subgroup.subgroupOf_sup hN₁ hN₁w₁]
    exact Subgroup.subgroupOf_mono _ hgen₁
  have hgen₂' : Γ₂.subgroupOf (normDY D Y) ≤ U₂.subgroupOf (normDY D Y) ⊔
      (U₂.subgroupOf (normDY D Y)).map (MulAut.conj (⟨w₂, hw₂N⟩ : normDY D Y)).toMonoidHom := by
    rw [← map_conj_subgroupOf (normDY D Y) U₂ hw₂N, ← Subgroup.subgroupOf_sup hN₂ hN₂w₂]
    exact Subgroup.subgroupOf_mono _ hgen₂
  have hfix' : ∀ v : D ⧸ Y.subgroupOf D,
      (∀ g ∈ Γ₁.subgroupOf (normDY D Y), actQuot D Y g v = v) →
      (∀ g ∈ Γ₂.subgroupOf (normDY D Y), actQuot D Y g v = v) → v = 1 :=
    fun v h₁ h₂ => eq_one_of_fixed D Y hΓ₁ hΓ₂ hfix v h₁ h₂
  have hplus' : Nat.card (fixSub (actQuot D Y)
      (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y))) = 16 := by
    have h1 : Nat.card (liftFix D Y ((U₁ ⊔ U₂).subgroupOf (normDY D Y))) = 2 ^ 12 := hplus
    rw [Subgroup.subgroupOf_sup hN₁ hN₂] at h1
    have h2 := card_liftFix D Y hYD (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y))
    rw [h1, hYcard] at h2
    norm_num at h2
    omega
  have hdisj' : fixSub (actQuot D Y)
      (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y)) ⊓
      (fixSub (actQuot D Y)
        (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y))).map
          (actQuot D Y (⟨w₁, hw₁N⟩ * ⟨w₂, hw₂N⟩ : normDY D Y)).toMonoidHom = ⊥ := by
    refine fixSub_disjoint_of_liftFix D Y hYD hYpos _ _ ?_
    rw [← Subgroup.subgroupOf_sup hN₁ hN₂]
    exact hdisj
  obtain ⟨c1, c2, s12, i12⟩ := splitting (actQuot D Y) hcomm hV hk ⟨t, ht⟩ (Subtype.ext htt)
    (Γ₁.subgroupOf (normDY D Y)) (Γ₂.subgroupOf (normDY D Y))
    (U₁.subgroupOf (normDY D Y)) (U₂.subgroupOf (normDY D Y))
    ⟨w₁, hw₁N⟩ ⟨w₂, hw₂N⟩
    ((Subgroup.subgroupOfEquivOfLe hΓ₂).trans e₂) ((Subgroup.subgroupOfEquivOfLe hΓ₁).trans e₁)
    hU' hcommΓ' hU₁' hU₂' hw₁' hw₂' hp₁' hp₂' hgen₁' hgen₂' hfix' hplus' hdisj'
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Nat.card (liftFix D Y (Γ₁.subgroupOf (normDY D Y))) = 2 ^ 12
    rw [card_liftFix D Y hYD, c1, hYcard] <;> norm_num
  · show Nat.card (liftFix D Y (Γ₂.subgroupOf (normDY D Y))) = 2 ^ 12
    rw [card_liftFix D Y hYD, c2, hYcard] <;> norm_num
  · exact liftFix_sup_of_fixSub_sup D Y (Γ₁.subgroupOf (normDY D Y))
      (Γ₂.subgroupOf (normDY D Y)) s12
  · show liftFix D Y (Γ₁.subgroupOf (normDY D Y)) ⊓ liftFix D Y (Γ₂.subgroupOf (normDY D Y)) = Y
    rw [liftFix_inf]
    have hcardL : Nat.card (fixSub (actQuot D Y)
        (Γ₁.subgroupOf (normDY D Y) ⊔ Γ₂.subgroupOf (normDY D Y))) = 1 := by
      rw [fixSub_sup, i12, Subgroup.card_bot]
    have h1 := card_liftFix D Y hYD (Γ₁.subgroupOf (normDY D Y) ⊔ Γ₂.subgroupOf (normDY D Y))
    rw [hcardL, mul_one] at h1
    exact (Subgroup.eq_of_le_of_card_ge
      (Y_le_liftFix D Y hYD (Γ₁.subgroupOf (normDY D Y) ⊔ Γ₂.subgroupOf (normDY D Y))) h1.le).symm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit
