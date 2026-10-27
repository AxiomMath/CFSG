module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2End
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2

structure SplitFacts (M : Model) : Prop where
  card_fixM_tbar : Nat.card (fixM (M.tbar : Mat12)) = 2 ^ 6
  exists_of_fixM_tbar : ∀ v : Vec12, (M.tbar : Mat12) *ᵥ v = v →
    ∃ x : Vec12, (M.tbar : Mat12) *ᵥ x + x = v
  offender_m2 : ∀ E : Subgroup GL12, E ≤ M.TC → (∀ x ∈ E, x * x = 1) → E ≠ ⊥ →
    Nat.card E * Nat.card ↥(fixM (M.tbar : Mat12) ∩ fixV E) ≤ 2 ^ 8
  offender_TC : ∀ A : Subgroup GL12, A ≤ M.TC → (∀ x ∈ A, x * x = 1) → A ≠ ⊥ →
    Nat.card A * Nat.card ↥(Set.univ ∩ fixV A) ≤ 2 ^ 11
  card_TC : Nat.card M.TC = 2 ^ 8
  TC_le_CC : M.TC ≤ M.CC
  TC_max : ∀ Y : Subgroup GL12, IsPGroup 2 Y → M.TC ≤ Y → Y ≤ M.CC → Y = M.TC

variable {G : Type*} [Group G]

theorem mem_zpowers_of_sq {u z : G} (hu : u * u = 1) (hz : z ∈ zpowers u) : z = 1 ∨ z = u := by
  obtain ⟨k, rfl⟩ := hz
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  change u ^ k = 1 ∨ u ^ k = u
  rw [hk, _root_.zpow_add, _root_.zpow_mul, hu2, _root_.one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · exact Or.inl (zpow_zero u)
  · exact Or.inr (zpow_one u)

theorem mem_sup_zpowers_iff {X : Subgroup G} {u : G} (hu : u * u = 1)
    (hc : ∀ x ∈ X, x * u = u * x) {y : G} :
    y ∈ X ⊔ zpowers u ↔ ∃ x ∈ X, y = x ∨ y = x * u := by
  have hcomm : ∀ a ∈ X, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_of_sq hu hb with rfl | rfl
    · rw [mul_one, one_mul]
    · exact hc a ha
  constructor
  · intro hy
    obtain ⟨x, hx, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hy
    rcases mem_zpowers_of_sq hu hz with rfl | rfl
    · exact ⟨x, hx, Or.inl (mul_one x)⟩
    · exact ⟨x, hx, Or.inr rfl⟩
  · rintro ⟨x, hx, rfl | rfl⟩
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers u))

theorem card_sup_zpowers [Finite G] {X : Subgroup G} {u : G} (hu : u * u = 1) (huX : u ∉ X)
    (hc : ∀ x ∈ X, x * u = u * x) : Nat.card (X ⊔ zpowers u : Subgroup G) = 2 * Nat.card X := by
  have hidx : X.relIndex (X ⊔ zpowers u) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨u, mem_sup_right (mem_zpowers u), fun b hb => ?_⟩
    obtain ⟨x, hx, rfl | rfl⟩ := (mem_sup_zpowers_iff hu hc).1 hb
    · exact Or.inr ⟨hx, fun h => huX (by simpa using X.mul_mem (X.inv_mem hx) h)⟩
    · rw [mul_assoc, hu, mul_one]
      exact Or.inl ⟨hx, fun h => huX (by simpa using X.mul_mem (X.inv_mem hx) h)⟩
  rw [← Subgroup.relIndex_mul_card (H := X) (K := X ⊔ zpowers u), hidx,
    inf_of_le_left le_sup_left]

theorem card_inf_centralizer_W {W : Subgroup G} (φ : W ≃* Multiplicative (Fin 12 → ZMod 2))
    {g : G} (hg : g ∈ NW W) :
    Nat.card ↥(W ⊓ centralizer ({g} : Set G)) = Nat.card (fixM (rhoG W φ g : Mat12)) := by
  rw [card_fixM_rhoG hg]
  refine Nat.card_congr
    { toFun := fun e => ⟨⟨e.1, e.2.1⟩, ?_⟩
      invFun := fun w => ⟨w.1.1, w.1.2, ?_⟩
      left_inv := fun e => rfl
      right_inv := fun w => rfl }
  · have h2 : e.1 ∈ centralizer ({g} : Set G) := e.2.2
    rw [mem_centralizer_singleton_iff] at h2
    show g * e.1 * g⁻¹ = e.1
    rw [← h2, mul_inv_cancel_right]
  · show w.1.1 ∈ centralizer ({g} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h2 := w.2
    calc w.1.1 * g = g * w.1.1 * g⁻¹ * g := by rw [h2]
      _ = g * w.1.1 := by group

section Hyp

variable {M : Model} {t : G} {TH W : Subgroup G} {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}

theorem isPGroup_W_inf (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) (X : Subgroup G) :
    IsPGroup 2 (W ⊓ X : Subgroup G) :=
  isPGroup_of_sq_eq_one fun _ hx => W_mem_sq φ hx.1

theorem commute_inv_of_commute {x t : G} (h : x * t = t * x) : x⁻¹ * t = t * x⁻¹ := by
  calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * t) * x⁻¹ := by rw [h]
    _ = t * x⁻¹ := by group

theorem W_inf_le_TH [Finite G] (h : Stage2Hyp M t TH W φ) :
    W ⊓ centralizer ({t} : Set G) ≤ TH := by
  have hN : TH ≤ normalizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (h.TH_le hx)
    have hx' := commute_inv_of_commute hxt
    have hxW := mem_normalizer_iff.1 (h.TH_le_normalizer hx)
    intro w
    constructor
    · rintro ⟨hw, hwt⟩
      refine ⟨(hxW w).1 hw, mem_centralizer_singleton_iff.2 ?_⟩
      have hwt' : w * t = t * w := mem_centralizer_singleton_iff.1 hwt
      calc x * w * x⁻¹ * t = x * w * (x⁻¹ * t) := by group
        _ = x * w * (t * x⁻¹) := by rw [hx']
        _ = x * (w * t) * x⁻¹ := by group
        _ = x * (t * w) * x⁻¹ := by rw [hwt']
        _ = (x * t) * w * x⁻¹ := by group
        _ = (t * x) * w * x⁻¹ := by rw [hxt]
        _ = t * (x * w * x⁻¹) := by group
    · rintro ⟨hw, hwt⟩
      refine ⟨(hxW w).2 hw, mem_centralizer_singleton_iff.2 ?_⟩
      have hwt' : x * w * x⁻¹ * t = t * (x * w * x⁻¹) := mem_centralizer_singleton_iff.1 hwt
      calc w * t = x⁻¹ * (x * w * x⁻¹) * (x * t) := by group
        _ = x⁻¹ * (x * w * x⁻¹) * (t * x) := by rw [hxt]
        _ = x⁻¹ * ((x * w * x⁻¹) * t) * x := by group
        _ = x⁻¹ * (t * (x * w * x⁻¹)) * x := by rw [hwt']
        _ = (x⁻¹ * t) * (x * w) := by group
        _ = (t * x⁻¹) * (x * w) := by rw [hx']
        _ = t * w := by group
  have h2 : IsPGroup 2 ((W ⊓ centralizer ({t} : Set G)) ⊔ TH : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_W_inf φ _) h.TH_pgroup hN
  have heq := eq_of_isPGroup_of_not_dvd h.TH_index h2 le_sup_right
    (sup_le inf_le_right h.TH_le)
  exact le_sup_left.trans heq.le

theorem TH_inf_centralizer [Finite G] (h : Stage2Hyp M t TH W φ) :
    TH ⊓ centralizer (W : Set G) = W ⊓ centralizer ({t} : Set G) := by
  refine le_antisymm (fun x hx => ⟨inf_centralizer_le_W h.TH_pgroup h.sylow_W hx,
    h.TH_le hx.1⟩) (fun x hx => ⟨W_inf_le_TH h hx, ?_⟩)
  refine mem_centralizer_iff.2 fun w hw => ?_
  exact congrArg Subtype.val (W_comm φ ⟨w, hw⟩ ⟨x, hx.1⟩)

theorem rhoImg_TH (h : Stage2Hyp M t TH W φ) : rhoImg W φ TH = M.TC := by
  ext y
  rw [mem_rhoImg h.TH_le_normalizer]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h.rho_TH x hx
  · intro hy
    exact h.TC_le y hy

theorem card_TH [Finite G] (h : Stage2Hyp M t TH W φ) :
    Nat.card TH = Nat.card M.TC * Nat.card (fixM (M.tbar : Mat12)) := by
  rw [card_eq_card_rhoImg_mul (φ := φ) h.TH_le_normalizer, rhoImg_TH h, TH_inf_centralizer h,
    card_inf_centralizer_W φ h.t_mem_NW, h.rho_t]

theorem inf_centralizer_eq [Finite G] (h : Stage2Hyp M t TH W φ) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTHT : TH ≤ T) : T ⊓ centralizer ({t} : Set G) = TH :=
  eq_of_isPGroup_of_not_dvd h.TH_index (hT2.to_le inf_le_left) (le_inf hTHT h.TH_le)
    inf_le_right

theorem card_le_eight [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M) (E : Subgroup G)
    (hE : E ≤ centralizer ({t} : Set G)) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ 8 := by
  have hoff := hF.offender_m2
  rw [← h.rho_t] at hoff
  refine card_le_of_le_centralizer h.TH_index h.TH_le h.TH_le_normalizer h.sylow_W h.rho_TH
    h.t_mem_NW hoff ?_ E hE hsq
  rw [h.rho_t, hF.card_fixM_tbar]
  norm_num

theorem card_fixM_le' [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M) {u g : G}
    (hu : u = g * t * g⁻¹) (hun : u ∈ NW W) : Nat.card (fixM (rhoG W φ u : Mat12)) ≤ 2 ^ 7 := by
  rw [← card_inf_centralizer_W φ hun]
  set X : Subgroup G := W ⊓ centralizer ({u} : Set G) with hX
  have hu2 : u * u = 1 := by rw [hu]; exact h.conj_mul_self g
  have hcX : ∀ x ∈ X, x * u = u * x := fun x hx => mem_centralizer_singleton_iff.1 hx.2
  set Y : Subgroup G := X ⊔ zpowers u with hY
  have hYsq : ∀ y ∈ Y, y * y = 1 := by
    intro y hy
    obtain ⟨x, hx, e | e⟩ := (mem_sup_zpowers_iff hu2 hcX).1 hy <;> rw [e]
    · exact W_mem_sq φ hx.1
    · calc x * u * (x * u) = x * (u * x) * u := by group
        _ = x * (x * u) * u := by rw [hcX x hx]
        _ = 1 := by rw [← mul_assoc, W_mem_sq φ hx.1, one_mul, hu2]
  set E : Subgroup G := Y.map (MulAut.conj g⁻¹).toMonoidHom with hE
  have hYu : ∀ y ∈ Y, y * u = u * y := by
    intro y hy
    obtain ⟨x, hx, e | e⟩ := (mem_sup_zpowers_iff hu2 hcX).1 hy <;> rw [e]
    · exact hcX x hx
    · calc x * u * u = x * (u * u) := by group
        _ = u * (u * x) := by rw [hu2, mul_one, ← mul_assoc, hu2, one_mul]
        _ = u * (x * u) := by rw [hcX x hx]
  have hEt : E ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    have e := hYu y hy
    rw [hu] at e
    calc g⁻¹ * y * g * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [e]
      _ = t * (g⁻¹ * y * g) := by group
  have hEsq : ∀ z ∈ E, z * z = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hYsq y hy]; group
  have hcE : Nat.card E = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hle := card_le_eight h hF E hEt hEsq
  rw [hcE] at hle
  by_cases huX : u ∈ X
  · exfalso
    have hXW : X = W := by
      refine le_antisymm inf_le_left fun w hw => ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
      exact congrArg Subtype.val (W_comm φ ⟨w, hw⟩ ⟨u, huX.1⟩)
    have h1 : Nat.card X ≤ Nat.card Y := Subgroup.card_le_of_le le_sup_left
    rw [hXW, card_W φ] at h1
    have := h1.trans hle
    norm_num at this
  · rw [card_sup_zpowers hu2 huX hcX] at hle
    omega

end Hyp

end CFSG.EvenSmallLie.OmegaEight.N3Split
