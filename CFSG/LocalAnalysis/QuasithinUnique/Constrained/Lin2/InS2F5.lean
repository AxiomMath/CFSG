module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem sq_factors {r₁ r₂ : G} (hr₁ : r₁ ∈ L) (hr₂ : r₂ ∈ conjR L t) (h : (r₁ * r₂) * (r₁ * r₂) = 1) :
    r₁ * r₁ = 1 ∧ r₂ * r₂ = 1 := by
  have hB := O.base
  have hc : r₂ * r₁ = r₁ * r₂ := (hB.comm_elem r₁ hr₁ r₂ hr₂).symm
  have h1 : (r₁ * r₁) * (r₂ * r₂) = 1 * 1 := by
    calc (r₁ * r₁) * (r₂ * r₂) = r₁ * (r₁ * r₂) * r₂ := by group
      _ = r₁ * (r₂ * r₁) * r₂ := by rw [hc]
      _ = (r₁ * r₂) * (r₁ * r₂) := by group
      _ = 1 * 1 := by rw [h, one_mul]
  exact exists_unique_of_inf_bot hB.L_inf_L₂ (L.mul_mem hr₁ hr₁) L.one_mem
    ((conjR L t).mul_mem hr₂ hr₂) ((conjR L t).one_mem) h1

theorem card_inf_R_le_sq_nonswap {A : Subgroup G} (hA : A ≤ M₀) (hsq : ∀ e ∈ A, e * e = 1) {a : G}
    (haA : a ∈ A) (haS : a ∉ S)
    (h1 : conjR (thompsonJ S ⊓ L) a = thompsonJ S ⊓ L)
    (h2 : conjR (thompsonJ S ⊓ conjR L t) a = thompsonJ S ⊓ conjR L t) :
    Nat.card ↥(A ⊓ thompsonJ S) ≤ q ^ 2 := by
  have hB := O.base
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := comm_of_sq hsq
  have ha2 : a * a = 1 := hsq a haA
  have hUa₁ := O.conjR_U₁_of_nonswap (hA haA) haS h1
  have hUa₂ : conjR (blockU (conjR L t)) a = conjR (blockU (conjR L t)) x₀ := by
    rw [DoubleA3.blockU_conjR]
    exact O.conjR_U₂_of_nonswap (hA haA) haS h2
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hB.su.loc.q2
  have hWL : W ≤ L := hB.su.loc.rk.W_le_U.trans (blockU_le L)
  have hsub : A ⊓ thompsonJ S ≤ W ⊔ conjR W t := by
    rintro e ⟨heA, heR⟩
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := O.R_decomp' heR
    have hea : a * (r₁ * r₂) * a⁻¹ = r₁ * r₂ := by
      have hae := hcomm a haA (r₁ * r₂) heA
      calc a * (r₁ * r₂) * a⁻¹ = (r₁ * r₂) * a * a⁻¹ := by rw [hae]
        _ = r₁ * r₂ := by group
    have hr₁a : a * r₁ * a⁻¹ ∈ thompsonJ S ⊓ L := by
      have : r₁ ∈ conjR (thompsonJ S ⊓ L) a := by rw [h1]; exact hr₁
      exact mem_conjR.1 this
    have hr₂a : a * r₂ * a⁻¹ ∈ thompsonJ S ⊓ conjR L t := by
      have : r₂ ∈ conjR (thompsonJ S ⊓ conjR L t) a := by rw [h2]; exact hr₂
      exact mem_conjR.1 this
    have huniq := exists_unique_of_inf_bot hB.L_inf_L₂ hr₁a.2 hr₁.2 hr₂a.2 hr₂.2
      (by rw [← hea]; group)
    have hsq' := hsq _ heA
    obtain ⟨hs₁, hs₂⟩ := O.sq_factors hr₁.2 hr₂.2 hsq'
    have hc₁ : r₁ * a = a * r₁ := by
      have := huniq.1
      calc r₁ * a = (a * r₁ * a⁻¹) * a := by rw [this]
        _ = a * r₁ := by group
    have hc₂ : r₂ * a = a * r₂ := by
      have := huniq.2
      calc r₂ * a = (a * r₂ * a⁻¹) * a := by rw [this]
        _ = a * r₂ := by group
    have hW₁ : r₁ ∈ W := O.UT3_R₁.mem_W_of_swap hUa₁ ha2 hr₁ hs₁ hc₁
    have hW₂ : r₂ ∈ conjR W t := O.UT3_R₂.mem_W_of_swap hUa₂ ha2 hr₂ hs₂ hc₂
    exact (W ⊔ conjR W t).mul_mem (Subgroup.mem_sup_left hW₁) (Subgroup.mem_sup_right hW₂)
  have hN : W ≤ Subgroup.normalizer ((conjR W t : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun x hx y hy =>
      (hB.comm_elem y (hWL hy) x (conjR_mono hWL t hx)).symm
  have hcard := card_sup_mul_card_inf hN
  have hW : Nat.card W = q := O.UT3_R₁.card_W
  have hW₂ : Nat.card (conjR W t) = q := by rw [card_conjR, hW]
  have hpos : 0 < Nat.card ↥(W ⊓ conjR W t) := Nat.card_pos
  have hle : Nat.card ↥(W ⊔ conjR W t) ≤ q * q := by
    rw [hW, hW₂] at hcard
    nlinarith
  calc Nat.card ↥(A ⊓ thompsonJ S) ≤ Nat.card ↥(W ⊔ conjR W t) := Subgroup.card_le_of_le hsub
    _ ≤ q * q := hle
    _ = q ^ 2 := by ring

theorem card_inf_R_le_sq_swap {A : Subgroup G} (hsq : ∀ e ∈ A, e * e = 1) {a : G} (haA : a ∈ A)
    (h2 : conjR (thompsonJ S ⊓ conjR L t) a = thompsonJ S ⊓ L) :
    Nat.card ↥(A ⊓ thompsonJ S) ≤ q ^ 2 := by
  have hB := O.base
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := comm_of_sq hsq
  have hR₁N₂ : thompsonJ S ⊓ L ≤
      Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun x hx y hy => (hB.comm_elem y hy.2 x hx.2).symm
  have hRN₂ : thompsonJ S ≤
      Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) := by
    intro r hr
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := O.R_decomp' hr
    exact mul_mem (hR₁N₂ hr₁) (Subgroup.le_normalizer hr₂)
  have hEN : A ⊓ thompsonJ S ≤
      Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
    inf_le_right.trans hRN₂
  have hE₂ : (A ⊓ thompsonJ S) ⊓ (thompsonJ S ⊓ conjR L t) = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨⟨heA, heR⟩, heR₂⟩
    have hae : a * e = e * a := hcomm a haA e heA
    have h1 : a⁻¹ * e * a ∈ conjR (thompsonJ S ⊓ conjR L t) a := mem_conjR_iff'.2 ⟨e, heR₂, rfl⟩
    rw [h2] at h1
    have e1 : a⁻¹ * e * a = e := by
      calc a⁻¹ * e * a = a⁻¹ * (e * a) := by group
        _ = a⁻¹ * (a * e) := by rw [hae]
        _ = e := by group
    rw [e1] at h1
    have : e ∈ (thompsonJ S ⊓ L) ⊓ (thompsonJ S ⊓ conjR L t) := ⟨h1, heR₂⟩
    rw [hB.R₁_inf_R₂] at this
    exact this
  have hF₂ : ((A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t)) ⊓ (thompsonJ S ⊓ L) ⊓
      (thompsonJ S ⊓ conjR L t) = ⊥ := by
    rw [eq_bot_iff, ← hB.R₁_inf_R₂]
    exact inf_le_inf inf_le_right le_rfl
  have hFN : ((A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t)) ⊓ (thompsonJ S ⊓ L) ≤
      Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
    inf_le_right.trans hR₁N₂
  have hsqF : ∀ f ∈ ((A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t)) ⊓ (thompsonJ S ⊓ L),
      f * f = 1 := by
    rintro f ⟨hf, hf₁⟩
    rw [sup_comm] at hf
    obtain ⟨k, hk, e, he, hfe⟩ := (mem_sup_iff_of_le_normalizer hEN).1 hf
    have hfk : f * k⁻¹ = k⁻¹ * f := hB.comm_elem f hf₁.2 k⁻¹ ((conjR L t).inv_mem hk.2)
    have hee : (k⁻¹ * f) * (k⁻¹ * f) = 1 := by
      have : k⁻¹ * f = e := by rw [hfe]; group
      rw [this]
      exact hsq e he.1
    have hprod : (f * f) * (k⁻¹ * k⁻¹) = 1 * 1 := by
      calc (f * f) * (k⁻¹ * k⁻¹) = f * (f * k⁻¹) * k⁻¹ := by group
        _ = f * (k⁻¹ * f) * k⁻¹ := by rw [hfk]
        _ = (f * k⁻¹) * (f * k⁻¹) := by group
        _ = (k⁻¹ * f) * (k⁻¹ * f) := by rw [hfk]
        _ = 1 * 1 := by rw [hee, one_mul]
    exact (exists_unique_of_inf_bot hB.L_inf_L₂ (L.mul_mem hf₁.2 hf₁.2) L.one_mem
      ((conjR L t).mul_mem ((conjR L t).inv_mem hk.2) ((conjR L t).inv_mem hk.2))
      (conjR L t).one_mem hprod).1
  have hEF : (A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t) ≤
      (((A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t)) ⊓ (thompsonJ S ⊓ L)) ⊔
        (thompsonJ S ⊓ conjR L t) := by
    refine sup_le (fun e he => ?_) le_sup_right
    obtain ⟨r₁, hr₁, r₂, hr₂, hdec⟩ := O.R_decomp' he.2
    have h1 : r₁ ∈ (A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t) := by
      have : r₁ = e * r₂⁻¹ := by rw [hdec]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.inv_mem _
        (Subgroup.mem_sup_right hr₂))
    rw [hdec]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h1, hr₁⟩) (Subgroup.mem_sup_right hr₂)
  have hc₁ := card_sup_mul_card_inf hEN
  have hc₂ := card_sup_mul_card_inf hFN
  rw [hE₂, Subgroup.card_bot, mul_one] at hc₁
  rw [hF₂, Subgroup.card_bot, mul_one] at hc₂
  have hpos : 0 < Nat.card ↥(thompsonJ S ⊓ conjR L t) := Nat.card_pos
  have hcard : Nat.card ↥(A ⊓ thompsonJ S) ≤
      Nat.card ↥(((A ⊓ thompsonJ S) ⊔ (thompsonJ S ⊓ conjR L t)) ⊓ (thompsonJ S ⊓ L)) := by
    have h3 := Subgroup.card_le_of_le hEF
    rw [hc₁, hc₂] at h3
    exact Nat.le_of_mul_le_mul_right h3 hpos
  exact hcard.trans (O.UT3_R₁.card_le_sq inf_le_right hsqF)

theorem card_inf_R_le_sq {A : Subgroup G} (hA : A ≤ M₀) (hsq : ∀ e ∈ A, e * e = 1) {a : G}
    (haA : a ∈ A) (haS : a ∉ S) : Nat.card ↥(A ⊓ thompsonJ S) ≤ q ^ 2 := by
  rcases O.R_perm_M₀ (hA haA) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact O.card_inf_R_le_sq_nonswap hA hsq haA haS h1 h2
  · exact O.card_inf_R_le_sq_swap hsq haA h2

end S2Ok

end CFSG.QuasithinUnique.Lin2
