module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneJhatBase

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

variable {G : Type} [Group G]

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem C_le_J (h : JBase τ lev z ν A D C E Dh) : C ≤ Dh ⊓ centralizer (E : Set G) :=
  fun _ hc => mem_inf.2 ⟨h.C_le_Dh hc, mem_centralizer_iff.2 fun _ hx => h.comm_of_mem hx hc⟩

theorem conj_mem_J (h : JBase τ lev z ν A D C E Dh) {t x : G} (ht : t ∈ Dh)
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) : t * x * t⁻¹ ∈ Dh ⊓ centralizer (E : Set G) := by
  refine mem_inf.2 ⟨mul_mem (mul_mem ht (mem_inf.1 hx).1) (inv_mem ht),
    mem_centralizer_iff.2 fun e he => ?_⟩
  have h1 := mem_centralizer_iff.1 (mem_inf.1 hx).2 _ (h.conj_inv_mem_E ht he)
  calc e * (t * x * t⁻¹) = t * ((t⁻¹ * e * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * e * t)) * t⁻¹ := by rw [h1]
    _ = t * x * t⁻¹ * e := by group

theorem lev_conj_mem_E (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {x : G}
    (hx : x ∈ E) : lev g * x * (lev g)⁻¹ ∈ E := by
  obtain ⟨h1, h2⟩ := h.ν_lev g x (h.E_C hx)
  refine (h.ν_E _ h1).1 ?_
  rw [h2, symThreeDiag_coe_congr, h.dν_E hx, mulVec_zero]

theorem lev_conj_mem_J (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {x : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) :
    lev g * x * (lev g)⁻¹ ∈ Dh ⊓ centralizer (E : Set G) := by
  refine mem_inf.2 ⟨h.lev_Dh g x (mem_inf.1 hx).1, mem_centralizer_iff.2 fun e he => ?_⟩
  have he' : (lev g)⁻¹ * e * lev g ∈ E := by
    have := h.lev_conj_mem_E g⁻¹ he
    rwa [map_inv, inv_inv] at this
  have h1 := mem_centralizer_iff.1 (mem_inf.1 hx).2 _ he'
  calc e * (lev g * x * (lev g)⁻¹) = lev g * (((lev g)⁻¹ * e * lev g) * x) * (lev g)⁻¹ := by
        group
    _ = lev g * (x * ((lev g)⁻¹ * e * lev g)) * (lev g)⁻¹ := by rw [h1]
    _ = lev g * x * (lev g)⁻¹ * e := by group

theorem good_D (h : JBase τ lev z ν A D C E Dh) {d : G} (hd : d ∈ D) :
    d ∈ Dh ⊓ centralizer (E : Set G) ∨ d * z ∈ Dh ⊓ centralizer (E : Set G) := by
  rcases h.D_C d hd with hc | hc
  · exact Or.inl (h.C_le_J hc)
  · right
    have e : d * z = z * (z * d) * z⁻¹ := by
      rw [h.z_inv, ← mul_assoc, h.z_sq, one_mul]
    rw [e]
    exact h.conj_mem_J h.z_Dh (h.C_le_J hc)

theorem good_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {t : G}
    (ht : t ∈ Dh ⊓ centralizer (E : Set G) ∨ t * z ∈ Dh ⊓ centralizer (E : Set G)) :
    lev g * t * (lev g)⁻¹ ∈ Dh ⊓ centralizer (E : Set G) ∨
      lev g * t * (lev g)⁻¹ * z ∈ Dh ⊓ centralizer (E : Set G) := by
  rcases ht with ht | ht
  · exact Or.inl (h.lev_conj_mem_J g ht)
  · right
    have e : lev g * t * (lev g)⁻¹ * z = lev g * (t * z) * (lev g)⁻¹ := by
      have hz : (lev g)⁻¹ * z = z * (lev g)⁻¹ := by
        rw [← map_inv]
        exact h.lev_z g⁻¹
      rw [mul_assoc (lev g * t), hz]
      group
    rw [e]
    exact h.lev_conj_mem_J g ht

theorem good_mul_D (h : JBase τ lev z ν A D C E Dh) {t d : G}
    (ht : t ∈ Dh ⊓ centralizer (E : Set G) ∨ t * z ∈ Dh ⊓ centralizer (E : Set G))
    (hd : d ∈ D) :
    d * t ∈ Dh ⊓ centralizer (E : Set G) ∨ d * t * z ∈ Dh ⊓ centralizer (E : Set G) := by
  have hz' : z⁻¹ ∈ Dh := inv_mem h.z_Dh
  rcases h.good_D hd with hd' | hd' <;> rcases ht with ht | ht
  · exact Or.inl (mul_mem hd' ht)
  · right
    rw [mul_assoc]
    exact mul_mem hd' ht
  · right
    have e : d * t * z = (d * z) * (z⁻¹ * t * z⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem hd' (h.conj_mem_J hz' ht)
  · left
    have e : d * t = (d * z) * (z⁻¹ * (t * z) * z⁻¹⁻¹) := by
      calc d * t = d * t * (z * z) := by rw [h.z_sq, mul_one]
        _ = (d * z) * (z⁻¹ * (t * z) * z⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem hd' (h.conj_mem_J hz' ht)

theorem yt_fix (h : JBase τ lev z ν A D C E Dh) (p : GL (Fin 3) (ZMod 2))
    (hp : ∀ i : Fin 3, symThreeCongr p⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => (p : M₃) i j))
    (hpe : (p : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0]) {t₁ : G} (ht₁ : t₁ ∈ Dh)
    (hw₁ : wvec z ν t₁ = ![1, 0, 0]) :
    actY p (yt τ E ν t₁) = yt τ E ν t₁ ∨ actY p (yt τ E ν t₁) = yt τ E ν t₁ + iotaY := by
  have ht' : lev p * t₁ * (lev p)⁻¹ ∈ Dh := h.lev_Dh p t₁ ht₁
  have hw' : wvec z ν (lev p * t₁ * (lev p)⁻¹) = wvec z ν t₁ := by
    rw [h.wvec_lev p ht₁, hw₁, hpe]
  have hd := h.mul_inv_mem_D ht' ht₁ hw'
  have e : lev p * t₁ * (lev p)⁻¹ = (lev p * t₁ * (lev p)⁻¹ * t₁⁻¹) * t₁ := by group
  rw [← h.yt_lev p hp ht₁, e, h.yt_mul (h.D_Dh hd) ht₁]
  rcases h.yt_D hd with h0 | h0 <;> rw [h0]
  · exact Or.inl (zero_add _)
  · exact Or.inr (add_comm _ _)

theorem yt_sum (h : JBase τ lev z ν A D C E Dh) {t₁ : G} (ht₁ : t₁ ∈ Dh)
    (hw₁ : wvec z ν t₁ = ![1, 0, 0]) :
    yt τ E ν t₁ + actY glSwapOneTwo (yt τ E ν t₁) + actY glRot⁻¹ (yt τ E ν t₁) = 0 ∨
      yt τ E ν t₁ + actY glSwapOneTwo (yt τ E ν t₁) + actY glRot⁻¹ (yt τ E ν t₁) =
        iotaY := by
  have ht₂ := h.lev_Dh glSwapOneTwo t₁ ht₁
  have ht₃ := h.lev_Dh glRot⁻¹ t₁ ht₁
  have hd : t₁ * (lev glSwapOneTwo * t₁ * (lev glSwapOneTwo)⁻¹) *
      (lev glRot⁻¹ * t₁ * (lev glRot⁻¹)⁻¹) ∈ D := by
    rw [← h.wvec_eq_zero_iff (mul_mem (mul_mem ht₁ ht₂) ht₃), h.wvec_mul (mul_mem ht₁ ht₂) ht₃,
      h.wvec_mul ht₁ ht₂, h.wvec_lev _ ht₁, h.wvec_lev _ ht₁, hw₁, glSwapOneTwo_e1,
      glRot_inv_e1]
    decide
  rw [← h.yt_lev glSwapOneTwo inv_alt_glSwapOneTwo ht₁, ← h.yt_lev glRot⁻¹ inv_alt_glRot_inv ht₁,
    ← h.yt_mul ht₁ ht₂, ← h.yt_mul (mul_mem ht₁ ht₂) ht₃]
  exact h.yt_D hd

theorem yt_add_self (y : Fin 3 → 𝕊) : y + y = 0 := by
  funext i
  exact sym_add_self (y i)

theorem good_all (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) :
    t ∈ Dh ⊓ centralizer (E : Set G) ∨ t * z ∈ Dh ⊓ centralizer (E : Set G) := by
  obtain ⟨t₁, ht₁, hw₁⟩ := h.exists_wvec ![1, 0, 0]
  have hy := eq_zero_or_eq_iotaY (yt τ E ν t₁)
    (h.yt_fix _ inv_alt_glSwapTwoThree glSwapTwoThree_e1 ht₁ hw₁)
    (h.yt_fix _ inv_alt_glTransTwoOne glTransTwoOne_e1 ht₁ hw₁)
    (h.yt_fix _ inv_alt_glTransThreeTwo glTransThreeTwo_e1 ht₁ hw₁) (h.yt_sum ht₁ hw₁)
  have hgood₁ : t₁ ∈ Dh ⊓ centralizer (E : Set G) ∨
      t₁ * z ∈ Dh ⊓ centralizer (E : Set G) := by
    rcases hy with hy | hy
    · exact Or.inl (mem_inf.2 ⟨ht₁, mem_centralizer_iff.2 fun x hx =>
        h.comm_of_yt_eq_zero ht₁ hy hx⟩)
    · right
      have h0 : yt τ E ν (t₁ * z) = 0 := by
        rw [h.yt_mul ht₁ h.z_Dh, hy, h.yt_z, yt_add_self]
      exact mem_inf.2 ⟨mul_mem ht₁ h.z_Dh, mem_centralizer_iff.2 fun x hx =>
        h.comm_of_yt_eq_zero (mul_mem ht₁ h.z_Dh) h0 hx⟩
  by_cases hw : wvec z ν t = 0
  · exact h.good_D ((h.wvec_eq_zero_iff ht).1 hw)
  · obtain ⟨v, hv0, hv⟩ := exists_ne_zero_ne (wvec z ν t)
    obtain ⟨g, hg, -⟩ := exists_gl_pair hw hv0 hv
    have ht' := h.lev_Dh g t₁ ht₁
    have hw' : wvec z ν t = wvec z ν (lev g * t₁ * (lev g)⁻¹) := by
      rw [h.wvec_lev g ht₁, hw₁, hg]
    have hd := h.mul_inv_mem_D ht ht' hw'
    have e : t = (t * (lev g * t₁ * (lev g)⁻¹)⁻¹) * (lev g * t₁ * (lev g)⁻¹) := by group
    rw [e]
    exact h.good_mul_D (h.good_lev g hgood₁) hd

theorem z_not_mem_J (h : JBase τ lev z ν A D C E Dh) : z ∉ Dh ⊓ centralizer (E : Set G) :=
  fun hz => h.z_C (by rw [h.C_eq]; exact mem_inf.2 ⟨h.z_D, (mem_inf.1 hz).2⟩)

theorem J_inf_D (h : JBase τ lev z ν A D C E Dh) : Dh ⊓ centralizer (E : Set G) ⊓ D = C := by
  rw [h.C_eq]
  ext x
  simp only [mem_inf]
  exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨h.D_Dh hx.1, hx.2⟩, hx.1⟩⟩

theorem J_sup_z (h : JBase τ lev z ν A D C E Dh) :
    Dh ⊓ centralizer (E : Set G) ⊔ zpowers z = Dh := by
  apply le_antisymm
  · exact sup_le inf_le_left (zpowers_le.2 h.z_Dh)
  · intro t ht
    rcases h.good_all ht with h1 | h1
    · exact mem_sup_left h1
    · have e : t = t * z * z⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (inv_mem (mem_zpowers z)))

theorem relIndex_J (h : JBase τ lev z ν A D C E Dh) :
    (Dh ⊓ centralizer (E : Set G)).relIndex Dh = 2 := by
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨z, h.z_Dh⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf, coe_mul]
  have hb : (b : G) ∈ Dh := b.2
  rcases h.good_all hb with h1 | h1
  · refine Or.inr ⟨h1, fun h2 => h.z_not_mem_J ?_⟩
    have e : z = (b : G)⁻¹ * ((b : G) * z) := by group
    rw [e]
    exact mul_mem (inv_mem h1) h2
  · refine Or.inl ⟨h1, fun h2 => h.z_not_mem_J ?_⟩
    have e : z = (b : G)⁻¹ * ((b : G) * z) := by group
    rw [e]
    exact mul_mem (inv_mem h2) h1

theorem card_J (h : JBase τ lev z ν A D C E Dh) :
    Nat.card (Dh ⊓ centralizer (E : Set G) : Subgroup G) = 2 ^ 15 := by
  have e := relIndex_mul_card (H := Dh ⊓ centralizer (E : Set G)) (K := Dh)
  rw [h.relIndex_J, h.Dh_card, inf_eq_left.2 inf_le_left] at e
  omega

end JBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat
