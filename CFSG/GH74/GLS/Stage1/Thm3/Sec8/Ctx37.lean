module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx36
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx22
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Sig810 {G : Type} [Group G] (S K₁ W₂ : Subgroup G) (h t : G) (Sg : Subgroup G) : Prop :=
  zpowers h ⊔ zpowers t ≤ Sg ∧ Aof S K₁ W₂ h ⊓ Sg = ⊥ ∧ S ⊔ zpowers h = Aof S K₁ W₂ h ⊔ Sg ∧
    ∃ _ : ((zpowers (h ^ 3)).subgroupOf Sg).Normal,
      Nonempty ((↥Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) ≃* Equiv.Perm (Fin 4))

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
variable {Y D E₁ E₂ : Subgroup G} {t w : G}

theorem exists_Sigma (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) (hE : EData Y U E₁ E₂) (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    ∃ Sg : Subgroup G, Sig810 S K₁ W₂ h t Sg := by
  obtain ⟨m, hm⟩ := hs.h_order
  obtain ⟨htS, ht2, hth, htu⟩ := t_facts hC
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ 2 := by norm_num; omega
  have hYS := Y_le_S hC
  have hYW := Y_le_W hE hC
  have hE₁Y : E₁ ≤ Y := hE.le₁
  have hsq := E₁_sq hE
  have hUE₁ : U ≤ E₁ := hE.inter ▸ inf_le_left
  have htE := hs.E₁_tnorm hII hq hrec hP8 hS7 hE hC
  have hhE := hs.E₁_hnorm hE hC
  have hh3 : ∀ x ∈ E₁, h ^ 3 * x = x * h ^ 3 := fun x hx => hs.h_cube x (hYW (hE₁Y hx))
  have hCh : ∀ x ∈ E₁, h * x = x * h → x = 1 := fun x hx hc => hC.2.2.1.2.2.2.2 x (hE₁Y hx) hc
  have hUh : ∀ x ∈ U, h⁻¹ * x * h ∈ U := fun x hx => hs.U_conj_h hx
  have htz : t * z * t⁻¹ = z := by
    rw [← hs.z_comm hII htS]
    group
  have hCU : ∀ x ∈ U, t * x * t⁻¹ = x → x = 1 ∨ x = z := by
    intro x hx hxt
    rcases hs.U_elems x hx with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      rw [h1, htu] at hxt
      apply hs.z_ne
      have : u * z = u * 1 := by rw [mul_one]; exact hxt
      exact mul_left_cancel this
    · exfalso
      rw [h1] at hxt
      have h2 : t * (u * z) * t⁻¹ = u := by
        calc t * (u * z) * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) := by group
          _ = (u * z) * z := by rw [htu, htz]
          _ = u := by rw [mul_assoc, hs.z_sq, mul_one]
      rw [h2] at hxt
      apply hs.z_ne
      have : u * 1 = u * z := by rw [mul_one]; exact hxt
      exact (mul_left_cancel this).symm
  obtain ⟨e, heE, heU, hte⟩ := Basic.exists_fixed_outside (E := E₁) (U := U) (t := t) (z := z)
    hsq hE.elem₁.1 hE.card₁ ht2 htE hCU
  obtain ⟨e₁, e₂, hD, he₁E, he₂E, hE0U⟩ := Basic.exists_trio (E := E₁) (U := U) (h := h) (t := t)
    (e := e) (m := m) hsq hE.elem₁.1 hhE hh3 hCh hUh hm ht2 hth heE heU hte
  have hE0E₁ : zpowers e ⊔ zpowers e₁ ≤ E₁ := sup_le (zpowers_le.2 heE) (zpowers_le.2 he₁E)
  have hE0Y : zpowers e ⊔ zpowers e₁ ≤ Y := hE0E₁.trans hE₁Y
  have hEH : (zpowers e ⊔ zpowers e₁) ⊓ (zpowers h ⊔ zpowers t) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ (zpowers h ⊔ zpowers t) ⊓ Y := Subgroup.mem_inf.2 ⟨hg.2, hE0Y hg.1⟩
    rw [hs.H_inf_Y hII hC, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  have hA_inf : Aof S K₁ W₂ h ⊓ ((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨n, hn, e₀, he₀, hge⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers h ⊔ zpowers t)
      (B := zpowers e ⊔ zpowers e₁) hD.H_le_normalizer
      (sup_comm (zpowers e ⊔ zpowers e₁) (zpowers h ⊔ zpowers t) ▸ hg.2)
    have hgY : g ∈ Y := hC.2.2.1.1 hg.1
    have he₀Y : e₀ ∈ Y := hE0Y he₀
    have hnY : n ∈ Y := by
      have : n = g * e₀⁻¹ := by rw [hge]; group
      rw [this]
      exact mul_mem hgY (inv_mem he₀Y)
    have hn1 : n = 1 := by
      have : n ∈ (zpowers h ⊔ zpowers t) ⊓ Y := Subgroup.mem_inf.2 ⟨hn, hnY⟩
      rwa [hs.H_inf_Y hII hC, Subgroup.mem_bot] at this
    rw [hn1, one_mul] at hge
    have he₀A : e₀ ∈ Aof S K₁ W₂ h := hge ▸ hg.1
    have he₀U : e₀ ∈ U := hs.A_inv_mem_U hII hq hrec he₀A (hsq e₀ (hE0E₁ he₀))
    have : e₀ ∈ (zpowers e ⊔ zpowers e₁) ⊓ U := Subgroup.mem_inf.2 ⟨he₀, he₀U⟩
    rw [hE0U, Subgroup.mem_bot] at this
    rw [hge, this]
    exact one_mem _
  refine ⟨(zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t), le_sup_right, hA_inf, ?_, hD.iso hEH⟩
  have hAnorm : ∀ x ∈ zpowers e ⊔ zpowers e₁, ∀ a ∈ Aof S K₁ W₂ h,
      x * a * x⁻¹ ∈ Aof S K₁ W₂ h := fun x hx a ha =>
    hs.A_normS hII hq hrec (hYS (hE0Y hx)) ha
  have hE0A : zpowers e ⊔ zpowers e₁ ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) := by
    intro x hx
    exact Basic.mem_normalizer_of_invol (hsq x (hE0E₁ hx)) (fun p hp => hAnorm x hx p hp)
  have hbot : Aof S K₁ W₂ h ⊓ (zpowers e ⊔ zpowers e₁) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ Aof S K₁ W₂ h ⊓ ((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t)) :=
      Subgroup.mem_inf.2 ⟨hg.1, Subgroup.mem_sup_left hg.2⟩
    rwa [hA_inf] at this
  have hAEcard : Nat.card ↥(Aof S K₁ W₂ h ⊔ (zpowers e ⊔ zpowers e₁)) = 64 := by
    have h1 := Basic.card_sup_mul_card_inf' (A := Aof S K₁ W₂ h) (B := zpowers e ⊔ zpowers e₁) hE0A
    rw [hbot, Subgroup.card_bot, mul_one, hs.card_A hII hq hrec hk, hD.card_E₀] at h1
    omega
  have hAEY : Aof S K₁ W₂ h ⊔ (zpowers e ⊔ zpowers e₁) = Y := by
    have hle : Aof S K₁ W₂ h ⊔ (zpowers e ⊔ zpowers e₁) ≤ Y := sup_le hC.2.2.1.1 hE0Y
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hs.card_Y hE, hAEcard])
  have hSeq := hs.S_eq_Y_t hII hS7 hE hC
  have hNle := hC.2.2.1.2.1
  have hth : zpowers h ≤ S ⊔ zpowers h := le_sup_right
  have htS' : zpowers t ≤ S := zpowers_le.2 htS
  apply le_antisymm
  · apply sup_le
    · refine hSeq.le.trans (sup_le ?_ ?_)
      · calc Y = Aof S K₁ W₂ h ⊔ (zpowers e ⊔ zpowers e₁) := hAEY.symm
          _ ≤ Aof S K₁ W₂ h ⊔ ((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t)) :=
            sup_le_sup le_rfl le_sup_left
      · exact (zpowers_le.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))).trans
          (le_sup_right.trans le_sup_right)
    · exact (zpowers_le.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers h))).trans
        (le_sup_right.trans le_sup_right)
  · apply sup_le
    · exact hC.2.2.1.1.trans hNle
    · apply sup_le
      · exact hE0Y.trans hNle
      · exact sup_le hth (htS'.trans le_sup_left)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
