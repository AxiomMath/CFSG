module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx35
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem h_order (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : ∃ m : ℕ, orderOf h = 3 ^ (m + 1) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hs.h_three
  rw [Nat.card_zpowers] at hn
  have hh1 : h ≠ 1 := by
    intro h1
    apply hs.h_move
    rw [h1]
    group
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hh1 (orderOf_eq_one_iff.1 (by simpa using hn))
  exact ⟨n - 1, by rw [hn]; congr 1; omega⟩

theorem h_sq_ne (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : h * h ≠ 1 := by
  obtain ⟨m, hm⟩ := hs.h_order
  intro h1
  have h2 : h ^ 2 = 1 := by rw [pow_two]; exact h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hm] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 3 ^ 1 ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem S_inf_h (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ S)
    (hxh : x ∈ zpowers h) : x = 1 := by
  obtain ⟨m, hm⟩ := hs.h_order
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (hs.S_pgroup hII)) ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hx]
    exact hk
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxh
  have h1 : orderOf (h ^ i) ∣ 3 ^ (m + 1) := by
    rw [← hm]
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  rw [hk'] at h1
  have h2 : Nat.Coprime (2 ^ k) (3 ^ (m + 1)) := Nat.Coprime.pow _ _ (by norm_num)
  have h3 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd h2 h1
  rw [h3] at hk'
  exact orderOf_eq_one_iff.1 hk'

section Y8

variable {Y D E₁ E₂ : Subgroup G} {t w : G}

theorem Y_le_S (hC : Concl86 z S K₁ W₂ U u h Y D t w) : Y ≤ S := by
  rw [hC.2.1]
  exact le_sup_left

theorem Y_norm_S (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    ∀ x ∈ S, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy =>
  hC.2.2.1.2.2.1 x ((le_sup_left : S ≤ S ⊔ zpowers h) hx) y hy

theorem Y_norm_h (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    ∀ y ∈ Y, h * y * h⁻¹ ∈ Y := fun y hy =>
  hC.2.2.1.2.2.1 h (Subgroup.mem_sup_right (Subgroup.mem_zpowers h)) y hy

theorem Y_norm_h_inv (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    ∀ y ∈ Y, h⁻¹ * y * h ∈ Y := fun y hy => by
  have := hC.2.2.1.2.2.1 h⁻¹ (inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers h))) y hy
  simpa using this

theorem card_Y (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hE : EData Y U E₁ E₂) : Nat.card ↥Y = 64 := by
  have hUE₂ : U ≤ E₂ := hE.inter ▸ inf_le_right
  have key : ∀ e ∈ E₁, ∀ f ∈ E₂, e * f * e⁻¹ ∈ E₂ := fun e he f hf => by
    have h1 := hE.comm e he f hf
    have h2 : e * f * e⁻¹ = (e * f * e⁻¹ * f⁻¹) * f := by group
    rw [h2]
    exact mul_mem (hUE₂ h1) hf
  have hN : E₁ ≤ normalizer (E₂ : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · exact key e he f
    · intro hf
      have h3 := key e⁻¹ (inv_mem he) _ hf
      have h4 : e⁻¹ * (e * f * e⁻¹) * e⁻¹⁻¹ = f := by group
      rw [h4] at h3
      exact h3
  have h1 := Basic.card_sup_mul_card_inf' (A := E₂) (B := E₁) hN
  rw [sup_comm, hE.prod, inf_comm, hE.inter, hs.U_four.2, hE.card₂, hE.card₁] at h1
  omega

theorem t_facts (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    t ∈ S ∧ t * t = 1 ∧ t * h * t⁻¹ = h⁻¹ ∧ t * u * t⁻¹ = u * z := by
  obtain ⟨htP, hto, htu, hth⟩ := hC.2.2.2.2.1
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hto
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv] at hth htu
  refine ⟨htP.1, ht2, ?_, ?_⟩
  · rw [htinv]
    exact hth
  · rw [htinv]
    exact htu

theorem t_not_mem_Y (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hC : Concl86 z S K₁ W₂ U u h Y D t w) : t ∉ Y := by
  intro htY
  obtain ⟨htS, ht2, hth, -⟩ := t_facts hC
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 : h * t * h⁻¹ ∈ Y := Y_norm_h hC t htY
  have h2 : (h * t * h⁻¹) * t⁻¹ ∈ Y := mul_mem h1 (inv_mem htY)
  have h3 : (h * t * h⁻¹) * t⁻¹ = h * h := by
    have h4 : t * h⁻¹ * t⁻¹ = h := by
      calc t * h⁻¹ * t⁻¹ = (t * h * t⁻¹)⁻¹ := by group
        _ = h := by rw [hth, inv_inv]
    calc (h * t * h⁻¹) * t⁻¹ = h * (t * h⁻¹ * t⁻¹) := by group
      _ = h * h := by rw [h4]
  rw [h3] at h2
  have h4 : h * h ∈ S := Y_le_S hC h2
  have h5 : h * h ∈ zpowers h := mul_mem (Subgroup.mem_zpowers h) (Subgroup.mem_zpowers h)
  exact hs.h_sq_ne (hs.S_inf_h hII h4 h5)

theorem H_inf_Y (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hC : Concl86 z S K₁ W₂ U u h Y D t w) : (zpowers h ⊔ zpowers t) ⊓ Y = ⊥ := by
  obtain ⟨htS, ht2, hth, -⟩ := t_facts hC
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨b, hb, a, ha, hgba⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers t) (B := zpowers h)
    (Basic.zpowers_t_le_normalizer ht2 hth) (sup_comm (zpowers h) (zpowers t) ▸ hg.1)
  have hgS : g ∈ S := Y_le_S hC hg.2
  have hbS : b ∈ S := by
    rcases (Basic.mem_zpowers_of_sq' ht2).1 hb with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact htS
  have haS : a ∈ S := by
    have : a = b⁻¹ * g := by rw [hgba]; group
    rw [this]
    exact mul_mem (inv_mem hbS) hgS
  have ha1 : a = 1 := hs.S_inf_h hII haS ha
  rw [ha1, mul_one] at hgba
  rcases (Basic.mem_zpowers_of_sq' ht2).1 hb with h1 | h1
  · rw [hgba, h1]
    exact one_mem _
  · exfalso
    rw [h1] at hgba
    exact hs.t_not_mem_Y hII hC (hgba ▸ hg.2)

theorem S_eq_Y_t (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hS7 : Nat.card ↥S = 2 ^ 7) (hE : EData Y U E₁ E₂) (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    S = Y ⊔ zpowers t := by
  obtain ⟨htS, ht2, hth, -⟩ := t_facts hC
  have hY64 := hs.card_Y hE
  have hN : zpowers t ≤ normalizer (Y : Set G) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Y_norm_S hC t htS y hy
    · intro hy
      have := Y_norm_S hC t⁻¹ (inv_mem htS) _ hy
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rwa [e] at this
  have hbot : Y ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases (Basic.mem_zpowers_of_sq' ht2).1 hg.2 with h1 | h1
    · rw [h1]
      exact one_mem _
    · exfalso
      exact hs.t_not_mem_Y hII hC (h1 ▸ hg.1)
  have hcard := Basic.card_sup_mul_card_inf' (A := Y) (B := zpowers t) hN
  have ht1 : t ≠ 1 := by
    intro h1
    have := hth
    rw [h1] at this
    apply hs.h_sq_ne
    have : h = h⁻¹ := by simpa using this
    exact mul_eq_one_iff_eq_inv.2 this
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1, hY64] at hcard
  have hle : Y ⊔ zpowers t ≤ S := sup_le (Y_le_S hC) (zpowers_le.2 htS)
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem Y_le_W (hE : EData Y U E₁ E₂) (hC : Concl86 z S K₁ W₂ U u h Y D t w) : Y ≤ Wsub S U := by
  have hUE₁ : U ≤ E₁ := hE.inter ▸ inf_le_left
  have hUE₂ : U ≤ E₂ := hE.inter ▸ inf_le_right
  have h₁ : E₁ ≤ centralizer (U : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 (fun x hx => hE.elem₁.1 x (hUE₁ hx) e he)
  have h₂ : E₂ ≤ centralizer (U : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 (fun x hx => hE.elem₂.1 x (hUE₂ hx) e he)
  intro y hy
  have hy' : y ∈ E₁ ⊔ E₂ := by
    rw [hE.prod]
    exact hy
  exact Subgroup.mem_inf.2 ⟨Y_le_S hC hy, (sup_le h₁ h₂) hy'⟩

theorem invol_of_EData (hE : EData Y U E₁ E₂) : ∀ x ∈ Y, x * x = 1 → x ∈ E₁ ∨ x ∈ E₂ := by
  intro x hx hx2
  by_cases hx1 : x = 1
  · left
    rw [hx1]
    exact one_mem _
  · exact hE.invol x hx (orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1)

theorem E₁_sq (hE : EData Y U E₁ E₂) : ∀ e ∈ E₁, e * e = 1 := fun e he => by
  have := hE.elem₁.2 e he
  simpa [pow_two] using this

theorem E₂_sq (hE : EData Y U E₁ E₂) : ∀ e ∈ E₂, e * e = 1 := fun e he => by
  have := hE.elem₂.2 e he
  simpa [pow_two] using this

theorem E₁_ne_E₂ (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hE : EData Y U E₁ E₂) : E₁ ≠ E₂ := by
  intro h12
  have h1 := hE.inter
  rw [← h12, inf_idem] at h1
  have h2 := hs.U_four.2
  rw [← h1, hE.card₁] at h2
  omega

theorem conj_sq (g : G) {E : Subgroup G} (hE : ∀ e ∈ E, e * e = 1) :
    ∀ x ∈ conjugate E g, x * x = 1 := by
  intro x hx
  have h1 := hE _ (mem_conjugate_iff.1 hx)
  have h2 : g * (x * x) * g⁻¹ = 1 := by
    rw [show g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) by group]
    exact h1
  calc x * x = g⁻¹ * (g * (x * x) * g⁻¹) * g := by group
    _ = 1 := by rw [h2]; group

theorem E₁_hnorm (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hE : EData Y U E₁ E₂)
    (hC : Concl86 z S K₁ W₂ U u h Y D t w) : ∀ x ∈ E₁, h⁻¹ * x * h ∈ E₁ := by
  have hconjY : ∀ E : Subgroup G, E ≤ Y → conjugate E h ≤ Y := by
    intro E hEY x hx
    have h1 : h * x * h⁻¹ ∈ E := mem_conjugate_iff.1 hx
    have h2 := Y_norm_h_inv hC _ (hEY h1)
    have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rwa [e] at h2
  have hc₁ := Basic.elem_eq_or_of_le (hconjY E₁ hE.le₁) (conj_sq h (E₁_sq hE)) (invol_of_EData hE)
    hE.card₁ hE.card₂ (by rw [conjugate_card]; exact hE.card₁)
  have hc₂ := Basic.elem_eq_or_of_le (hconjY E₂ hE.le₂) (conj_sq h (E₂_sq hE)) (invol_of_EData hE)
    hE.card₁ hE.card₂ (by rw [conjugate_card]; exact hE.card₂)
  have hinj : conjugate E₁ h ≠ conjugate E₂ h := by
    intro h12
    apply E₁_ne_E₂ hs hE
    ext x
    have h1 : x ∈ E₁ ↔ h⁻¹ * x * h ∈ conjugate E₁ h := by
      rw [mem_conjugate_iff]
      have : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rw [this]
    have h2 : x ∈ E₂ ↔ h⁻¹ * x * h ∈ conjugate E₂ h := by
      rw [mem_conjugate_iff]
      have : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rw [this]
    rw [h1, h2, h12]
  have hmain : conjugate E₁ h = E₁ := by
    rcases hc₁ with h1 | h1
    · exact h1
    · exfalso
      rcases hc₂ with h2 | h2
      ·
        have hW : E₁ ≤ Wsub S U := (hE.prod ▸ le_sup_left : E₁ ≤ Y).trans (Y_le_W hE hC)
        have hall : ∀ e ∈ E₁, e ∈ U := by
          intro e he
          have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
          have hcen : (h * h * h) * e = e * (h * h * h) := by
            have := hs.h_cube e (hW he)
            rwa [e3] at this
          have h3 : h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h = e := by
            calc h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h = (h * h * h)⁻¹ * (e * (h * h * h)) := by group
              _ = (h * h * h)⁻¹ * ((h * h * h) * e) := by rw [hcen]
              _ = e := by group
          have a1 : h⁻¹ * e * h ∈ E₂ := by
            rw [← h1]
            rw [mem_conjugate_iff]
            have : h * (h⁻¹ * e * h) * h⁻¹ = e := by group
            rw [this]
            exact he
          have a2 : h⁻¹ * (h⁻¹ * e * h) * h ∈ E₁ := by
            rw [← h2]
            rw [mem_conjugate_iff]
            have : h * (h⁻¹ * (h⁻¹ * e * h) * h) * h⁻¹ = h⁻¹ * e * h := by group
            rw [this]
            exact a1
          have a3 : h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h ∈ E₂ := by
            rw [← h1]
            rw [mem_conjugate_iff]
            have : h * (h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h) * h⁻¹ =
                h⁻¹ * (h⁻¹ * e * h) * h := by group
            rw [this]
            exact a2
          rw [h3] at a3
          rw [← hE.inter]
          exact Subgroup.mem_inf.2 ⟨he, a3⟩
        have := Subgroup.card_le_of_le (fun x hx => hall x hx : E₁ ≤ U)
        rw [hE.card₁, hs.U_four.2] at this
        omega
      · exact hinj (h1.trans h2.symm)
  intro x hx
  have : h⁻¹ * x * h ∈ conjugate E₁ h := by
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rw [e]
    exact hx
  rwa [hmain] at this

theorem E₁_tnorm (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) (hE : EData Y U E₁ E₂) (hC : Concl86 z S K₁ W₂ U u h Y D t w) :
    ∀ x ∈ E₁, t * x * t⁻¹ ∈ E₁ := by
  obtain ⟨htP, hto, htu, hth⟩ := hC.2.2.2.2.1
  have h87 := lemma_8_7 hII hq hrec G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7.ge hC E₁ E₂ hE t htP hto htu
  intro x hx
  rw [← h87.1] at hx
  exact mem_conjugate_iff.1 hx

end Y8

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
