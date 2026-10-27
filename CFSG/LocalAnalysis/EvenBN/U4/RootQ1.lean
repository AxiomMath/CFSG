module

public import CFSG.LocalAnalysis.EvenBN.U4.RootP1

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (card_sup_mul_card_inf_eq)
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem F1_inf_T (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ T = miyamotoA1G h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.A1_le_F1
    ((le_sup_right : miyamotoA1G h L η ≤ miyamotoB1 h L η t).trans hS.B1_le_T))
  obtain ⟨hxF, hxT⟩ := mem_inf.1 hx
  rw [← hS.F1_inf_B1, ← hS.D1_inf_C]
  exact mem_inf.2 ⟨hxF, mem_inf.2 ⟨hS.F1_le_D1 hxF, hS.T_le hxT⟩⟩

theorem T_le_normalizer_F1 (hS : Setting h L η t Q T) :
    T ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1

theorem Q1_mod_F1 (hS : Setting h L η t Q T) :
    (∀ x ∈ miyamotoF1G h L η t ⊔ Q, x * x ∈ miyamotoF1G h L η t) ∧
      ∀ x ∈ miyamotoF1G h L η t ⊔ Q, ∀ y ∈ miyamotoF1G h L η t ⊔ Q,
        ⁅x, y⁆ ∈ miyamotoF1G h L η t := by
  obtain ⟨hPsq, hPcomm⟩ := hS.P_mod_A1
  have hQF : Q ≤ normalizer (miyamotoF1G h L η t : Set G) := hS.Q_le_T.trans hS.T_le_normalizer_F1
  have hdec : ∀ x ∈ Q, ∃ p ∈ miyamotoPG h L η, ∃ u ∈ zpowers t, x = p * u := fun x hx => by
    rw [hS.Q_eq] at hx
    exact exists_mul_of_mem_sup_of_commute hS.P_comm_zpowers hx
  have hQsq : ∀ q ∈ Q, q * q ∈ miyamotoA1G h L η := fun q hq => by
    obtain ⟨p, hp, u, hu, rfl⟩ := hdec q hq
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
    have hup : t ^ k * p = p * t ^ k := (hS.P_comm_zpowers p hp _ hu).symm
    have htk : t ^ k * t ^ k = 1 := by
      rcases hS.zpow_t_eq k with h1 | h1 <;> rw [h1]
      · exact mul_one 1
      · exact hS.t_mul_t
    have e : p * t ^ k * (p * t ^ k) = p * p := by
      calc p * t ^ k * (p * t ^ k) = p * (t ^ k * p) * t ^ k := by group
        _ = p * (p * t ^ k) * t ^ k := by rw [hup]
        _ = p * p * (t ^ k * t ^ k) := by group
        _ = p * p := by rw [htk, mul_one]
    rw [e]
    exact hPsq p hp
  have hQcomm : ∀ q ∈ Q, ∀ q' ∈ Q, ⁅q, q'⁆ ∈ miyamotoA1G h L η := fun q hq q' hq' => by
    obtain ⟨p, hp, u, hu, rfl⟩ := hdec q hq
    obtain ⟨p', hp', u', hu', rfl⟩ := hdec q' hq'
    rw [commutatorElement_mul_mul_eq_of_commute (hS.P_comm_zpowers p' hp' u hu).symm
      (hS.zpowers_comm hu hu') (hS.P_comm_zpowers p hp u' hu').symm]
    exact hPcomm p hp p' hp'
  have hconj : ∀ {q f₀ : G}, q ∈ Q → f₀ ∈ miyamotoF1G h L η t →
      q * f₀ * q⁻¹ ∈ miyamotoF1G h L η t := fun hq hf₀ =>
    (mem_normalizer_iff.1 (hQF hq) _).1 hf₀
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨f₀, hf₀, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hQF hx
    have e : f₀ * q * (f₀ * q) = f₀ * (q * f₀ * q⁻¹) * (q * q) := by group
    rw [e]
    exact mul_mem (mul_mem hf₀ (hconj hq hf₀)) (hS.A1_le_F1 (hQsq q hq))
  · obtain ⟨f₀, hf₀, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hQF hx
    obtain ⟨f₁, hf₁, q', hq', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hQF hy
    have e : ⁅f₀ * q, f₁ * q'⁆ =
        f₀ * (q * f₁ * q⁻¹) * ⁅q, q'⁆ * (q' * f₀⁻¹ * q'⁻¹) * f₁⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem hf₀ (hconj hq hf₁)) (hS.A1_le_F1 (hQcomm q hq q' hq')))
      (hconj hq' (inv_mem hf₀))) (inv_mem hf₁)

theorem card_Q1 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G) = 2 * (2 ^ f) ^ 10 := by
  have hQF : Q ≤ normalizer (miyamotoF1G h L η t : Set G) := hS.Q_le_T.trans hS.T_le_normalizer_F1
  have key := card_sup_mul_card_inf_eq hQF
  have hinf : miyamotoF1G h L η t ⊓ Q = miyamotoA1G h L η := by
    refine le_antisymm (fun x hx => ?_) (le_inf hS.A1_le_F1 (hS.A1G_le_PG.trans hS.P_le_Q))
    rw [← hS.F1_inf_T]
    exact mem_inf.2 ⟨(mem_inf.1 hx).1, hS.Q_le_T (mem_inf.1 hx).2⟩
  rw [hinf, hS.card_F1, hS.card_Q, card_miyamotoA1G] at key
  have : Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G) * (2 ^ f) ^ 4 =
      2 * (2 ^ f) ^ 10 * (2 ^ f) ^ 4 := by
    rw [key]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem eq_Q1_of_mod_F1 (hS : Setting h L η t Q T) {Y : Subgroup G}
    (hFY : miyamotoF1G h L η t ≤ Y) (hYT : Y ≤ miyamotoF1G h L η t ⊔ T)
    (hsq : ∀ x ∈ Y, x * x ∈ miyamotoF1G h L η t)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, ⁅x, y⁆ ∈ miyamotoF1G h L η t)
    (hcard : Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G) ≤ Nat.card Y) :
    Y = miyamotoF1G h L η t ⊔ Q := by
  have hTF := hS.T_le_normalizer_F1
  set Y₀ := Y ⊓ T with hY₀
  have hYeq : Y = miyamotoF1G h L η t ⊔ Y₀ := by
    refine le_antisymm (fun y hy => ?_) (sup_le hFY inf_le_left)
    obtain ⟨f₀, hf₀, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hTF (hYT hy)
    have hsY : s ∈ Y := by
      have := mul_mem (inv_mem (hFY hf₀)) hy
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_left hf₀) (mem_sup_right (mem_inf.2 ⟨hsY, hs⟩))
  have hinf : miyamotoF1G h L η t ⊓ Y₀ = miyamotoA1G h L η := by
    rw [hY₀, inf_comm Y T, ← inf_assoc, hS.F1_inf_T]
    exact inf_eq_left.2 (hS.A1_le_F1.trans hFY)
  have key := card_sup_mul_card_inf_eq (inf_le_right.trans hTF : Y₀ ≤ _)
  rw [← hYeq, hinf] at key
  rw [hS.card_Q1] at hcard
  have hY₀B : ∀ x ∈ miyamotoF1G h L η t, x ∈ T → x ∈ miyamotoB1 h L η t := fun x hxF hxT =>
    mem_sup_right (hS.F1_inf_T ▸ mem_inf.2 ⟨hxF, hxT⟩ : x ∈ miyamotoA1G h L η)
  obtain ⟨hle, heq⟩ := hS.card_le_of_mod_B1 (Y := Y₀) inf_le_right
    (fun y hy => hY₀B _ (hsq y (mem_inf.1 hy).1) (mul_mem (mem_inf.1 hy).2 (mem_inf.1 hy).2))
    fun y hy y' hy' => hY₀B _ (hcomm y (mem_inf.1 hy).1 y' (mem_inf.1 hy').1)
      (by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (mem_inf.1 hy).2 (mem_inf.1 hy').2)
          (inv_mem (mem_inf.1 hy).2)) (inv_mem (mem_inf.1 hy').2))
  have hcardY₀ : Nat.card Y₀ = 2 * (2 ^ f) ^ 6 := by
    refine le_antisymm hle ?_
    rw [hS.card_F1, card_miyamotoA1G] at key
    have : 2 * (2 ^ f) ^ 6 * (2 ^ f) ^ 8 ≤ Nat.card Y₀ * (2 ^ f) ^ 8 := by
      calc 2 * (2 ^ f) ^ 6 * (2 ^ f) ^ 8 = 2 * (2 ^ f) ^ 10 * (2 ^ f) ^ 4 := by ring
        _ ≤ Nat.card Y * (2 ^ f) ^ 4 := Nat.mul_le_mul_right _ hcard
        _ = Nat.card Y₀ * (2 ^ f) ^ 8 := by rw [key]; ring
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  rw [hYeq, heq hcardY₀]

theorem normalizer_T1_le_normalizer_Q1 (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ T : Subgroup G) : Set G) ≤
      normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) := by
  intro g hg
  have hgF := hS.mem_normalizer_F1_of_le le_sup_left le_rfl hg
  obtain ⟨hsq, hcomm⟩ := hS.Q1_mod_F1
  have hQT : miyamotoF1G h L η t ⊔ Q ≤ miyamotoF1G h L η t ⊔ T := sup_le_sup_left hS.Q_le_T _
  set Y := (miyamotoF1G h L η t ⊔ Q).map (MulAut.conj g).toMonoidHom with hYdef
  have hmem : ∀ {x : G}, x ∈ miyamotoF1G h L η t ⊔ Q → g * x * g⁻¹ ∈ Y := fun hx =>
    ⟨_, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hY : Y = miyamotoF1G h L η t ⊔ Q := by
    refine hS.eq_Q1_of_mod_F1 (fun x hx => ?_) ?_ ?_ ?_ ?_
    · have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ miyamotoF1G h L η t :=
        (mem_normalizer_iff.1 (inv_mem hgF) x).1 hx
      have := hmem (mem_sup_left hx')
      rwa [show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group] at this
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (mem_normalizer_iff.1 hg x).1 (hQT hx)
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group]
      exact (mem_normalizer_iff.1 hgF _).1 (hsq x hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group]
      exact (mem_normalizer_iff.1 hgF _).1 (hcomm x hx y hy)
    · exact le_of_eq (card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).symm
  exact mem_normalizer_fintype fun x hx => hY ▸ hmem hx

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
