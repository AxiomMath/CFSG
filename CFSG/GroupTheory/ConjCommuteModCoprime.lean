module

public import CFSG.Walter.W67.Section6.Util
public import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [Finite G]

private theorem comm_of_isMulCommutative {H : Subgroup G} (h : IsMulCommutative ↥H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x :=
  fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥H)).comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem commutator_mem_of_mem_union {U H₁ H₂ : Subgroup G}
    (ha₁ : ∀ x ∈ H₁, ∀ y ∈ H₁, x * y = y * x) (ha₂ : ∀ x ∈ H₂, ∀ y ∈ H₂, x * y = y * x)
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y * x⁻¹ * y⁻¹ ∈ U) {x y : G}
    (hxN : x ∈ normalizer (U : Set G)) (hyN : y ∈ normalizer (U : Set G))
    (hx : x ∈ ((U : Set G) ∪ H₁) ∪ H₂) (hy : y ∈ ((U : Set G) ∪ H₁) ∪ H₂) : ⁅x, y⁆ ∈ U := by
  rw [commutatorElement_def]
  by_cases hxU : x ∈ U
  · rw [mul_assoc, mul_assoc]
    exact U.mul_mem hxU
      (by simpa only [mul_assoc] using (mem_normalizer_iff.mp hyN x⁻¹).mp (U.inv_mem hxU))
  by_cases hyU : y ∈ U
  · exact U.mul_mem ((mem_normalizer_iff.mp hxN y).mp hyU) (U.inv_mem hyU)
  have hx' : x ∈ H₁ ∨ x ∈ H₂ := by
    rcases hx with (hx | hx) | hx
    exacts [absurd hx hxU, Or.inl hx, Or.inr hx]
  have hy' : y ∈ H₁ ∨ y ∈ H₂ := by
    rcases hy with (hy | hy) | hy
    exacts [absurd hy hyU, Or.inl hy, Or.inr hy]
  rcases hx' with hx | hx <;> rcases hy' with hy | hy
  · rw [ha₁ x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem
  · exact hcomm x hx y hy
  · simpa [mul_assoc] using U.inv_mem (hcomm y hy x hx)
  · rw [ha₂ x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem

theorem commutator_mem_join_of_commutator_mem {U H₁ H₂ : Subgroup G}
    (h₁ : H₁ ≤ Subgroup.normalizer (U : Set G))
    (h₂ : H₂ ≤ Subgroup.normalizer (U : Set G))
    (ha₁ : IsMulCommutative ↥H₁)
    (ha₂ : IsMulCommutative ↥H₂)
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y * x⁻¹ * y⁻¹ ∈ U) :
    ∀ y ∈ U ⊔ H₁ ⊔ H₂, ∀ y' ∈ U ⊔ H₁ ⊔ H₂, ⁅y, y'⁆ ∈ U := by
  have hY : U ⊔ H₁ ⊔ H₂ = closure (((U : Set G) ∪ H₁) ∪ H₂) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, closure_eq, closure_eq, closure_eq]
  have hN : closure (((U : Set G) ∪ H₁) ∪ H₂) ≤ normalizer (U : Set G) :=
    hY ▸ sup_le (sup_le le_normalizer h₁) h₂
  have conj_mem : ∀ g ∈ normalizer (U : Set G), ∀ u ∈ U, g * u * g⁻¹ ∈ U :=
    fun g hg u hu => (mem_normalizer_iff.mp hg u).mp hu
  intro y hy y' hy'
  rw [hY] at hy hy'
  induction hy, hy' using closure_induction₂ with
  | mem x z hx hz =>
    exact commutator_mem_of_mem_union (comm_of_isMulCommutative ha₁)
      (comm_of_isMulCommutative ha₂) hcomm (hN (subset_closure hx))
      (hN (subset_closure hz)) hx hz
  | one_left x _ => simp
  | one_right x _ => simp
  | mul_left x y z hx _ _ hxz hyz =>
    rw [show ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ by simp only [commutatorElement_def]; group]
    exact U.mul_mem (conj_mem x (hN hx) _ hyz) hxz
  | mul_right y z x hy _ _ hxy hxz =>
    rw [show ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) by simp only [commutatorElement_def]; group]
    exact U.mul_mem hxy (conj_mem y (hN hy) _ hxz)
  | inv_left x y hx _ hxy =>
    rw [show ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ by simp only [commutatorElement_def]; group]
    exact conj_mem _ (inv_mem (hN hx)) _ (inv_mem hxy)
  | inv_right x y _ hy hxy =>
    rw [show ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ by simp only [commutatorElement_def]; group]
    exact conj_mem _ (inv_mem (hN hy)) _ (inv_mem hxy)

private theorem relIndex_dvd_of_card_dvd_mul {U Z : Subgroup G} (hUZ : U ≤ Z) {n : ℕ}
    (h : Nat.card Z ∣ Nat.card U * n) : U.relIndex Z ∣ n := by
  have hrelmul : U.relIndex Z * Nat.card U = Nat.card Z := by
    have := Subgroup.relIndex_mul_card U Z
    rwa [inf_eq_left.mpr hUZ] at this
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos (α := ↥U))
  rw [mul_comm (Nat.card U) (U.relIndex Z), hrelmul]
  exact h

theorem relIndex_join_dvd_card_mul {U H₁ H₂ : Subgroup G}
    (h₁ : H₁ ≤ Subgroup.normalizer (U : Set G))
    (h₂ : H₂ ≤ Subgroup.normalizer (U : Set G))
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y * x⁻¹ * y⁻¹ ∈ U) :
    U.relIndex (U ⊔ H₁ ⊔ H₂) ∣ Nat.card H₁ * Nat.card H₂ := by
  let Z : Subgroup G := U ⊔ H₁
  have hUZ : U ≤ Z := le_sup_left
  have hH2Z : H₂ ≤ Subgroup.normalizer (Z : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hsub : Z.map (MulAut.conj b).toMonoidHom ≤ Z := by
      rw [show Z = U ⊔ H₁ from rfl, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂ hb)).le.trans le_sup_left
      · intro z hz
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
        change b * a * b⁻¹ ∈ Z
        have hu : a⁻¹ * (b * a * b⁻¹) ∈ U := by
          simpa [mul_assoc] using hcomm a⁻¹ (H₁.inv_mem ha) b hb
        have hu' : a⁻¹ * b * a * b⁻¹ ∈ U := by simpa [mul_assoc] using hu
        have heq : b * a * b⁻¹ = a * (a⁻¹ * b * a * b⁻¹) := by group
        rw [heq]
        exact Z.mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hu')
    have hcard : Nat.card (Z.map (MulAut.conj b).toMonoidHom) = Nat.card Z :=
      Subgroup.card_map_of_injective (K := Z) (f := (MulAut.conj b).toMonoidHom)
        (by simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj b).injective)
    exact Subgroup.eq_of_le_of_card_ge hsub (le_of_eq hcard.symm)
  have hZdiv : Nat.card Z ∣ Nat.card U * Nat.card H₁ := by
    simpa [Z] using
      CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
        U H₁ h₁
  have hYdiv : Nat.card ↥(Z ⊔ H₂) ∣ Nat.card Z * Nat.card H₂ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
      Z H₂ hH2Z
  have hY : Nat.card ↥(Z ⊔ H₂) ∣ Nat.card U * (Nat.card H₁ * Nat.card H₂) := by
    have hY2 : Nat.card Z * Nat.card H₂ ∣ Nat.card U * (Nat.card H₁ * Nat.card H₂) := by
      rw [← mul_assoc]
      exact Nat.mul_dvd_mul hZdiv dvd_rfl
    exact hYdiv.trans hY2
  exact relIndex_dvd_of_card_dvd_mul (le_sup_left.trans le_sup_left) hY

theorem exists_isMulCommutative_complement {U H₁ H₂ : Subgroup G}
    (h₁ : H₁ ≤ Subgroup.normalizer (U : Set G))
    (h₂ : H₂ ≤ Subgroup.normalizer (U : Set G))
    (ha₁ : IsMulCommutative ↥H₁)
    (ha₂ : IsMulCommutative ↥H₂)
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y * x⁻¹ * y⁻¹ ∈ U)
    (hc : Nat.Coprime (Nat.card U) (U.relIndex (U ⊔ H₁ ⊔ H₂))) :
    ∃ W : Subgroup G, W ≤ U ⊔ H₁ ⊔ H₂ ∧ U ⊓ W = ⊥ ∧ U ⊔ W = U ⊔ H₁ ⊔ H₂ ∧
      IsMulCommutative ↥W := by
  classical
  let Y : Subgroup G := U ⊔ H₁ ⊔ H₂
  have hUY : U ≤ Y := le_sup_left.trans le_sup_left
  have hYnorm : Y ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer h₁) h₂
  obtain ⟨W, hWY, hUW, hUWs, -⟩ :=
    CFSG.Walter.W67.Sec6.exists_complement_in hUY hYnorm hc
  refine ⟨W, hWY, hUW, hUWs, IsMulCommutative.of_comm ?_⟩
  intro w w'
  apply Subtype.ext
  have hmemU : ⁅(w : G), (w' : G)⁆ ∈ U :=
    commutator_mem_join_of_commutator_mem h₁ h₂ ha₁ ha₂ hcomm _
      (hWY w.2) _ (hWY w'.2)
  have hmemW : ⁅(w : G), (w' : G)⁆ ∈ W := by
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem w.2 w'.2) (W.inv_mem w.2)) (W.inv_mem w'.2)
  have hone : ⁅(w : G), (w' : G)⁆ = 1 := by
    have h : ⁅(w : G), (w' : G)⁆ ∈ U ⊓ W := Subgroup.mem_inf.mpr ⟨hmemU, hmemW⟩
    rwa [hUW, Subgroup.mem_bot] at h
  exact (commutatorElement_eq_one_iff_mul_comm).mp hone

theorem exists_conj_mem_of_le_sup {U H W : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (U : Set G))
    (hW : W ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ⊓ W = ⊥) (hHle : H ≤ U ⊔ W)
    (hc : Nat.Coprime (Nat.card U) (Nat.card H)) :
    ∃ u ∈ U, ∀ x ∈ H, u * x * u⁻¹ ∈ W := by
  classical
  let Z : Subgroup G := U ⊔ H
  have hUZ : U ≤ Z := le_sup_left
  have hHZ : H ≤ Z := le_sup_right
  have hZnorm : Z ≤ Subgroup.normalizer (U : Set G) :=
    sup_le Subgroup.le_normalizer hH
  have hUi : U ⊓ H = ⊥ := Subgroup.inf_eq_bot_of_coprime hc
  have hdvd : Nat.card Z ∣ Nat.card U * Nat.card H := by
    simpa [Z] using
      CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
        U H hH
  have hrelDvd : U.relIndex Z ∣ Nat.card H := relIndex_dvd_of_card_dvd_mul hUZ hdvd
  have hcopZ : Nat.Coprime (Nat.card U) (U.relIndex Z) := hc.coprime_dvd_right hrelDvd
  let W2 : Subgroup G := W ⊓ Z
  have hW2Z : W2 ≤ Z := inf_le_right
  have hW2i : U ⊓ W2 = ⊥ := by
    change U ⊓ (W ⊓ Z) = ⊥
    rw [← inf_assoc, hUW, bot_inf_eq]
  have hW2s : U ⊔ W2 = Z := by
    have h := Subgroup.inf_sup_assoc_of_le (H := W) (K := Z) (N := U) hW hUZ
    have hZle : Z ≤ W ⊔ U := by
      rw [sup_comm W U]
      exact sup_le le_sup_left hHle
    rw [inf_eq_left.mpr hZle, inf_comm Z W, sup_comm (W ⊓ Z) U] at h
    simpa [W2] using h
  obtain ⟨u, hu, hconj⟩ :=
    CFSG.Walter.W67.Sec6.exists_conj_complement_in hUZ hZnorm hcopZ hHZ hW2Z
      hUi rfl hW2i hW2s
  refine ⟨u, hu, fun x hx => ?_⟩
  have hmem : u * x * u⁻¹ ∈ W2 := by
    rw [hconj]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact (Subgroup.mem_inf.mp hmem).1

theorem exists_conj_commute_of_commutator_mem {U H₁ H₂ : Subgroup G}
    (h₁ : H₁ ≤ Subgroup.normalizer (U : Set G))
    (h₂ : H₂ ≤ Subgroup.normalizer (U : Set G))
    (hc₁ : Nat.Coprime (Nat.card U) (Nat.card H₁))
    (hc₂ : Nat.Coprime (Nat.card U) (Nat.card H₂))
    (ha₁ : IsMulCommutative ↥H₁)
    (ha₂ : IsMulCommutative ↥H₂)
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y * x⁻¹ * y⁻¹ ∈ U) :
    ∃ u ∈ U, ∀ x ∈ H₁, ∀ y ∈ H₂, (u * x * u⁻¹) * y = y * (u * x * u⁻¹) := by
  classical
  let Y : Subgroup G := U ⊔ H₁ ⊔ H₂
  have hUY : U ≤ Y := le_sup_left.trans le_sup_left
  have hH1Y : H₁ ≤ Y := (le_sup_right : H₁ ≤ U ⊔ H₁).trans le_sup_left
  have hH2Y : H₂ ≤ Y := le_sup_right
  have hYnorm : Y ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer h₁) h₂
  have hdiv : U.relIndex Y ∣ Nat.card H₁ * Nat.card H₂ :=
    relIndex_join_dvd_card_mul h₁ h₂ hcomm
  have hcopY : Nat.Coprime (Nat.card U) (U.relIndex Y) :=
    (hc₁.mul_right hc₂).coprime_dvd_right hdiv
  obtain ⟨W, hWY, hUW, hUWs, hWab⟩ :=
    exists_isMulCommutative_complement h₁ h₂ ha₁ ha₂ hcomm hcopY
  have hWnorm : W ≤ Subgroup.normalizer (U : Set G) := hWY.trans hYnorm
  obtain ⟨u₂, hu₂, hconj₂⟩ :=
    exists_conj_mem_of_le_sup h₂ hWnorm hUW (by rw [hUWs]; exact hH2Y) hc₂
  obtain ⟨u₁, hu₁, hconj₁⟩ :=
    exists_conj_mem_of_le_sup h₁ hWnorm hUW (by rw [hUWs]; exact hH1Y) hc₁
  let Wconj : Subgroup G := W.map (MulAut.conj u₂⁻¹).toMonoidHom
  have hWconj_ab : IsMulCommutative ↥Wconj := by
    letI := hWab
    exact Subgroup.map_isMulCommutative W (MulAut.conj u₂⁻¹).toMonoidHom
  refine ⟨u₂⁻¹ * u₁, U.mul_mem (U.inv_mem hu₂) hu₁, fun x hx y hy => ?_⟩
  have hxW : u₁ * x * u₁⁻¹ ∈ W := hconj₁ x hx
  have hyW : u₂ * y * u₂⁻¹ ∈ W := hconj₂ y hy
  have hxW' : (u₂⁻¹ * u₁) * x * (u₂⁻¹ * u₁)⁻¹ ∈ Wconj :=
    ⟨u₁ * x * u₁⁻¹, hxW, by
      change u₂⁻¹ * (u₁ * x * u₁⁻¹) * (u₂⁻¹)⁻¹ =
        (u₂⁻¹ * u₁) * x * (u₂⁻¹ * u₁)⁻¹
      group⟩
  have hyW' : y ∈ Wconj :=
    ⟨u₂ * y * u₂⁻¹, hyW, by
      change u₂⁻¹ * (u₂ * y * u₂⁻¹) * (u₂⁻¹)⁻¹ = y
      group⟩
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := ↥Wconj)).comm ⟨_, hxW'⟩ ⟨y, hyW'⟩)

end CFSG.GroupTheory

end
