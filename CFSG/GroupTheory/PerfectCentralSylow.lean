module

public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GroupTheory.PerfectCover

open CFSG.Open
open scoped commutatorElement

section Sylow

variable {E : Type} [Group E]

theorem card_sup_eq_mul_of_inf_eq_bot {Y A : Subgroup E} [Y.Normal] (h : A ⊓ Y = ⊥) :
    Nat.card ↥(Y ⊔ A) = Nat.card Y * Nat.card A := by
  have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup E) Y (Y ⊔ A) bot_le le_sup_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right, inf_comm, h, Subgroup.relIndex_bot_left] at h1
  exact h1.symm

theorem commutatorElement_central_mul_left {y a b : E} (hy : y ∈ Subgroup.center E) :
    ⁅y * a, b⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : E, g * y⁻¹ = y⁻¹ * g :=
    fun g => (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hy)) g
  simp only [commutatorElement_def, mul_inv_rev]
  calc y * a * b * (a⁻¹ * y⁻¹) * b⁻¹ = y * (a * b * a⁻¹ * y⁻¹) * b⁻¹ := by group
    _ = y * (y⁻¹ * (a * b * a⁻¹)) * b⁻¹ := by rw [hc]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_central_mul_right {y a b : E} (hy : y ∈ Subgroup.center E) :
    ⁅a, y * b⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : E, g * y⁻¹ = y⁻¹ * g :=
    fun g => (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hy)) g
  have hc' : ∀ g : E, g * y = y * g := fun g => (Subgroup.mem_center_iff.mp hy) g
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * (y * b) * a⁻¹ * (b⁻¹ * y⁻¹) = a * y * (b * a⁻¹ * b⁻¹) * y⁻¹ := by group
    _ = y * a * (b * a⁻¹ * b⁻¹) * y⁻¹ := by rw [hc']
    _ = y * (a * (b * a⁻¹ * b⁻¹) * y⁻¹) := by group
    _ = y * (y⁻¹ * (a * (b * a⁻¹ * b⁻¹))) := by rw [hc]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_bot_of_sylow_complement [Finite E] (hE : Group.IsPerfect E) {Y A : Subgroup E}
    (hY : Y ≤ Subgroup.center E) (hY2 : IsPGroup 2 Y) (hAY : A ⊓ Y = ⊥)
    (hsyl : IsPGroup 2 ↥(A ⊔ Y)) (hidx : ¬ 2 ∣ (A ⊔ Y).index) : Y = ⊥ := by
  haveI : Y.Normal := Subgroup.normal_of_le_center hY
  haveI : IsMulCommutative Y := ⟨⟨fun a b => Subtype.ext
    ((Subgroup.mem_center_iff.mp (hY a.2)) b).symm⟩⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 E := hsyl.toSylow hidx
  have hP : (P : Subgroup E) = A ⊔ Y := rfl
  obtain ⟨K, hYK, hsup⟩ := (CFSG.Quasithin.gaschutz hY2 P).mpr
    ⟨A, hP ▸ le_sup_left, by rw [inf_comm]; exact hAY, by rw [sup_comm, hP]⟩
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := E)]
    refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
    have hg : g ∈ Y ⊔ K := hsup ▸ Subgroup.mem_top g
    have hh : h ∈ Y ⊔ K := hsup ▸ Subgroup.mem_top h
    obtain ⟨y₁, hy₁, k₁, hk₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨y₂, hy₂, k₂, hk₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    rw [commutatorElement_central_mul_left (hY hy₁), commutatorElement_central_mul_right (hY hy₂),
      commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  rw [hK, inf_top_eq] at hYK
  exact hYK

theorem isPGroup_two_of_sq_eq_one {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ y ∈ H, y ^ 2 = 1) : IsPGroup 2 H := fun y =>
  ⟨1, Subtype.ext (by simpa using h y y.2)⟩

theorem eq_bot_or_lt_of_exponent_two [Finite E] (hE : Group.IsPerfect E) {Y : Subgroup E}
    (hY : Y ≤ Subgroup.center E) (hY2 : ∀ y ∈ Y, y ^ 2 = 1) {a r : ℕ}
    (hm : Nat.card E = Nat.card Y * (2 ^ a * r)) (hr : ¬ 2 ∣ r) :
    Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) → Nat.card A < 2 ^ a := by
  by_cases hY1 : Y = ⊥
  · exact Or.inl hY1
  refine Or.inr fun A hAY hAel _ => ?_
  by_contra hge
  push Not at hge
  haveI : Y.Normal := Subgroup.normal_of_le_center hY
  have hA2 : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun x hx => by
    simpa using hAel.2 x hx
  have hY2' : IsPGroup 2 Y := isPGroup_two_of_sq_eq_one hY2
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hA2
  have hcard := card_sup_eq_mul_of_inf_eq_bot (Y := Y) hAY
  have hdvd : Nat.card ↥(Y ⊔ A) ∣ Nat.card E := Subgroup.card_subgroup_dvd_card _
  rw [hcard, hm] at hdvd
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hAdvd : Nat.card A ∣ 2 ^ a * r := Nat.dvd_of_mul_dvd_mul_left hYpos hdvd
  have hcop : Nat.Coprime (2 ^ b) r :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr)
  rw [hb] at hAdvd hge
  have hba : b ≤ a :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hAdvd)
  have hab : a ≤ b := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
  have hbeq : b = a := le_antisymm hba hab
  rw [hbeq] at hb
  have hsup : IsPGroup 2 ↥(A ⊔ Y) := hA2.to_sup_of_normal_right hY2'
  have hidx : (A ⊔ Y).index = r := by
    have h1 : Nat.card ↥(A ⊔ Y) * (A ⊔ Y).index = Nat.card E := Subgroup.card_mul_index _
    have hcard' : Nat.card ↥(A ⊔ Y) = Nat.card Y * Nat.card A := by
      rw [sup_comm]
      exact hcard
    rw [hcard', hb, hm] at h1
    have h2 : Nat.card Y * 2 ^ a * (A ⊔ Y).index = Nat.card Y * 2 ^ a * r := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  exact hY1 (eq_bot_of_sylow_complement hE hY hY2' hAY hsup (hidx ▸ hr))

end Sylow

section Power

theorem pow_eq_one_of_mem_of_card_dvd {G : Type*} [Group G] [Finite G] {H : Subgroup G} {n : ℕ}
    (h : Nat.card H ∣ n) {y : G} (hy : y ∈ H) : y ^ n = 1 := by
  obtain ⟨c, hc⟩ := h
  have h1 : (⟨y, hy⟩ : H) ^ n = 1 := by
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  simpa using congrArg Subtype.val h1

end Power

