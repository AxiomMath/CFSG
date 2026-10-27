module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Extra
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.ExtraInv

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Dich

variable {G : Type} [Group G]

@[expose] def ActsTriv (Q : Subgroup G) (b : G) : Prop := ∀ x ∈ Q, ⁅x⁻¹, b⁆ ∈ zOf Q

@[expose] def ActsInv (Q : Subgroup G) (b : G) : Prop := ∀ x ∈ Q, x * (b * x * b⁻¹) ∈ zOf Q

theorem exists_fixed_inv_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hz : z * z = 1)
    {Q : Subgroup G} (hzQ : z ∈ normalizer (Q : Set G)) (hexp : ∀ x ∈ Q, x ^ p = 1) {q : G}
    (hq : q ∈ Q) : ∃ y ∈ Q, ∃ s ∈ ⁅Q, zpowers z⁆, z * y * z⁻¹ = y ∧ z * s * z⁻¹ = s⁻¹ ∧ q = y * s := by
  obtain ⟨a, ha⟩ : ∃ a : G, a = q⁻¹ * (z * q * z⁻¹) := ⟨_, rfl⟩
  have hzqQ : z * q * z⁻¹ ∈ Q := (mem_normalizer_iff.mp hzQ q).mp hq
  have haQ : a ∈ Q := by rw [ha]; exact Q.mul_mem (Q.inv_mem hq) hzqQ
  have hainv : z * a * z⁻¹ = a⁻¹ := by rw [ha]; exact conj_inv_elt hz q
  have haR : a ∈ ⁅Q, zpowers z⁆ := by
    have h1 : ⁅q⁻¹, z⁆ = a := by rw [ha]; simp [commutatorElement_def, mul_assoc]
    rw [← h1]
    exact Subgroup.commutator_mem_commutator (Q.inv_mem hq) (Subgroup.mem_zpowers z)
  obtain ⟨s₀, hs₀, hs₀sq⟩ := exists_sqrt hp hp2 (hexp a haQ)
  have hs₀R : s₀ ∈ ⁅Q, zpowers z⁆ := (Subgroup.zpowers_le.mpr haR) hs₀
  have h1 : z * s₀ * z⁻¹ = s₀⁻¹ := inverts_zpowers hainv s₀ hs₀
  refine ⟨q * s₀, Q.mul_mem hq ((Subgroup.zpowers_le.mpr haQ) hs₀), s₀⁻¹, Subgroup.inv_mem _ hs₀R,
    ?_, ?_, by group⟩
  · have h2 : z * q * z⁻¹ = q * a := by rw [ha]; group
    calc z * (q * s₀) * z⁻¹ = (z * q * z⁻¹) * (z * s₀ * z⁻¹) := by group
      _ = (q * a) * s₀⁻¹ := by rw [h2, h1]
      _ = q * s₀ := by rw [← hs₀sq]; group
  · calc z * s₀⁻¹ * z⁻¹ = (z * s₀ * z⁻¹)⁻¹ := by group
      _ = s₀⁻¹⁻¹ := by rw [h1]

end Dich

section Cent

variable {G : Type} [Group G]

theorem centralizer_eq_sup_zpowers [Finite G] {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (hE : ExtraG p Q)
    (hcard : Nat.card ↥Q = p ^ 3) {y : G} (hyQ : y ∈ Q) (hy : y ∉ zOf Q) :
    Q ⊓ centralizer ({y} : Set G) = zOf Q ⊔ zpowers y := by
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hAQ : zOf Q ⊔ zpowers y ≤ Q := sup_le hZQ (Subgroup.zpowers_le.mpr hyQ)
  have hKQ : Q ⊓ centralizer ({y} : Set G) ≤ Q := inf_le_left
  have hAK : zOf Q ⊔ zpowers y ≤ Q ⊓ centralizer ({y} : Set G) := by
    refine sup_le (fun c hc => ⟨hc.1, ?_⟩) (Subgroup.zpowers_le.mpr ⟨hyQ, ?_⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc.2 y hyQ).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKne : Q ⊓ centralizer ({y} : Set G) ≠ Q := by
    intro h
    apply hy
    refine ⟨hyQ, ?_⟩
    show y ∈ centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ Q ⊓ centralizer ({y} : Set G) := by rw [h]; exact hq
    exact Subgroup.mem_centralizer_singleton_iff.mp hq'.2
  obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow hp).mp
    (hcard ▸ Subgroup.card_dvd_of_le hKQ : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) ∣ p ^ 3)
  have hi3 : i ≠ 3 := by
    rintro rfl
    exact hKne (Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcard, hKi]))
  obtain ⟨j, hj, hAj⟩ := (Nat.dvd_prime_pow hp).mp
    (hcard ▸ Subgroup.card_dvd_of_le hAQ : Nat.card ↥(zOf Q ⊔ zpowers y) ∣ p ^ 3)
  have hZA : zOf Q ≤ zOf Q ⊔ zpowers y := le_sup_left
  have hZdvd : p ∣ Nat.card ↥(zOf Q ⊔ zpowers y) := hE.card_Z ▸ Subgroup.card_dvd_of_le hZA
  have hAneZ : zOf Q ⊔ zpowers y ≠ zOf Q := by
    intro h
    apply hy
    rw [← h]
    exact (le_sup_right : zpowers y ≤ zOf Q ⊔ zpowers y) (Subgroup.mem_zpowers y)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hAj
      rw [hAj] at hZdvd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hZdvd)
    have hj1 : j = 1 := by omega
    subst hj1
    exact hAneZ (Subgroup.eq_of_le_of_card_ge hZA (by rw [hE.card_Z, hAj, pow_one])).symm
  have hle : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) ≤ Nat.card ↥(zOf Q ⊔ zpowers y) := by
    rw [hKi, hAj]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  exact (Subgroup.eq_of_le_of_card_ge hAK hle).symm

end Cent

section Main

variable {G : Type} [Group G]

theorem dichotomy [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G} (hE : ExtraG p Q)
    (hcard : Nat.card ↥Q = p ^ 3) (hexp : ∀ x ∈ Q, x ^ p = 1) {b : G} (hb : b * b = 1)
    (hbQ : b ∈ normalizer (Q : Set G)) (hZ : zOf Q ≤ Cen b) : ActsTriv Q b ∨ ActsInv Q b := by
  by_contra hno
  obtain ⟨hnT, hnI⟩ := not_or.mp hno
  have hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := by
    rw [hE.comm_eq]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  unfold ActsTriv at hnT
  unfold ActsInv at hnI
  push Not at hnT hnI
  obtain ⟨x₁, hx₁, hx₁Z⟩ := hnT
  obtain ⟨x₂, hx₂, hx₂Z⟩ := hnI
  obtain ⟨y₁, hy₁, w₁, hw₁, hy₁b, hw₁b, rfl⟩ := exists_fixed_inv_mul hp hp2 hb hbQ hexp hx₁
  obtain ⟨y₂, hy₂, w₂, hw₂, hy₂b, hw₂b, rfl⟩ := exists_fixed_inv_mul hp hp2 hb hbQ hexp hx₂
  have hRQ : ⁅Q, zpowers b⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hbQ)
  have hw₁Q : w₁ ∈ Q := hRQ hw₁
  have hw₁Z : w₁ ∉ zOf Q := by
    intro hZw
    apply hx₁Z
    have h1 : ⁅(y₁ * w₁)⁻¹, b⁆ = (y₁ * w₁)⁻¹ * ((b * y₁ * b⁻¹) * (b * w₁ * b⁻¹)) := by
      rw [commutatorElement_def]; group
    rw [h1, hy₁b, hw₁b]
    have e : (y₁ * w₁)⁻¹ * (y₁ * w₁⁻¹) = w₁⁻¹ * w₁⁻¹ := by group
    rw [e]
    exact (zOf Q).mul_mem ((zOf Q).inv_mem hZw) ((zOf Q).inv_mem hZw)
  have hc₂ : w₂ * y₂ = y₂ * w₂ := Subgroup.mem_centralizer_singleton_iff.mp
    (commutator_le_centralizer_of_fixed hp hp2 hb hbQ hexp hcl hZ hy₂ hy₂b hw₂)
  have hy₂Z : y₂ ∉ zOf Q := by
    intro hZy
    apply hx₂Z
    have h1 : b * (y₂ * w₂) * b⁻¹ = (b * y₂ * b⁻¹) * (b * w₂ * b⁻¹) := by group
    rw [h1, hy₂b, hw₂b]
    have e : y₂ * w₂ * (y₂ * w₂⁻¹) = y₂ * y₂ := by
      calc y₂ * w₂ * (y₂ * w₂⁻¹) = y₂ * (w₂ * y₂) * w₂⁻¹ := by group
        _ = y₂ * (y₂ * w₂) * w₂⁻¹ := by rw [hc₂]
        _ = y₂ * y₂ := by group
    rw [e]
    exact (zOf Q).mul_mem hZy hZy
  have hw₁c : w₁ ∈ centralizer ({y₂} : Set G) :=
    commutator_le_centralizer_of_fixed hp hp2 hb hbQ hexp hcl hZ hy₂ hy₂b hw₁
  have hw₁K : w₁ ∈ Q ⊓ centralizer ({y₂} : Set G) := ⟨hw₁Q, hw₁c⟩
  rw [centralizer_eq_sup_zpowers hp hE hcard hy₂ hy₂Z] at hw₁K
  have hy₂Cen : y₂ ∈ Cen b := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y₂ * b = (b * y₂ * b⁻¹) * b := by rw [hy₂b]
      _ = b * y₂ := by group
  have hle : zOf Q ⊔ zpowers y₂ ≤ Cen b := sup_le hZ (Subgroup.zpowers_le.mpr hy₂Cen)
  have hcw : w₁ * b = b * w₁ := Subgroup.mem_centralizer_singleton_iff.mp (hle hw₁K)
  have hw₁1 : w₁ ≠ 1 := fun h => hw₁Z (h ▸ (zOf Q).one_mem)
  apply ne_inv_of_prime hp hp2 hw₁1 (hexp w₁ hw₁Q)
  calc w₁ = w₁ * b * b⁻¹ := by group
    _ = b * w₁ * b⁻¹ := by rw [hcw]
    _ = w₁⁻¹ := hw₁b

theorem actsTriv_mul {Q : Subgroup G} {b₁ b₂ : G} (h₂ : b₂ ∈ normalizer (Q : Set G))
    (hI₁ : ActsInv Q b₁) (hI₂ : ActsInv Q b₂) : ActsTriv Q (b₁ * b₂) := by
  intro x hx
  have hx' : b₂ * x * b₂⁻¹ ∈ Q := (mem_normalizer_iff.mp h₂ x).mp hx
  obtain ⟨x', hx'def⟩ : ∃ x', x' = b₂ * x * b₂⁻¹ := ⟨_, rfl⟩
  rw [← hx'def] at hx'
  have ht₂ : x * x' ∈ zOf Q := by rw [hx'def]; exact hI₂ x hx
  have ht₁ : x' * (b₁ * x' * b₁⁻¹) ∈ zOf Q := hI₁ x' hx'
  have hcomm : x * x' = x' * x := by
    have h1 := Subgroup.mem_centralizer_iff.mp ht₂.2 x hx
    exact mul_left_cancel (by rw [h1, mul_assoc] : x * (x * x') = x * (x' * x))
  have hC : Commute x⁻¹ x' := Commute.inv_left hcomm
  have h1 : ⁅x⁻¹, b₁ * b₂⁆ = x⁻¹ * (b₁ * x' * b₁⁻¹) := by
    rw [commutatorElement_def, hx'def]; group
  have h2 : x'⁻¹ * x⁻¹ * x' = x⁻¹ := by
    calc x'⁻¹ * x⁻¹ * x' = x'⁻¹ * (x⁻¹ * x') := by group
      _ = x'⁻¹ * (x' * x⁻¹) := by rw [hC.eq]
      _ = x⁻¹ := by group
  have e : ⁅x⁻¹, b₁ * b₂⁆ = (x * x')⁻¹ * (x' * (b₁ * x' * b₁⁻¹)) := by
    calc ⁅x⁻¹, b₁ * b₂⁆ = x⁻¹ * (b₁ * x' * b₁⁻¹) := h1
      _ = (x'⁻¹ * x⁻¹ * x') * (b₁ * x' * b₁⁻¹) := by rw [h2]
      _ = (x * x')⁻¹ * (x' * (b₁ * x' * b₁⁻¹)) := by group
  rw [e]
  exact (zOf Q).mul_mem ((zOf Q).inv_mem ht₂) ht₁

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
