module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPIdx
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Cocycle
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Main

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.ABGLocalTools CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped commutatorElement

theorem comm_t_mem {G : Type*} [Group G] {P Q R : Subgroup G} {t : G} (ht : t * t = 1)
    (htP : t ∈ normalizer (P : Set G)) (hsq : ∀ x ∈ P, x * x ∈ Q)
    (hfix : ∀ x ∈ P, x * t * x⁻¹ * t⁻¹ ∈ Q → x ∈ R) :
    ∀ p ∈ P, p * t * p⁻¹ * t⁻¹ ∈ R := by
  intro p hp
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : p * t * p⁻¹ * t⁻¹ ∈ P := by
    have := (mem_normalizer_iff.mp htP _).mp (inv_mem hp)
    rw [show p * t * p⁻¹ * t⁻¹ = p * (t * p⁻¹ * t⁻¹) by group]
    exact mul_mem hp this
  refine hfix _ hc ?_
  have e1 : p * t * p⁻¹ * t⁻¹ * t * (p * t * p⁻¹ * t⁻¹)⁻¹ * t⁻¹ =
      p * t * p⁻¹ * t * p * t⁻¹ * p⁻¹ * t⁻¹ := by group
  have e2 : p * t * p⁻¹ * t⁻¹ * (p * t * p⁻¹ * t⁻¹) =
      p * t * p⁻¹ * t⁻¹ * p * t * p⁻¹ * t⁻¹ := by group
  have := hsq _ hc
  rw [e2, ht'] at this
  rw [e1, ht']
  exact this

theorem mul_identity_of_sq {M : Type*} [CommGroup M] (h2 : ∀ u : M, u * u = 1) (X A B : M) :
    X⁻¹ * A * X⁻¹ * B * X⁻¹ = A⁻¹ * B * A⁻¹ * X * A⁻¹ := by
  have hi : ∀ u : M, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (h2 u)
  simp only [hi]
  calc X * A * X * B * X = (X * X) * X * (A * B) := by ac_rfl
    _ = (A * A) * A * (B * X) := by rw [h2, h2, one_mul, one_mul]; ac_rfl
    _ = A * B * A * X * A := by ac_rfl

theorem fix_identity {G : Type*} [Group G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hPQ : P ≤ normalizer (Q : Set G)) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hsq : ∀ x ∈ P, x * x ∈ Q) {j : G} (hjP : j ∈ normalizer (P : Set G)) (hj3 : j ^ 3 = 1)
    (hfix : ∀ x ∈ P, j * x * j⁻¹ * x⁻¹ ∈ Q → x ∈ Q) :
    ∀ x ∈ P, x⁻¹ * ⁅j, x⁆ * ⁅j ^ 2, x⁆ ∈ Q := by
  have hN : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPQ
  let mk : P →* ↥P ⧸ Q.subgroupOf P := QuotientGroup.mk' _
  have hmk : ∀ u v : P, mk u = mk v ↔ (u : G)⁻¹ * v ∈ Q := fun u v => by
    change (QuotientGroup.mk u : ↥P ⧸ Q.subgroupOf P) = QuotientGroup.mk v ↔ _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hcomm : ∀ a b : ↥P ⧸ Q.subgroupOf P, a * b = b * a := by
    intro a b
    obtain ⟨u, rfl⟩ := hsurj a
    obtain ⟨v, rfl⟩ := hsurj b
    rw [← map_mul, ← map_mul, hmk]
    have := hab _ v.2 _ u.2
    have hvu : (v : G) * u ∈ P := mul_mem v.2 u.2
    have h' := (mem_normalizer_iff.mp (hPQ (inv_mem hvu)) _).mp this
    have e : ((u * v : P) : G)⁻¹ * ((v * u : P) : G) =
        ((v : G) * u)⁻¹ * ((v : G) * u * (v : G)⁻¹ * (u : G)⁻¹) * ((v : G) * u)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul]; group
    rw [e]
    exact h'
  let _ : CommGroup (↥P ⧸ Q.subgroupOf P) := { (inferInstance : Group _) with mul_comm := hcomm }
  have h2 : ∀ a : ↥P ⧸ Q.subgroupOf P, a * a = 1 := by
    intro a
    obtain ⟨u, rfl⟩ := hsurj a
    rw [← map_mul, ← map_one mk, hmk]
    simpa using Q.inv_mem (hsq _ u.2)
  intro x hx
  have hj2 : j ^ 2 ∈ normalizer (P : Set G) := pow_mem hjP 2
  have ha : j * x * j⁻¹ ∈ P := (mem_normalizer_iff.mp hjP _).mp hx
  have hb : j ^ 2 * x * (j ^ 2)⁻¹ ∈ P := (mem_normalizer_iff.mp hj2 _).mp hx
  set xs : P := ⟨x, hx⟩
  set as : P := ⟨_, ha⟩
  set bs : P := ⟨_, hb⟩
  set ys : P := xs⁻¹ * as * xs⁻¹ * bs * xs⁻¹
  set zs : P := as⁻¹ * bs * as⁻¹ * xs * as⁻¹
  have hy : (ys : G) = x⁻¹ * ⁅j, x⁆ * ⁅j ^ 2, x⁆ := by
    simp only [ys, xs, as, bs, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  have hz : (zs : G) = j * (ys : G) * j⁻¹ := by
    have hj3' : j ^ 3 = 1 := hj3
    simp only [zs, ys, xs, as, bs, Subgroup.coe_mul, Subgroup.coe_inv]
    have e : ∀ g : G, j ^ 3 * g * (j ^ 3)⁻¹ = g := fun g => by rw [hj3']; group
    calc (j * x * j⁻¹)⁻¹ * (j ^ 2 * x * (j ^ 2)⁻¹) * (j * x * j⁻¹)⁻¹ * x * (j * x * j⁻¹)⁻¹
        = (j * x * j⁻¹)⁻¹ * (j ^ 2 * x * (j ^ 2)⁻¹) * (j * x * j⁻¹)⁻¹ *
            (j ^ 3 * x * (j ^ 3)⁻¹) * (j * x * j⁻¹)⁻¹ := by rw [e]
      _ = j * (x⁻¹ * (j * x * j⁻¹) * x⁻¹ * (j ^ 2 * x * (j ^ 2)⁻¹) * x⁻¹) * j⁻¹ := by group
  have hyz : mk ys = mk zs := by
    simp only [ys, zs, map_mul, map_inv]
    exact mul_identity_of_sq h2 _ _ _
  rw [hmk, hz] at hyz
  rw [← hy]
  refine hfix _ ys.2 ?_
  have := (mem_normalizer_iff.mp (hPQ ys.2) _).mp hyz
  convert this using 1
  group

theorem card_SL3 : Nat.card SL3 = 2 ^ 6 * 945 := by
  rw [Matrix.card_SL_field]
  have : Fintype.card CFSG.Fischer.F4 = 4 := rfl
  simp only [this, Fin.prod_univ_three]
  norm_num

theorem pow_three_of_mem_center {g : SL3} (hg : g ∈ center SL3) : g ^ 3 = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hrg, ← map_pow, hr,
    map_one]

theorem not_two_dvd_card_of_le_center {K : Subgroup SL3} (hK : K ≤ center SL3) :
    ¬ 2 ∣ Nat.card K := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  have h3 : (g : SL3) ^ 3 = 1 := pow_three_of_mem_center (hK g.2)
  have h3' : g ^ 3 = 1 := Subtype.ext (by simpa using h3)
  have := orderOf_dvd_of_pow_eq_one h3'
  rw [hg] at this
  omega

theorem card_sup_mul_card_inf {Γ : Type*} [Group Γ] [Finite Γ] (X Y : Subgroup Γ) [Y.Normal] :
    Nat.card (X ⊔ Y : Subgroup Γ) * Nat.card (X ⊓ Y : Subgroup Γ) = Nat.card X * Nat.card Y := by
  have h1 := Subgroup.relIndex_mul_card Y (X ⊔ Y)
  have h2 := Subgroup.relIndex_mul_card Y X
  rw [Subgroup.relIndex_sup_right, inf_eq_left.mpr (le_sup_right : Y ≤ X ⊔ Y)] at h1
  rw [← h1, ← h2, inf_comm]
  ring

theorem two_pow_mul_of_dvd {a k m e : ℕ} (h : a * k = 2 ^ e * m) (hk : ¬ 2 ∣ k) (hm : ¬ 2 ∣ m) :
    ∃ a', a = 2 ^ e * a' ∧ ¬ 2 ∣ a' := by
  have hcop : Nat.Coprime (2 ^ e) k :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hk)
  obtain ⟨a', ha'⟩ := hcop.dvd_of_dvd_mul_right (h ▸ Dvd.intro m rfl : 2 ^ e ∣ a * k)
  refine ⟨a', ha', fun h2 => hm ?_⟩
  have : 2 ^ e * (a' * k) = 2 ^ e * m := by rw [← h, ha']; ring
  have hak : a' * k = m := Nat.eq_of_mul_eq_mul_left (by positivity) this
  rw [← hak]
  exact Dvd.dvd.mul_right h2 k

section Card

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}

theorem Y14Hyp.card_nTwo [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    ∃ m, Nat.card (nTwo D₂ K₂ D₁) = 2 ^ 30 * m ∧ ¬ 2 ∣ m := by
  have : Fact (ElemSec D₂ (⊥ : Subgroup G)) := ⟨h.elemSec⟩
  have hN := h.normal_nTwo
  obtain ⟨-, X, h1, h2, h3, ψ, hψ, hk, -⟩ := h.r3bHyp.main
  set τ := tauG2 h
  have hττ := h.pi_ττ
  have hX : Nat.card X * Nat.card ψ.ker = 2 ^ 6 * 945 := by
    rw [← card_SL3, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  obtain ⟨a, ha, ha2⟩ := two_pow_mul_of_dvd hX (not_two_dvd_card_of_le_center hk) (by norm_num)
  have hτinj : Function.Injective τ := fun x y hxy => by
    rw [← hττ x, ← hττ y, hxy]
  have hXτ : Nat.card (X.map τ) = Nat.card X := Subgroup.card_map_of_injective hτinj
  have hc := comm_of_commutator_eq_bot h2
  have hYn : (X.map τ).Normal := by
    constructor
    intro y hy g
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hc (h1 ▸ Subgroup.mem_top g)
    have e : a' * b' * y * (a' * b')⁻¹ = b' * y * b'⁻¹ := by
      have h1' := hc a' ha' (b' * y * b'⁻¹) (mul_mem (mul_mem hb' hy) (inv_mem hb'))
      calc a' * b' * y * (a' * b')⁻¹ = a' * (b' * y * b'⁻¹) * a'⁻¹ := by group
        _ = (b' * y * b'⁻¹) * a' * a'⁻¹ := by rw [h1']
        _ = b' * y * b'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hb' hy) (inv_mem hb')
  have hΓ := card_sup_mul_card_inf X (X.map τ)
  rw [h1, Subgroup.card_top, hXτ, ha] at hΓ
  have hodd : ¬ 2 ∣ Nat.card (X ⊓ X.map τ : Subgroup _) := fun h2' =>
    absurd (h2'.trans h3) (by norm_num)
  obtain ⟨m, hm, hm2⟩ := two_pow_mul_of_dvd (e := 12) (m := a * a)
    (by rw [hΓ]; ring) hodd (fun h' => ha2 ((Nat.Prime.dvd_mul Nat.prime_two).mp h' |>.elim id id))
  refine ⟨m, ?_, hm2⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (D₂.subgroupOf (nTwo D₂ K₂ D₁)),
    card_subgroupOf_of_le D₂_le_nTwo, h.card_D₂, hm]
  ring

theorem Y14Hyp.isSylowOf [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) {P : Subgroup G}
    (hPN : P ≤ nTwo D₂ K₂ D₁) (hP : Nat.card P = 2 ^ 30) : IsSylowOf 2 P (nTwo D₂ K₂ D₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hm2⟩ := h.card_nTwo
  exact isSylowOf_of_card hPN (by rw [hP, hm, factorization_two_mul hm2])

end Card

theorem nTwo_eq_sup_P {G : Type*} [Group G] {D₂ K₂ D₁ P X₁ X₂ : Subgroup G} {w₁ w₂ : G}
    (hK : K₂ = X₁ ⊔ X₂ ⊔ zpowers w₁ ⊔ zpowers w₂) (hX₁ : X₁ ≤ P) (hX₂ : X₂ ≤ P)
    (hPN : P ≤ nTwo D₂ K₂ D₁) (hD₁ : D₁ ≤ P) (hD₂ : D₂ ≤ P) :
    nTwo D₂ K₂ D₁ = P ⊔ zpowers w₁ ⊔ zpowers w₂ := by
  have hK₂ : K₂ ≤ nTwo D₂ K₂ D₁ := le_sup_right.trans le_sup_left
  have hw₁ : w₁ ∈ K₂ := hK ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers w₁))
  have hw₂ : w₂ ∈ K₂ := hK ▸ Subgroup.mem_sup_right (mem_zpowers w₂)
  refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) (sup_le (sup_le hPN ?_) ?_)
  · exact hD₂.trans (le_sup_left.trans le_sup_left)
  · rw [hK]
    exact sup_le_sup_right (sup_le_sup_right (sup_le hX₁ hX₂) _) _
  · exact hD₁.trans (le_sup_left.trans le_sup_left)
  · exact (zpowers_le.mpr hw₁).trans hK₂
  · exact (zpowers_le.mpr hw₂).trans hK₂

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
