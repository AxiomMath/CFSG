module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

theorem exists_commutatorRadical {U R : Subgroup G}
    (hc : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ R)
    (hRc : ∀ x ∈ U, ∀ r ∈ R, x * r = r * x) (Z : Subgroup G) :
    ∃ J : Subgroup G, ∀ x : G, x ∈ J ↔ x ∈ U ∧ ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  refine ⟨{ carrier := {x | x ∈ U ∧ ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ Z}
            mul_mem' := ?_
            one_mem' := ⟨one_mem _, fun y _ => by
              rw [one_mul, inv_one, mul_one, mul_inv_cancel]
              exact one_mem _⟩
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x x' ⟨hx, hxZ⟩ ⟨hx', hx'Z⟩
    refine ⟨mul_mem hx hx', fun y hy => ?_⟩
    have hcomm : x * (x' * y * x'⁻¹ * y⁻¹) = (x' * y * x'⁻¹ * y⁻¹) * x :=
      hRc x hx _ (hc x' hx' y hy)
    have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        (x * (x' * y * x'⁻¹ * y⁻¹)) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e, hcomm, mul_inv_cancel_right]
    exact mul_mem (hx'Z y hy) (hxZ y hy)
  · rintro x ⟨hx, hxZ⟩
    refine ⟨inv_mem hx, fun y hy => ?_⟩
    have hcomm : x * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * x := hRc x hx _ (hc y hy x hx)
    have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x := by group
    have e' : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    have hc' : x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x = y * x * y⁻¹ * x⁻¹ := by
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    rw [e, hc', ← e']
    exact inv_mem (hxZ y hy)

theorem exists_central_product_of_radical [Finite G] {U R Z J : Subgroup G} {t : G}
    (hc : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ R) (hRc : ∀ x ∈ U, ∀ r ∈ R, x * r = r * x)
    (hRU : R ≤ U) (hcent : ∀ x ∈ U, (∀ y ∈ U, x * y = y * x) → x ∈ R)
    (htt : t * t = 1) (htU : ∀ x ∈ U, t * x * t⁻¹ ∈ U)
    (hZt : ∀ z ∈ Z, t⁻¹ * z * t ∈ Z → z = 1)
    (hJU : J ≤ U) (hJZ : ∀ x ∈ J, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hcard : Nat.card U * Nat.card R ≤ Nat.card J * Nat.card J) :
    ∃ J₁ J₂ : Subgroup G, J₁ ⊔ J₂ = U ∧ J₁ ⊓ J₂ = R ∧
      (∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) ∧ (∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁) ∧
      (∀ k ∈ normalizer (U : Set G), k ∈ normalizer (Z : Set G) →
        k ∈ normalizer (J₁ : Set G)) ∧
      ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨J₁, hJ₁⟩ := exists_commutatorRadical hc hRc Z
  obtain ⟨J₂, hJ₂⟩ := exists_commutatorRadical hc hRc (Z.comap (MulAut.conj t⁻¹).toMonoidHom)
  have hJ₂' : ∀ x : G, x ∈ J₂ ↔ x ∈ U ∧ ∀ y ∈ U, t⁻¹ * (x * y * x⁻¹ * y⁻¹) * t ∈ Z := by
    intro x
    rw [hJ₂]
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have htU' : ∀ x ∈ U, t⁻¹ * x * t ∈ U := fun x hx => by
    have h1 := htU x hx
    rw [htinv] at h1 ⊢
    exact h1
  have hJ₁U : J₁ ≤ U := fun x hx => ((hJ₁ x).mp hx).1
  have hJ₂U : J₂ ≤ U := fun x hx => ((hJ₂' x).mp hx).1
  have ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂ := by
    intro x hx
    obtain ⟨hxU, hxZ⟩ := (hJ₁ x).mp hx
    refine (hJ₂' _).mpr ⟨htU x hxU, fun y hy => ?_⟩
    have e : t⁻¹ * (t * x * t⁻¹ * y * (t * x * t⁻¹)⁻¹ * y⁻¹) * t =
        x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹ := by group
    rw [e]
    exact hxZ _ (htU' y hy)
  have ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁ := by
    intro x hx
    obtain ⟨hxU, hxZ⟩ := (hJ₂' x).mp hx
    refine (hJ₁ _).mpr ⟨htU x hxU, fun y hy => ?_⟩
    have e : t * x * t⁻¹ * y * (t * x * t⁻¹)⁻¹ * y⁻¹ =
        t * (x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
    have e2 : t * (x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹) * t⁻¹ =
        t⁻¹ * (x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹) * t := by rw [htinv]
    rw [e, e2]
    exact hxZ _ (htU' y hy)
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haU, haZ⟩ := (hJ₁ a).mp ha
    obtain ⟨hbU, hbZ⟩ := (hJ₂' b).mp hb
    have h1 := haZ b hbU
    have h2 : t⁻¹ * (a * b * a⁻¹ * b⁻¹) * t ∈ Z := by
      have h4 := inv_mem (hbZ a haU)
      have e : (t⁻¹ * (b * a * b⁻¹ * a⁻¹) * t)⁻¹ = t⁻¹ * (a * b * a⁻¹ * b⁻¹) * t := by group
      rw [e] at h4
      exact h4
    have h3 := hZt _ h1 h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hRJ₁ : R ≤ J₁ := fun r hr => (hJ₁ r).mpr ⟨hRU hr, fun y hy => by
    rw [← hRc y hy r hr, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _⟩
  have hRJ₂ : R ≤ J₂ := fun r hr => (hJ₂' r).mpr ⟨hRU hr, fun y hy => by
    rw [← hRc y hy r hr, mul_inv_cancel_right, mul_inv_cancel, mul_one, inv_mul_cancel]
    exact one_mem _⟩
  have hinf : J₁ ⊓ J₂ = R := by
    refine le_antisymm (fun x hx => ?_) (le_inf hRJ₁ hRJ₂)
    obtain ⟨hxU, hxZ⟩ := (hJ₁ x).mp (mem_inf.mp hx).1
    obtain ⟨-, hxZ'⟩ := (hJ₂' x).mp (mem_inf.mp hx).2
    refine hcent x hxU fun y hy => ?_
    have h3 := hZt _ (hxZ y hy) (hxZ' y hy)
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  have hJJ₁ : J ≤ J₁ := fun x hx => (hJ₁ x).mpr ⟨hJU hx, hJZ x hx⟩
  have hJ₁J₂ : J₁.map (MulAut.conj t).toMonoidHom ≤ J₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ht₁ x hx
  have hcJ₁ : Nat.card J ≤ Nat.card J₁ := Subgroup.card_le_of_le hJJ₁
  have hcJ₂ : Nat.card J₁ ≤ Nat.card J₂ := by
    calc Nat.card J₁ = Nat.card (J₁.map (MulAut.conj t).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj t).injective).symm
      _ ≤ Nat.card J₂ := Subgroup.card_le_of_le hJ₁J₂
  have hprod := CFSG.LocalAnalysis.ComponentInitial.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf] at hprod
  have hsupU : J₁ ⊔ J₂ ≤ U := sup_le hJ₁U hJ₂U
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hge : Nat.card U ≤ Nat.card (J₁ ⊔ J₂ : Subgroup G) := by
    have h1 : Nat.card U * Nat.card R ≤ Nat.card (J₁ ⊔ J₂ : Subgroup G) * Nat.card R := by
      rw [hprod]
      calc Nat.card U * Nat.card R ≤ Nat.card J * Nat.card J := hcard
        _ ≤ Nat.card J₁ * Nat.card J₂ := Nat.mul_le_mul hcJ₁ (hcJ₁.trans hcJ₂)
    exact Nat.le_of_mul_le_mul_right h1 hRpos
  have hsup : J₁ ⊔ J₂ = U := Subgroup.eq_of_le_of_card_ge hsupU hge
  refine ⟨J₁, J₂, hsup, hinf, ht₁, ht₂, fun k hkU hkZ => ?_, hcomm⟩
  have key : ∀ c : G, c ∈ normalizer (U : Set G) → c ∈ normalizer (Z : Set G) →
      ∀ x ∈ J₁, c * x * c⁻¹ ∈ J₁ := by
    intro c hcU hcZ x hx
    obtain ⟨hxU, hxZ⟩ := (hJ₁ x).mp hx
    refine (hJ₁ _).mpr ⟨(mem_normalizer_iff.mp hcU x).mp hxU, fun y hy => ?_⟩
    have hy' : c⁻¹ * y * c ∈ U := by
      have := (mem_normalizer_iff.mp (inv_mem hcU) y).mp hy
      rwa [inv_inv] at this
    have e : c * x * c⁻¹ * y * (c * x * c⁻¹)⁻¹ * y⁻¹ =
        c * (x * (c⁻¹ * y * c) * x⁻¹ * (c⁻¹ * y * c)⁻¹) * c⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp hcZ _).mp (hxZ _ hy')
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key k hkU hkZ x hx, fun hx => ?_⟩
  have := key k⁻¹ (inv_mem hkU) (inv_mem hkZ) _ hx
  rwa [show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at this

end CFSG.SeitzReduction.RankOne
