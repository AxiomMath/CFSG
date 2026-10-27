module

public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

section Commutators

variable {E : Type*} [Group E]

theorem commute_commutatorElement_of_mem_center {a x y : E} (hx : ⁅a, x⁆ ∈ center E)
    (hy : ⁅a, y⁆ ∈ center E) : a * ⁅x, y⁆ = ⁅x, y⁆ * a := by
  have hx' : a * x * a⁻¹ = x * ⁅a, x⁆ := by
    rw [mem_center_iff.mp hx x, commutatorElement_def]
    group
  have hy' : a * y * a⁻¹ = y * ⁅a, y⁆ := by
    rw [mem_center_iff.mp hy y, commutatorElement_def]
    group
  have key : a * ⁅x, y⁆ * a⁻¹ = ⁅x, y⁆ := by
    have h : a * ⁅x, y⁆ * a⁻¹ = ⁅a * x * a⁻¹, a * y * a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h, hx', hy', CentralExtensions.commutator_mul_center_left _ _ _ hx,
      CentralExtensions.commutator_mul_center_right _ _ _ hy]
  calc a * ⁅x, y⁆ = a * ⁅x, y⁆ * a⁻¹ * a := by group
    _ = ⁅x, y⁆ * a := by rw [key]

theorem commutatorElement_commutatorElement_eq_of_involutions {x y : E} (hx : x * x = 1)
    (hy : y * y = 1) : ⁅⁅x, y⁆, x⁆ = ⁅⁅x, y⁆, y⁆ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  simp only [commutatorElement_def, mul_inv_rev, hxi, hyi]
  calc _ = x * y * x * y * x * y * x * y * (x * x) := by group
    _ = x * y * x * y * (y * y) * x * y * x * y := by rw [hx, hy]; group
    _ = _ := by group

end Commutators

section Norm

variable {A G : Type*} [CommGroup A] [Finite A] [Group G]

theorem exists_norm_complement (f : A →* G) (φ : A →* A) (hφ : ∀ z, f z = 1 → φ z = z)
    (hnorm : ∀ z, f (z * φ z * φ (φ z)) = 1) (h2 : ∀ z, f z * f z = 1) :
    ∃ C : Subgroup A, (∀ c ∈ C, f c = 1 → c = 1) ∧ (∀ z, ∃ c ∈ C, f c = f z) ∧
      ∀ c ∈ C, φ c ∈ C := by
  set n := Nat.card A with hn
  set n₂ := 2 ^ n.factorization 2 with hn₂
  set m := n / n₂ with hm
  have hnm : n₂ * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hmodd : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two Nat.card_pos.ne'
  have hcop : Nat.Coprime 3 n₂ := Nat.Coprime.pow_right _ (by norm_num)
  let N : A →* A := MonoidHom.id A * φ * φ.comp φ
  have hN : ∀ z, N z = z * φ z * φ (φ z) := fun z => rfl
  let C : Subgroup A := N.ker ⊓ (powMonoidHom n₂).ker
  have hmemC : ∀ c, c ∈ C ↔ c * φ c * φ (φ c) = 1 ∧ c ^ n₂ = 1 := fun c => Iff.rfl
  refine ⟨C, fun c hc hfc => ?_, fun z => ?_, fun c hc => ?_⟩
  · obtain ⟨hNc, hc2⟩ := (hmemC c).mp hc
    have hφc := hφ c hfc
    rw [hφc, hφc] at hNc
    have h3 : c ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact hNc
    have h := pow_gcd_eq_one.mpr ⟨h3, hc2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  · obtain ⟨t, ht⟩ : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hmodd)
    set z₁ := z ^ m with hz₁def
    have hfz₁ : f z₁ = f z := by
      rw [map_pow, ht, pow_succ, pow_mul, sq, h2, one_pow, one_mul]
    have hz₁ : z₁ ^ n₂ = 1 := by
      rw [hz₁def, ← pow_mul, mul_comm, hnm, hn, pow_card_eq_one']
    set κ₀ := N z₁ with hκ₀def
    have hfκ₀ : f κ₀ = 1 := hnorm z₁
    have hκ₀ : κ₀ ^ n₂ = 1 := by rw [hκ₀def, ← map_pow, hz₁, map_one]
    set κ := κ₀ ^ 3 ^ (Nat.totient n₂ - 1) with hκdef
    have hκ3 : κ ^ 3 = κ₀ := by
      have hφ1 : 1 ≤ Nat.totient n₂ := Nat.totient_pos.mpr (pow_pos two_pos _)
      have he : 3 ^ (Nat.totient n₂ - 1) * 3 = 3 ^ Nat.totient n₂ := by
        rw [← pow_succ, Nat.sub_add_cancel hφ1]
      rw [hκdef, ← pow_mul, he]
      conv_rhs => rw [← pow_one κ₀]
      rw [pow_eq_pow_iff_modEq]
      exact (Nat.ModEq.pow_totient hcop).of_dvd (orderOf_dvd_of_pow_eq_one hκ₀)
    have hfκ : f κ = 1 := by rw [hκdef, map_pow, hfκ₀, one_pow]
    have hNκ : N κ = κ₀ := by
      rw [hN, hφ κ hfκ, hφ κ hfκ, ← hκ3, pow_three, mul_assoc]
    have hκn : κ ^ n₂ = 1 := by rw [hκdef, ← pow_mul, mul_comm, pow_mul, hκ₀, one_pow]
    refine ⟨z₁ * κ⁻¹, (hmemC _).mpr ⟨?_, ?_⟩, ?_⟩
    · rw [← hN, map_mul, map_inv, hNκ, hκ₀def, mul_inv_cancel]
    · rw [mul_pow, inv_pow, hz₁, hκn, inv_one, one_mul]
    · rw [map_mul, map_inv, hfκ, inv_one, mul_one, hfz₁]
  · obtain ⟨hNc, hc2⟩ := (hmemC c).mp hc
    refine (hmemC _).mpr ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul, hNc, map_one]
    · rw [← map_pow, hc2, map_one]

end Norm

section Lift

variable {k E G : Type*} [Ring k] [Group E] [Finite E] [Group G]

theorem exists_equivariant_additive_lift (η : E →* G) (hker : ∀ z, η z = 1 → z ∈ center E)
    (r : k → G) (hr : ∀ a b, r (a + b) = r a * r b) (hr2 : ∀ a, r a * r a = 1)
    (hlift : ∀ a, ∃ z, η z = r a)
    (hcomm : ∀ z₁ z₂ : E, (∃ a, η z₁ = r a) → (∃ a, η z₂ = r a) → z₁ * z₂ = z₂ * z₁)
    (u : E) (ζ : k) (hu : ∀ a, η u * r a * (η u)⁻¹ = r (ζ * a)) (hζ : 1 + ζ + ζ * ζ = 0) :
    ∃ ρ : k → E, (∀ a, η (ρ a) = r a) ∧ (∀ a b, ρ (a + b) = ρ a * ρ b) ∧
      ∀ a, u * ρ a * u⁻¹ = ρ (ζ * a) := by
  have hr0 : r 0 = 1 := by
    have h := hr 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  let S : Subgroup E :=
    { carrier := {z | ∃ a, η z = r a}
      one_mem' := ⟨0, by rw [map_one, hr0]⟩
      mul_mem' := fun {z w} ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [map_mul, ha, hb, hr]⟩
      inv_mem' := fun {z} ⟨a, ha⟩ => ⟨a, by rw [map_inv, ha, inv_eq_of_mul_eq_one_right (hr2 a)]⟩ }
  have hmemS : ∀ z, z ∈ S ↔ ∃ a, η z = r a := fun z => Iff.rfl
  let _ : CommGroup S :=
    { (inferInstance : Group S) with
      mul_comm := fun z w => Subtype.ext (hcomm z w z.2 w.2) }
  have huS : ∀ z ∈ S, u * z * u⁻¹ ∈ S := fun z hz => by
    obtain ⟨a, ha⟩ := (hmemS z).mp hz
    exact (hmemS _).mpr ⟨ζ * a, by rw [map_mul, map_mul, map_inv, ha, hu]⟩
  let φ : S →* S :=
    { toFun := fun z => ⟨u * z * u⁻¹, huS z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun z w => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ z : S, (φ z : E) = u * z * u⁻¹ := fun z => rfl
  let f : S →* G := η.comp S.subtype
  have hf : ∀ z : S, f z = η z := fun z => rfl
  obtain ⟨C, hC1, hC2, hC3⟩ := exists_norm_complement f φ (fun z hz => by
      have hc := hker z (by rw [← hf]; exact hz)
      apply Subtype.ext
      rw [hφ, mem_center_iff.mp hc u, mul_inv_cancel_right])
    (fun z => by
      obtain ⟨a, ha⟩ := (hmemS z).mp z.2
      have h1 : f (φ z) = r (ζ * a) := by rw [hf, hφ, map_mul, map_mul, map_inv, ha, hu]
      have h2 : f (φ (φ z)) = r (ζ * (ζ * a)) := by
        rw [hf, hφ, map_mul, map_mul, map_inv, ← hf, h1, hu]
      rw [map_mul, map_mul, hf z, ha, h1, h2, ← hr, ← hr]
      have : a + ζ * a + ζ * (ζ * a) = 0 :=
        calc a + ζ * a + ζ * (ζ * a) = (1 + ζ + ζ * ζ) * a := by
              rw [add_mul, add_mul, one_mul, mul_assoc]
          _ = 0 := by rw [hζ, zero_mul]
      rw [this, hr0])
    (fun z => by
      obtain ⟨a, ha⟩ := (hmemS z).mp z.2
      rw [hf, ha, hr2])
  have hex : ∀ a, ∃ c : S, c ∈ C ∧ f c = r a := fun a => by
    obtain ⟨z, hz⟩ := hlift a
    obtain ⟨c, hc, hfc⟩ := hC2 ⟨z, a, hz⟩
    exact ⟨c, hc, hfc.trans hz⟩
  choose c hcC hfc using hex
  have huniq : ∀ c₁ ∈ C, ∀ c₂ ∈ C, f c₁ = f c₂ → c₁ = c₂ := fun c₁ h₁ c₂ h₂ h => by
    have h1 := hC1 (c₁ * c₂⁻¹) (C.mul_mem h₁ (C.inv_mem h₂))
      (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  refine ⟨fun a => (c a : E), fun a => hfc a, fun a b => ?_, fun a => ?_⟩
  · have h := huniq (c (a + b)) (hcC _) (c a * c b) (C.mul_mem (hcC a) (hcC b))
      (by rw [hfc, map_mul, hfc, hfc, hr])
    change (c (a + b) : E) = c a * c b
    rw [h]
    rfl
  · have h := huniq (φ (c a)) (hC3 _ (hcC a)) (c (ζ * a)) (hcC _)
      (by rw [hfc, hf, hφ, map_mul, map_mul, map_inv, ← hf, hfc, hu])
    change u * (c a : E) * u⁻¹ = c (ζ * a)
    rw [← h]
    rfl

end Lift

end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
