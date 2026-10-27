module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Scan

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts Subgroup

theorem exists_conj_mem_of_card {M : Type*} [Group M] [Finite M] {H P X : Subgroup M}
    (hPH : P ≤ H) (hcard : Nat.card P = 2 ^ (Nat.card H).factorization 2) (hXH : X ≤ H)
    (hX : IsPGroup 2 X) : ∃ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc' : Nat.card (P.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  set P' : Sylow 2 H := Sylow.ofCard (P.subgroupOf H) hc'
  have hX' : IsPGroup 2 (X.subgroupOf H) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q
  refine ⟨(g : M)⁻¹, H.inv_mem g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXH hx⟩ : H) ∈ (Q : Subgroup H) := hQ (mem_subgroupOf.mpr hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨p, hp, hpx⟩ := hxQ
  have hp' : (p : M) ∈ P := by
    have : p ∈ P.subgroupOf H := by rwa [Sylow.coe_ofCard] at hp
    exact mem_subgroupOf.mp this
  have hval : (g : M) * p * (g : M)⁻¹ = x := by
    have := congrArg Subtype.val hpx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [← hval]
  simpa [mul_assoc] using hp'

theorem factorization_241920 : (241920 : ℕ).factorization 2 = 8 := by
  have h : (241920 : ℕ) = 2 ^ 8 * 945 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 945)]
  simp

theorem le_sixteen_of_lt {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (h : Nat.card G < 32) : Nat.card G ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  rw [hk] at h ⊢
  have hk5 : k < 5 := by
    by_contra hk5
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> norm_num

theorem le_eight_of_lt {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (h : Nat.card G < 16) : Nat.card G ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  rw [hk] at h ⊢
  have hk4 : k < 4 := by
    by_contra hk4
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> norm_num

theorem isPGroup_of_sq {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) : IsPGroup 2 G :=
  fun g => ⟨1, by rw [pow_one, pow_two, h]⟩

theorem TR_le_R : TR ≤ R := by
  rw [TR, closure_le]
  rintro x (hx | hx)
  · exact S_le_R (wordSet_subset _ hx)
  · rcases hx with rfl | rfl
    · exact r₂_mem_R
    · exact r₃_mem_R

theorem mem_normalizer_of_involution {r : Equiv.Perm (Fin 42)} (hr : r * r = 1)
    (h : ∀ t ∈ T0, r * t * r ∈ T0) : r ∈ normalizer (T0 : Set (Equiv.Perm (Fin 42))) := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  rw [mem_normalizer_iff]
  intro t
  rw [hri]
  refine ⟨h t, fun ht => ?_⟩
  have := h _ ht
  rwa [show r * (r * t * r) * r = (r * r) * t * (r * r) by group, hr, one_mul, mul_one] at this

theorem TR_le_normalizer : TR ≤ normalizer (T0 : Set (Equiv.Perm (Fin 42))) := by
  have h2 := mem_normalizer_of_involution r₂_mul_self' fun t ht => r₂_conj_mem ht
  have h3 := mem_normalizer_of_involution r₃_mul_self' fun t ht => r₃_conj_mem ht
  rw [TR, closure_le]
  rintro x (hx | hx)
  · exact le_normalizer (subset_closure hx)
  · rcases hx with rfl | rfl
    · exact h2
    · exact h3

theorem TR_inf_S {x : Equiv.Perm (Fin 42)} (hx : x ∈ TR)
    (hxS : x ∈ S) : x ∈ T0 := by
  obtain ⟨t, ht, v, hv, rfl⟩ := (mem_TR_iff x).1 hx
  have hvS : v ∈ S := by
    have := S.mul_mem (S.inv_mem (T0_le_S ht)) hxS
    rwa [inv_mul_cancel_left] at this
  rcases hv with rfl | rfl | rfl | rfl
  · rwa [mul_one]
  · exact absurd hvS not_mem_S_r₂
  · exact absurd hvS not_mem_S_r₃
  · exact absurd hvS not_mem_S_r₄

theorem exists_conj_mem_TR {X : Subgroup (Equiv.Perm (Fin 42))}
    (hXR : X ≤ R) (hX : IsPGroup 2 X) : ∃ c ∈ R, ∀ x ∈ X, c * x * c⁻¹ ∈ TR :=
  exists_conj_mem_of_card TR_le_R (by rw [card_TR, card_R, factorization_241920]; norm_num) hXR hX

theorem card_le_sixteen {X : Subgroup (Equiv.Perm (Fin 42))}
    (hXR : X ≤ R) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX2 : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 16 := by
  have hX : IsPGroup 2 X := isPGroup_of_sq fun x => Subtype.ext (hX2 x x.2)
  obtain ⟨c, -, hc⟩ := exists_conj_mem_TR hXR hX
  have hsq : ∀ x ∈ X, c * x * c⁻¹ * (c * x * c⁻¹) = 1 := fun x hx => by
    rw [show c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ by group, hX2 x hx]
    group
  have hinj : ∀ x y : X, c * (x : Equiv.Perm (Fin 42)) * c⁻¹ = c * y * c⁻¹ → x = y :=
    fun x y h => Subtype.ext (by simpa using h)
  apply le_sixteen_of_lt hX
  by_cases hall : ∀ x ∈ X, c * x * c⁻¹ ∈ T0
  · refine lt_of_le_of_lt (Nat.card_le_card_of_injective
      (fun x : X => (⟨c * x * c⁻¹, hall x x.2, hsq x x.2⟩ : {t // t ∈ T0 ∧ t * t = 1}))
      fun x y h => hinj x y (congrArg Subtype.val h)) card_sq_T0_lt
  · push Not at hall
    obtain ⟨x₀, hx₀, hx₀T⟩ := hall
    have hcomm : ∀ x ∈ X, c * x * c⁻¹ * (c * x₀ * c⁻¹) = c * x₀ * c⁻¹ * (c * x * c⁻¹) :=
      fun x hx => by
        rw [show c * x * c⁻¹ * (c * x₀ * c⁻¹) = c * (x * x₀) * c⁻¹ by group, hXc x hx x₀ hx₀,
          show c * (x₀ * x) * c⁻¹ = c * x₀ * c⁻¹ * (c * x * c⁻¹) by group]
    refine lt_of_le_of_lt (Nat.card_le_card_of_injective
      (fun x : X => (⟨c * x * c⁻¹, hc x x.2, hsq x x.2, hcomm x x.2⟩ :
        {t // t ∈ TR ∧ t * t = 1 ∧ t * (c * x₀ * c⁻¹) = c * x₀ * c⁻¹ * t}))
      fun x y h => hinj x y (congrArg Subtype.val h))
      (card_sq_comm_lt (hc x₀ hx₀) (hsq x₀ hx₀) hx₀T)

theorem exists_std {X : Subgroup (Equiv.Perm (Fin 42))}
    (hXR : X ≤ R) (hX : IsPGroup 2 X) (hXS : Nat.card ↥(X ⊓ S) = 64) :
    ∃ c ∈ R, (∀ x ∈ X, c * x * c⁻¹ ∈ TR) ∧ (∀ x ∈ X, x ∈ S ↔ c * x * c⁻¹ ∈ T0) ∧
      ∀ t ∈ T0, ∃ x ∈ X ⊓ S, c * x * c⁻¹ = t := by
  obtain ⟨c, hcR, hc⟩ := exists_conj_mem_TR hXR hX
  have hiff : ∀ x ∈ X, x ∈ S ↔ c * x * c⁻¹ ∈ T0 := fun x hx =>
    ⟨fun hxS => TR_inf_S (hc x hx) (conj_mem_S hcR hxS),
      fun h => conj_mem_S' hcR (T0_le_S h)⟩
  refine ⟨c, hcR, hc, hiff, ?_⟩
  let f : ↥(X ⊓ S) → ↥T0 := fun x =>
    ⟨c * x * c⁻¹, (hiff x (mem_inf.1 x.2).1).1 (mem_inf.1 x.2).2⟩
  have hf : Function.Injective f := fun x y h => Subtype.ext (by
    have := congrArg Subtype.val h
    simpa [f] using this)
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hXS, card_T0'])
  intro t ht
  obtain ⟨x, hx⟩ := hb.2 ⟨t, ht⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

end CFSG.ComponentClassification.HSFLit.AutL34
