module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.DeltaClosure

section Coprime

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem apply_apply_of_mul_eq_one {σ : MulAut Y} (hσ : σ * σ = 1) (y : Y) : σ (σ y) = y := by
  simpa using congrArg (fun τ : MulAut Y => τ y) hσ

omit [Finite Y] in
theorem exists_fixed_mul_of_inv_mul_mem (σ : MulAut Y) (hσ : σ * σ = 1) {P : Subgroup Y}
    (hP : Odd (Nat.card P)) {y : Y} (hy : y⁻¹ * σ y ∈ P) :
    ∃ p ∈ P, σ (y * p) = y * p := by
  set y' : Y := y⁻¹ * σ y with hy'
  have hσσ := apply_apply_of_mul_eq_one hσ
  have hinv : σ y' = y'⁻¹ := by
    rw [hy', map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
  have hodd : Odd (orderOf y') :=
    Odd.of_dvd_nat hP (Subgroup.orderOf_dvd_natCard P hy)
  obtain ⟨j, hj⟩ := hodd
  have hk : orderOf y' + 1 = 2 * (j + 1) := by omega
  set u : Y := y' ^ (j + 1) with hu
  refine ⟨u, P.pow_mem hy _, ?_⟩
  have hσu : σ u = u⁻¹ := by rw [hu, map_pow, hinv, inv_pow]
  have huu : u * u = y' := by
    rw [hu, ← pow_add, ← two_mul, ← hk, pow_succ, pow_orderOf_eq_one, one_mul]
  have hσy : σ y = y * y' := by rw [hy']; group
  calc σ (y * u) = σ y * σ u := map_mul _ _ _
    _ = y * (y' * u⁻¹) := by rw [hσy, hσu, mul_assoc]
    _ = y * u := by rw [← huu, mul_assoc, mul_inv_cancel, mul_one]

end Coprime

section Quotient

variable {Y : Type} [Group Y]

@[expose] noncomputable def quotAut (P : Subgroup Y) [P.Normal] (σ : MulAut Y)
    (hσP : P.map (σ : Y →* Y) = P) : MulAut (Y ⧸ P) :=
  QuotientGroup.congr P P σ hσP

theorem quotAut_mk (P : Subgroup Y) [P.Normal] (σ : MulAut Y) (hσP : P.map (σ : Y →* Y) = P)
    (y : Y) : quotAut P σ hσP (QuotientGroup.mk y) = QuotientGroup.mk (σ y) :=
  rfl

theorem quotAut_mul_self (P : Subgroup Y) [P.Normal] (σ : MulAut Y) (hσ : σ * σ = 1)
    (hσP : P.map (σ : Y →* Y) = P) : quotAut P σ hσP * quotAut P σ hσP = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  show QuotientGroup.mk (σ (σ y)) = QuotientGroup.mk y
  rw [apply_apply_of_mul_eq_one hσ]

theorem exists_fixed_lift (P : Subgroup Y) [P.Normal] (hP : Odd (Nat.card P)) (σ : MulAut Y)
    (hσ : σ * σ = 1) (hσP : P.map (σ : Y →* Y) = P) {x : Y ⧸ P}
    (hx : x ∈ fixedSubgroup (quotAut P σ hσP)) :
    ∃ y ∈ fixedSubgroup σ, (QuotientGroup.mk y : Y ⧸ P) = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (QuotientGroup.mk (σ y) : Y ⧸ P) = QuotientGroup.mk y := hx
  have h2 : y⁻¹ * σ y ∈ P := QuotientGroup.eq.mp h1.symm
  obtain ⟨p, hp, hfix⟩ := exists_fixed_mul_of_inv_mul_mem σ hσ hP h2
  refine ⟨y * p, hfix, ?_⟩
  have h3 : (y * p)⁻¹ * y = p⁻¹ := by group
  exact QuotientGroup.eq.mpr (by rw [h3]; exact P.inv_mem hp)

variable [Finite Y]

theorem oddCoreIn_fixed_le_of_quotient (P : Subgroup Y) [P.Normal] (hP : Odd (Nat.card P))
    (σ : MulAut Y) (hσ : σ * σ = 1) (hσP : P.map (σ : Y →* Y) = P)
    (h : oddCoreIn (fixedSubgroup (quotAut P σ hσP)) = ⊥) :
    oddCoreIn (fixedSubgroup σ) ≤ P := by
  set π := QuotientGroup.mk' P with hπ
  set N := oddCoreIn (fixedSubgroup σ) with hN
  have hNC : N ≤ fixedSubgroup σ := oddCoreIn_le _
  have hle : N.map π ≤ oddCoreIn (fixedSubgroup (quotAut P σ hσP)) := by
    refine le_oddCoreIn_of_normalizes ?_ ?_
      ((odd_card_oddCoreIn (fixedSubgroup σ)).of_dvd_nat (Subgroup.card_map_dvd N π))
    · rintro _ ⟨n, hn, rfl⟩
      have : σ n = n := hNC hn
      show quotAut P σ hσP (QuotientGroup.mk n) = QuotientGroup.mk n
      rw [quotAut_mk, this]
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := exists_fixed_lift P hP σ hσ hσP hx
      exact Subgroup.le_normalizer_map π ⟨c, normalizer_oddCoreIn _ hc, rfl⟩
  intro n hn
  have h1 : π n ∈ oddCoreIn (fixedSubgroup (quotAut P σ hσP)) := hle ⟨n, hn, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff n).mp h1

end Quotient

section Local

variable {G : Type} [Group G]

@[expose] def conjAut (Y : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G)) :
    MulAut ↥Y where
  toFun y := ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha y).mp y.2⟩
  invFun y := ⟨a⁻¹ * y * a, (Subgroup.mem_normalizer_iff.mp ha _).mpr (by
    have e : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [e]
    exact y.2)⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' y z := Subtype.ext (by simp [mul_assoc])

theorem conjAut_apply (Y : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G))
    (y : ↥Y) : ((conjAut Y a ha y : ↥Y) : G) = a * y * a⁻¹ :=
  rfl

theorem conjAut_mul_self (Y : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G))
    (h2 : a * a = 1) : conjAut Y a ha * conjAut Y a ha = 1 := by
  ext y
  show a * (a * (y : G) * a⁻¹) * a⁻¹ = y
  have : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
  rw [this]
  calc a * (a * (y : G) * a) * a = (a * a) * (y : G) * (a * a) := by group
    _ = y := by rw [h2]; group

theorem map_fixedSubgroup_conjAut (Y : Subgroup G) (a : G)
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) :
    (fixedSubgroup (conjAut Y a ha)).map Y.subtype = Y ⊓ Subgroup.centralizer ({a} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : a * (y : G) * a⁻¹ = y := congrArg Subtype.val hy
    refine ⟨y.2, ?_⟩
    show (y : G) * a = a * (y : G)
    calc (y : G) * a = (a * (y : G) * a⁻¹) * a := by rw [h]
      _ = a * (y : G) := by group
  · rintro ⟨hxY, hxa⟩
    refine ⟨⟨x, hxY⟩, Subtype.ext ?_, rfl⟩
    show a * x * a⁻¹ = x
    calc a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [hxa]
      _ = x := by group

end Local

end CFSG.ClassicalInvolution.Q3.Q3NM
