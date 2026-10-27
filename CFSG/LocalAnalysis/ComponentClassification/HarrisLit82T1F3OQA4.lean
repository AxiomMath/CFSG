module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

abbrev psl23 : SL(2, ZMod 3) →* PSL(2, ZMod 3) := QuotientGroup.mk' (center SL(2, ZMod 3))

theorem psl23_surjective : Function.Surjective psl23 := QuotientGroup.mk'_surjective _

theorem eq_one_or_eq_neg_one_of_mem_center_sl23 {z : SL(2, ZMod 3)}
    (hz : z ∈ center SL(2, ZMod 3)) : z = 1 ∨ z = -1 := by
  have h : ∀ z : SL(2, ZMod 3), (∀ g : SL(2, ZMod 3), g * z = z * g) → z = 1 ∨ z = -1 := by
    decide
  exact h z (mem_center_iff.mp hz)

theorem neg_one_mem_center_sl23 : (-1 : SL(2, ZMod 3)) ∈ center SL(2, ZMod 3) := by
  rw [mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

theorem psl23_eq_iff {y y' : SL(2, ZMod 3)} : psl23 y = psl23 y' ↔ y' = y ∨ y' = -y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    rcases eq_one_or_eq_neg_one_of_mem_center_sl23 h with h1 | h1
    · left
      calc y' = y * (y⁻¹ * y') := by group
        _ = y := by rw [h1, mul_one]
    · right
      calc y' = y * (y⁻¹ * y') := by group
        _ = -y := by rw [h1, mul_neg_one]
  · rintro (rfl | rfl)
    · rw [inv_mul_cancel]
      exact one_mem _
    · rw [mul_neg, inv_mul_cancel]
      exact neg_one_mem_center_sl23

theorem psl23_eq_one_iff {y : SL(2, ZMod 3)} : psl23 y = 1 ↔ y = 1 ∨ y = -1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · exact eq_one_or_eq_neg_one_of_mem_center_sl23
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact neg_one_mem_center_sl23

private theorem sl23_pow_twelve : ∀ y : SL(2, ZMod 3), y ^ 12 = 1 := by decide

private theorem sl23_conj_escape : ∀ y : SL(2, ZMod 3), y ≠ 1 → y ≠ -1 →
    ∃ h : SL(2, ZMod 3), ∀ k : Fin 12,
      h * y * h⁻¹ ≠ y ^ (k : ℕ) ∧ h * y * h⁻¹ ≠ -(y ^ (k : ℕ)) := by
  decide

private theorem sl23_cube_escape : ∀ y : SL(2, ZMod 3), y ≠ 1 → y ≠ -1 →
    (y ^ 3 = 1 ∨ y ^ 3 = -1) →
      ∃ h : SL(2, ZMod 3), (h * y * h⁻¹ * y⁻¹) ^ 3 ≠ 1 ∧ (h * y * h⁻¹ * y⁻¹) ^ 3 ≠ -1 := by
  decide

theorem eq_one_of_forall_conj_mem_zpowers {x : PSL(2, ZMod 3)}
    (hx : ∀ a : PSL(2, ZMod 3), a * x * a⁻¹ ∈ zpowers x) : x = 1 := by
  obtain ⟨y, rfl⟩ := psl23_surjective x
  by_contra hne
  have hy1 : y ≠ 1 := fun h => hne (by rw [h, map_one])
  have hy2 : y ≠ -1 := fun h => hne (psl23_eq_one_iff.mpr (.inr h))
  obtain ⟨h, hh⟩ := sl23_conj_escape y hy1 hy2
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hx (psl23 h))
  have h12 : y ^ (12 : ℕ) = 1 := sl23_pow_twelve y
  have hm' : y ^ m = y ^ ((m % 12).toNat : ℕ) := by
    rw [zpow_eq_zpow_emod' m h12, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg m
      (by norm_num))]
    norm_num
  have hlt : (m % 12).toNat < 12 := by omega
  rw [← map_zpow, hm', ← map_inv, ← map_mul, ← map_mul, psl23_eq_iff] at hm
  rcases hm with hm | hm
  · exact (hh ⟨_, hlt⟩).1 hm
  · exact (hh ⟨_, hlt⟩).2 hm

theorem eq_one_of_forall_conj_mul_cube {x : PSL(2, ZMod 3)} (hx3 : x ^ 3 = 1)
    (hx : ∀ a : PSL(2, ZMod 3), (a * x * a⁻¹ * x⁻¹) ^ 3 = 1) : x = 1 := by
  obtain ⟨y, rfl⟩ := psl23_surjective x
  by_contra hne
  have hy1 : y ≠ 1 := fun h => hne (by rw [h, map_one])
  have hy2 : y ≠ -1 := fun h => hne (psl23_eq_one_iff.mpr (.inr h))
  have hy3 : y ^ 3 = 1 ∨ y ^ 3 = -1 := by
    rw [← map_pow] at hx3
    exact psl23_eq_one_iff.mp hx3
  obtain ⟨h, hh1, hh2⟩ := sl23_cube_escape y hy1 hy2 hy3
  have h1 := hx (psl23 h)
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, psl23_eq_one_iff] at h1
  rcases h1 with h1 | h1
  · exact hh1 h1
  · exact hh2 h1

private theorem exists_sl23_pair : ∃ a b : SL(2, ZMod 3), a * b ≠ b * a ∧ a * b ≠ -(b * a) ∧
    a ^ 2 ≠ 1 ∧ a ^ 2 ≠ -1 :=
  ⟨⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩,
    ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide, by decide,
    by decide⟩

theorem exists_psl23_mul_ne : ∃ a b : PSL(2, ZMod 3), a * b ≠ b * a := by
  obtain ⟨a, b, h1, h2, -, -⟩ := exists_sl23_pair
  refine ⟨psl23 a, psl23 b, fun h => ?_⟩
  rw [← map_mul, ← map_mul, psl23_eq_iff] at h
  rcases h with h | h
  · exact h1 h.symm
  · exact h2 (by rw [h, neg_neg])

private theorem one_ne_neg_one_sl23 : (1 : SL(2, ZMod 3)) ≠ -1 := by decide

private theorem exists_sl23_four : ∃ c : SL(2, ZMod 3), c * c = -1 :=
  ⟨⟨!![0, 2; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩, by decide⟩

theorem exists_psl23_involution : ∃ a : PSL(2, ZMod 3), a ≠ 1 ∧ a ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := exists_sl23_four
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [one_mul] at hc
    exact one_ne_neg_one_sl23 hc
  have hc2 : c ≠ -1 := by
    rintro rfl
    rw [neg_mul_neg, one_mul] at hc
    exact one_ne_neg_one_sl23 hc
  refine ⟨psl23 c, fun h1 => ?_, ?_⟩
  · rcases psl23_eq_one_iff.mp h1 with h | h
    · exact hc1 h
    · exact hc2 h
  · rw [← map_pow, sq, hc, psl23_eq_one_iff]
    exact .inr rfl

section Steps

variable {A : Type*} [Group A] {R : Subgroup A} {φ : ↥R →* PSL(2, ZMod 3)}

theorem forall_eq_one_of_cyclic {N M : Subgroup A} [hN : N.Normal] {Q : Type*} [Group Q]
    [IsCyclic Q] (ρ : ↥N →* Q) (hρ : ∀ x : ↥N, ρ x = 1 → (x : A) ∈ M)
    (hφ : Function.Surjective φ) (hM : ∀ r : ↥R, (r : A) ∈ M → φ r = 1) :
    ∀ r : ↥R, (r : A) ∈ N → φ r = 1 := by
  set H : Subgroup Q := (R.subgroupOf N).map ρ with hH
  obtain ⟨⟨y₀, hy₀⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥H)
  obtain ⟨x₀, hx₀R, rfl⟩ := hy₀
  set r₀ : ↥R := ⟨x₀, hx₀R⟩ with hr₀
  have hpow : ∀ r : ↥R, ∀ hr : (r : A) ∈ N, φ r ∈ zpowers (φ r₀) := by
    intro r hr
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hgen ⟨ρ ⟨r, hr⟩, ⟨r, hr⟩, r.2, rfl⟩)
    have hk' : ρ (x₀ ^ k) = ρ ⟨r, hr⟩ := by
      rw [map_zpow]
      exact congrArg Subtype.val hk
    have h1 : ρ ((x₀ ^ k)⁻¹ * ⟨r, hr⟩) = 1 := by rw [map_mul, map_inv, hk', inv_mul_cancel]
    have h2 := hρ _ h1
    have h3 : φ ((r₀ ^ k)⁻¹ * r) = 1 := hM _ (by simpa [hr₀] using h2)
    rw [map_mul, map_inv, map_zpow, inv_mul_eq_one] at h3
    exact ⟨k, h3⟩
  have hconj : ∀ a : PSL(2, ZMod 3), a * φ r₀ * a⁻¹ ∈ zpowers (φ r₀) := by
    intro a
    obtain ⟨s, rfl⟩ := hφ a
    have h1 : ((s * r₀ * s⁻¹ : ↥R) : A) ∈ N := hN.conj_mem _ x₀.2 _
    have h2 := hpow (s * r₀ * s⁻¹) h1
    rwa [map_mul, map_mul, map_inv] at h2
  have h1 := eq_one_of_forall_conj_mem_zpowers hconj
  intro r hr
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hpow r hr)
  rw [← hk, h1, one_zpow]

theorem forall_eq_one_of_cube {N M : Subgroup A} [hN : N.Normal]
    (hcube : ∀ x ∈ N, x ^ 3 ∈ M) (hφ : Function.Surjective φ)
    (hM : ∀ r : ↥R, (r : A) ∈ M → φ r = 1) : ∀ r : ↥R, (r : A) ∈ N → φ r = 1 := by
  intro r hr
  apply eq_one_of_forall_conj_mul_cube
  · rw [← map_pow]
    exact hM _ (by simpa using hcube _ hr)
  · intro a
    obtain ⟨s, rfl⟩ := hφ a
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow]
    apply hM
    have h1 : ((s * r * s⁻¹ * r⁻¹ : ↥R) : A) ∈ N :=
      N.mul_mem (hN.conj_mem _ hr _) (N.inv_mem hr)
    simpa using hcube _ h1

theorem false_of_forall_eq_one_ker {B : Type*} [Group B] (ψ : A →* B)
    (hψ : ∀ a b : A, ψ a * ψ b = ψ b * ψ a) (hφ : Function.Surjective φ)
    (hker : ∀ r : ↥R, ψ r = 1 → φ r = 1) : False := by
  obtain ⟨a, b, hab⟩ := exists_psl23_mul_ne
  obtain ⟨r, rfl⟩ := hφ a
  obtain ⟨s, rfl⟩ := hφ b
  apply hab
  have hψ1 : ψ ((r * s * r⁻¹ * s⁻¹ : ↥R) : A) = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [hψ (r : A) (s : A)]
    group
  have h1 : φ (r * s * r⁻¹ * s⁻¹) = 1 := hker _ hψ1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc φ r * φ s = φ r * φ s * (φ r)⁻¹ * (φ s)⁻¹ * (φ s * φ r) := by group
    _ = φ s * φ r := by rw [h1, one_mul]

theorem false_of_forall_eq_one_odd {M : Subgroup A} (hodd : ∀ x : A, ∃ m : ℕ, Odd m ∧ x ^ m ∈ M)
    (hφ : Function.Surjective φ) (hM : ∀ r : ↥R, (r : A) ∈ M → φ r = 1) : False := by
  obtain ⟨a, ha1, ha2⟩ := exists_psl23_involution
  obtain ⟨r, rfl⟩ := hφ a
  obtain ⟨m, ⟨k, rfl⟩, hm⟩ := hodd r
  have h1 : φ (r ^ (2 * k + 1)) = 1 := hM _ (by simpa using hm)
  rw [map_pow, pow_succ, pow_mul, ha2, one_pow, one_mul] at h1
  exact ha1 h1

end Steps

@[expose] def OutNoA4 (T : Type*) [Group T] : Prop :=
  ∀ (R : Subgroup (MulAut T)) (φ : ↥R →* PSL(2, ZMod 3)), Function.Surjective φ →
    ∃ r : ↥R, (r : MulAut T) ∈ (MulAut.conj : T →* MulAut T).range ∧ φ r ≠ 1

theorem outNoA4_of_false {T : Type*} [Group T]
    (h : ∀ (R : Subgroup (MulAut T)) (φ : ↥R →* PSL(2, ZMod 3)), Function.Surjective φ →
      (∀ r : ↥R, (r : MulAut T) ∈ (MulAut.conj : T →* MulAut T).range → φ r = 1) → False) :
    OutNoA4 T := by
  intro R φ hφ
  by_contra hne
  push Not at hne
  exact h R φ hφ hne

theorem OutNoA4.of_mulEquiv {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') (h : OutNoA4 T) :
    OutNoA4 T' := by
  intro R' φ' hφ'
  set c := MulAut.congr e with hc
  let R : Subgroup (MulAut T) := R'.comap c.toMonoidHom
  let ι : ↥R →* ↥R' :=
    { toFun := fun r => ⟨c r, r.2⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun a b => Subtype.ext (map_mul c (a : MulAut T) (b : MulAut T)) }
  have hι : Function.Surjective ι := by
    intro r'
    refine ⟨⟨c.symm r', ?_⟩, Subtype.ext (c.apply_symm_apply r')⟩
    change c (c.symm r') ∈ R'
    rw [c.apply_symm_apply]
    exact r'.2
  obtain ⟨r, ⟨x, hx⟩, hne⟩ := h R (φ'.comp ι) (hφ'.comp hι)
  refine ⟨ι r, ⟨e x, ?_⟩, hne⟩
  change MulAut.conj (e x) = c r
  rw [← hx, hc, OuterAutomorphisms.congr_conj]

theorem OutNoA4.of_centerQuotient {X : Type*} [Group X] [Group.IsPerfect X]
    (h : OutNoA4 (X ⧸ center X)) : OutNoA4 X := by
  intro R φ hφ
  set ι := PerfectAutomorphisms.centerQuotientHom X with hιdef
  have hinj : Function.Injective ι := PerfectAutomorphisms.centerQuotientHom_injective X
  let e : ↥R ≃* ↥(R.map ι) := R.equivMapOfInjective ι hinj
  obtain ⟨r', ⟨q, hq⟩, hne⟩ := h (R.map ι) (φ.comp e.symm.toMonoidHom)
    (hφ.comp e.symm.surjective)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) q
  refine ⟨e.symm r', ⟨x, ?_⟩, hne⟩
  apply hinj
  rw [OuterAutomorphisms.centerQuotient_conj, hq]
  have h1 : ((e (e.symm r') : ↥(R.map ι)) : MulAut (X ⧸ center X)) = r' := by
    rw [e.apply_symm_apply]
  rw [← h1]
  rfl

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
