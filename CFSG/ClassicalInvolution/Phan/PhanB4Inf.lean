module

public import CFSG.ClassicalInvolution.Phan.PhanB3Good

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.PhanD4 (exists_normOne_sq_ne_one mem_range_torusTwo_of_commute
  exists_embSUid_torus_of_commute conjDiag_one)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] (S : PhanFamilyB3 C G)

@[expose] noncomputable def torusSub : Subgroup G := (mTor S).range

theorem mTor_mem_torusSub (t : Fin 3 → normOne (unitaryInvolution K p f)) :
    mTor S t ∈ torusSub S :=
  ⟨t, rfl⟩

theorem tor_mem_torusSub (i : Fin 3) (x : normOne (unitaryInvolution K p f)) :
    tor S i x ∈ torusSub S := by
  rw [← mTor_mulSingle]
  exact mTor_mem_torusSub S _

theorem torusSub_comm {a b : G} (ha : a ∈ torusSub S) (hb : b ∈ torusSub S) : a * b = b * a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

variable {S}

section Inf

theorem GoodFamily.exists_tor_of_comm (hg : GoodFamily S) (i : Fin 3)
    {x₀ : normOne (unitaryInvolution K p f)} (hx₀ : x₀ * x₀ ≠ 1) {A : Su K p f 2}
    (h : tor S i x₀ * S.ι i A = S.ι i A * tor S i x₀) :
    ∃ y, S.ι i A = tor S i y := by
  have h' : S.ι i (torusTwo (unitaryInvolution K p f) x₀ * A) =
      S.ι i (A * torusTwo (unitaryInvolution K p f) x₀) := by
    rw [map_mul, map_mul]
    exact h
  obtain ⟨y, hy⟩ := mem_range_torusTwo_of_commute hx₀ (hg.inj i h').symm
  exact ⟨y, by rw [← hy]; rfl⟩

variable (hq : 3 ≤ p ^ f)

include hK hq in
theorem GoodFamily.exists_tor_of_mem_range (hg : GoodFamily S) (i : Fin 3) {A : Su K p f 2}
    (hT : S.ι i A ∈ torusSub S) : ∃ y, S.ι i A = tor S i y := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  exact hg.exists_tor_of_comm i hx₀ ((torusSub_comm S (tor_mem_torusSub S i x₀) hT))

include hK hq in
theorem GoodFamily.exists_tor_of_θ (hg : GoodFamily S) {B : Su K p f 3}
    (hT : S.θ B ∈ torusSub S) : ∃ y w, S.θ B = tor S 0 y * tor S 1 w := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hc := torusSub_comm S (tor_mem_torusSub S 0 x₀) hT
  have hc' : S.θ (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) x₀) *
      B) = S.θ (B * embSUid (unitaryInvolution K p f) 2
        (torusTwo (unitaryInvolution K p f) x₀)) := by
    rw [map_mul, map_mul]
    have := hc
    simp only [tor, MonoidHom.comp_apply, ι_zero] at this
    exact this
  obtain ⟨y, w, hyw⟩ := exists_embSUid_torus_of_commute hx₀ (hg.θ_injective hc').symm
  refine ⟨y, w, ?_⟩
  rw [hyw, map_mul]
  simp only [tor, MonoidHom.comp_apply, ι_zero, ι_one_θ]

include hK hq in
theorem GoodFamily.exists_tor_of_ϑ (hg : GoodFamily S) {g : StatedSp 2 F}
    (hT : S.ϑ g ∈ torusSub S) : ∃ y w, S.ϑ g = tor S 1 y * tor S 2 w := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hc1 := torusSub_comm S (tor_mem_torusSub S 1 x₀) hT
  have hc2 := torusSub_comm S (tor_mem_torusSub S 2 x₀) hT
  have hc1' : g * C.ℓ (torusTwo (unitaryInvolution K p f) x₀) =
      C.ℓ (torusTwo (unitaryInvolution K p f) x₀) * g := by
    apply hg.ϑ_injective
    rw [map_mul, map_mul]
    have := hc1
    simp only [tor, MonoidHom.comp_apply, ι_one_ϑ] at this
    exact this.symm
  have hc2' : g * C.s (torusTwo (unitaryInvolution K p f) x₀) =
      C.s (torusTwo (unitaryInvolution K p f) x₀) * g := by
    apply hg.ϑ_injective
    rw [map_mul, map_mul]
    have := hc2
    simp only [tor, MonoidHom.comp_apply, ι_two] at this
    exact this.symm
  obtain ⟨y, w, hyw⟩ := C.cent x₀ hx₀ g hc1' hc2'
  refine ⟨y, w, ?_⟩
  rw [hyw, map_mul]
  simp only [tor, MonoidHom.comp_apply, ι_one_ϑ, ι_two]

include hK hq in
theorem GoodFamily.exists_tor_of_far (hg : GoodFamily S) {A B : Su K p f 2}
    (hT : S.ι 0 A * S.ι 2 B ∈ torusSub S) :
    ∃ y w, S.ι 0 A * S.ι 2 B = tor S 0 y * tor S 2 w := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hc := torusSub_comm S (tor_mem_torusSub S 0 x₀) hT
  have hc2 := torusSub_comm S (tor_mem_torusSub S 2 x₀) hT
  have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K p f)) = 1 := by
    ext i
    fin_cases i <;> rfl
  have e1 : tor S 0 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 0 x₀)⁻¹ =
      S.ι 0 (conjDiag hK ![x₀ * x₀, 1] A) * S.ι 2 B := by
    have h := tor_conj_ι S 0 2 x₀ B
    rw [chi_zero_two] at h
    rw [show tor S 0 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 0 x₀)⁻¹ =
      (tor S 0 x₀ * S.ι 0 A * (tor S 0 x₀)⁻¹) * (tor S 0 x₀ * S.ι 2 B * (tor S 0 x₀)⁻¹) by group,
      tor_conj_self S 0 x₀ A, h, h11, conjDiag_one hK B]
  have e2 : tor S 2 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 2 x₀)⁻¹ =
      S.ι 0 A * S.ι 2 (conjDiag hK ![x₀ * x₀, 1] B) := by
    have h := tor_conj_ι S 2 0 x₀ A
    rw [chi_two_zero] at h
    rw [show tor S 2 x₀ * (S.ι 0 A * S.ι 2 B) * (tor S 2 x₀)⁻¹ =
      (tor S 2 x₀ * S.ι 0 A * (tor S 2 x₀)⁻¹) * (tor S 2 x₀ * S.ι 2 B * (tor S 2 x₀)⁻¹) by group,
      tor_conj_self S 2 x₀ B, h, h11, conjDiag_one hK A]
  have f1 : S.ι 0 (conjDiag hK ![x₀ * x₀, 1] A) * S.ι 2 B = S.ι 0 A * S.ι 2 B := by
    rw [← e1]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  have f2 : S.ι 0 A * S.ι 2 (conjDiag hK ![x₀ * x₀, 1] B) = S.ι 0 A * S.ι 2 B := by
    rw [← e2]
    exact mul_inv_eq_iff_eq_mul.mpr hc2
  have g1 : tor S 0 x₀ * S.ι 0 A = S.ι 0 A * tor S 0 x₀ := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [tor_conj_self S 0 x₀ A]
    exact mul_right_cancel f1
  have g2 : tor S 2 x₀ * S.ι 2 B = S.ι 2 B * tor S 2 x₀ := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [tor_conj_self S 2 x₀ B]
    exact mul_left_cancel f2
  obtain ⟨y, hy⟩ := hg.exists_tor_of_comm 0 hx₀ g1
  obtain ⟨w, hw⟩ := hg.exists_tor_of_comm 2 hx₀ g2
  exact ⟨y, w, by rw [hy, hw]⟩

end Inf

end CFSG.ClassicalInvolution.PhanB3
