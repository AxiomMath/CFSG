module

public import CFSG.ClassicalInvolution.Phan.PhanD5Indep

public section

namespace CFSG.ClassicalInvolution.PhanD4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] (S : PhanFamilyD4 K p f G)

@[expose] noncomputable def torusSub : Subgroup G := (mTor S).range

theorem mTor_mem_torusSub (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    mTor S t ∈ torusSub S :=
  ⟨t, rfl⟩

theorem tor_mem_torusSub (i : Fin 4) (x : normOne (unitaryInvolution K p f)) :
    tor S i x ∈ torusSub S := by
  rw [← mTor_mulSingle]
  exact mTor_mem_torusSub S _

theorem torusSub_comm {a b : G} (ha : a ∈ torusSub S) (hb : b ∈ torusSub S) : a * b = b * a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

variable {S}

section Inf

theorem GoodFamily.exists_tor_of_comm (hg : GoodFamily S) (i : Fin 4)
    {x₀ : normOne (unitaryInvolution K p f)} (hx₀ : x₀ * x₀ ≠ 1) {A : Su K p f 2}
    (h : tor S i x₀ * S.ι i A = S.ι i A * tor S i x₀) :
    ∃ y, S.ι i A = tor S i y := by
  have h' : S.ι i (torusTwo (unitaryInvolution K p f) x₀ * A) =
      S.ι i (A * torusTwo (unitaryInvolution K p f) x₀) := by
    rw [map_mul, map_mul]
    exact h
  obtain ⟨y, hy⟩ := mem_range_torusTwo_of_commute hx₀ (hg.inj i h').symm
  exact ⟨y, by rw [← hy]; rfl⟩

variable (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f)

include hK hq in
theorem GoodFamily.exists_tor_of_mem_range (hg : GoodFamily S) (i : Fin 4) {A : Su K p f 2}
    (hT : S.ι i A ∈ torusSub S) : ∃ y, S.ι i A = tor S i y := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  exact hg.exists_tor_of_comm i hx₀ ((torusSub_comm S (tor_mem_torusSub S i x₀) hT))

include hK hq in
theorem GoodFamily.exists_tor_of_theta (hg : GoodFamily S) (e : Fin 3) {B : Su K p f 3}
    (hT : S.θ e B ∈ torusSub S) :
    ∃ y w, S.θ e B = tor S (edgeSrc e) y * tor S (edgeTgt e) w := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hc := torusSub_comm S (tor_mem_torusSub S (edgeSrc e) x₀) hT
  have hc' : S.θ e (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) x₀) *
      B) = S.θ e (B * embSUid (unitaryInvolution K p f) 2
        (torusTwo (unitaryInvolution K p f) x₀)) := by
    rw [map_mul, map_mul]
    have := hc
    simp only [tor, MonoidHom.comp_apply, ι_src] at this
    exact this
  obtain ⟨y, w, hyw⟩ := exists_embSUid_torus_of_commute hx₀ (hg.θ_injective hK e hc').symm
  refine ⟨y, w, ?_⟩
  rw [hyw, map_mul]
  simp only [tor, MonoidHom.comp_apply, ι_src, ι_tgt]

include hK hq in
theorem GoodFamily.exists_tor_of_pair (hg : GoodFamily S) {a b : Fin 4} (hab : a ≠ b)
    (h1 : ¬ edgeD 4 a b) (h2 : ¬ edgeD 4 b a) {A B : Su K p f 2}
    (hT : S.ι a A * S.ι b B ∈ torusSub S) :
    ∃ y w, S.ι a A * S.ι b B = tor S a y * tor S b w := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hc := torusSub_comm S (tor_mem_torusSub S a x₀) hT
  have hc2 := torusSub_comm S (tor_mem_torusSub S b x₀) hT
  have e1 : tor S a x₀ * (S.ι a A * S.ι b B) * (tor S a x₀)⁻¹ =
      S.ι a (conjDiag hK ![x₀ * x₀, 1] A) * S.ι b B := by
    have h := tor_conj_ι hK S a b x₀ B
    rw [chi_far hab h1 h2] at h
    rw [show tor S a x₀ * (S.ι a A * S.ι b B) * (tor S a x₀)⁻¹ =
      (tor S a x₀ * S.ι a A * (tor S a x₀)⁻¹) * (tor S a x₀ * S.ι b B * (tor S a x₀)⁻¹) by group,
      tor_conj_ι hK S a a x₀ A, chi_self, h]
    congr 2
    have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K p f)) = 1 := by
      ext i
      fin_cases i <;> rfl
    rw [h11, conjDiag_one hK B]
  have e2 : tor S b x₀ * (S.ι a A * S.ι b B) * (tor S b x₀)⁻¹ =
      S.ι a A * S.ι b (conjDiag hK ![x₀ * x₀, 1] B) := by
    have h := tor_conj_ι hK S b a x₀ A
    rw [chi_far hab.symm h2 h1] at h
    rw [show tor S b x₀ * (S.ι a A * S.ι b B) * (tor S b x₀)⁻¹ =
      (tor S b x₀ * S.ι a A * (tor S b x₀)⁻¹) * (tor S b x₀ * S.ι b B * (tor S b x₀)⁻¹) by group,
      tor_conj_ι hK S b b x₀ B, chi_self, h]
    congr 2
    have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K p f)) = 1 := by
      ext i
      fin_cases i <;> rfl
    rw [h11, conjDiag_one hK A]
  have f1 : S.ι a (conjDiag hK ![x₀ * x₀, 1] A) * S.ι b B = S.ι a A * S.ι b B := by
    rw [← e1]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  have f2 : S.ι a A * S.ι b (conjDiag hK ![x₀ * x₀, 1] B) = S.ι a A * S.ι b B := by
    rw [← e2]
    exact mul_inv_eq_iff_eq_mul.mpr hc2
  have g1 : tor S a x₀ * S.ι a A = S.ι a A * tor S a x₀ := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [tor_conj_ι hK S a a x₀ A, chi_self]
    exact mul_right_cancel f1
  have g2 : tor S b x₀ * S.ι b B = S.ι b B * tor S b x₀ := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [tor_conj_ι hK S b b x₀ B, chi_self]
    exact mul_left_cancel f2
  obtain ⟨y, hy⟩ := hg.exists_tor_of_comm a hx₀ g1
  obtain ⟨w, hw⟩ := hg.exists_tor_of_comm b hx₀ g2
  exact ⟨y, w, by rw [hy, hw]⟩

end Inf

end CFSG.ClassicalInvolution.PhanD4
