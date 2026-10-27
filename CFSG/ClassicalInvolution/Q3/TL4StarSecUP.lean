module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecPair
public import CFSG.ClassicalInvolution.Q3.Q3AM289Z4
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU02

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Q3.Q3PP (F9 two_ne_zero_F9 center_su3_eq_bot)
open CFSG.ClassicalInvolution.Q3.Q3AM (wElt suMat_wElt)

section Elements

noncomputable abbrev embU (c : Fin 3) : Su F9 3 1 2 →* Su F9 3 1 3 :=
  embSUid (unitaryInvolution F9 3 1) c

theorem suMat_embU (c : Fin 3) (A : Su F9 3 1 2) : suMat (embU c A) = embPair c (suMat A) := rfl

theorem wElt_mul_self : wElt * wElt = negOneSU F9 3 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_wElt, suMat_negOneSU]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {i : F9} (hi : i * i = -1)

include hi in
theorem up_facts :
    (∀ A : Su F9 3 1 2, embU 2 (negOneSU F9 3 1) * embU 2 A = embU 2 A * embU 2 (negOneSU F9 3 1)) ∧
    embU 2 (negOneSU F9 3 1) * embU 2 (negOneSU F9 3 1) = 1 ∧
    embU 0 (Q3T8.Asc77.jjSU hi) * embU 0 (Q3T8.Asc77.jjSU hi) = embU 0 (negOneSU F9 3 1) ∧
    embU 0 wElt * embU 0 wElt = embU 0 (negOneSU F9 3 1) ∧
    embU 0 (Q3T8.Asc77.jjSU hi) * embU 0 wElt * embU 0 (Q3T8.Asc77.jjSU hi) = embU 0 wElt ∧
    embU 0 (Q3T8.Asc77.jjSU hi) * embU 2 (negOneSU F9 3 1) =
      embU 2 (negOneSU F9 3 1) * embU 0 (Q3T8.Asc77.jjSU hi) ∧
    embU 0 wElt * embU 2 (negOneSU F9 3 1) =
      embU 0 (negOneSU F9 3 1) * embU 2 (negOneSU F9 3 1) * embU 0 wElt ∧
    embU 0 (negOneSU F9 3 1) ≠ 1 ∧
    embU 2 wElt * embU 0 (negOneSU F9 3 1) ≠ embU 0 (negOneSU F9 3 1) * embU 2 wElt := by
  have h2 := two_ne_zero_F9
  refine ⟨fun A => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_negOneSU, neg_one_mul, mul_neg_one]
  · rw [← map_mul, negOneSU_mul_self, map_one]
  · rw [← map_mul, Q3T8.Asc77.jjSU_mul_self]
  · rw [← map_mul, wElt_mul_self]
  · rw [← map_mul, ← map_mul]
    congr 1
    apply suMat_injective
    rw [suMat_mul, suMat_mul, Q3T8.Asc77.suMat_jjSU, suMat_wElt]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Q3T8.Asc77.jjMat, Matrix.mul_apply, Fin.sum_univ_two, hi]
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_embU, suMat_embU, Q3T8.Asc77.suMat_jjSU, suMat_negOneSU]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [embPair, Q3T8.Asc77.jjMat, Matrix.mul_apply, Fin.sum_univ_three]
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_mul, suMat_embU, suMat_embU, suMat_embU, suMat_wElt,
      suMat_negOneSU]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [embPair, Matrix.mul_apply, Fin.sum_univ_three]
  · intro h
    have h1 := congrFun (congrFun (congrArg suMat h) 1) 1
    rw [suMat_embU, suMat_negOneSU, suMat_one] at h1
    simp [embPair] at h1
    apply h2
    linear_combination -h1
  · intro h
    have h1 := congrFun (congrFun (congrArg suMat h) 0) 1
    rw [suMat_mul, suMat_mul, suMat_embU, suMat_embU, suMat_wElt, suMat_negOneSU] at h1
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three] at h1
    apply h2
    linear_combination -h1

end Elements

section Pair

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem starNbr_of_unitaryPair {G : Type} [Group G] {𝓕 : Set (Subgroup G)} {ψ : G →* X}
    (hker : ψ.ker ≤ Subgroup.center G) (hfund : ∀ L ∈ Φ, ∃ R ∈ 𝓕, IsSylow2In L (R.map ψ))
    (hcls : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : X, R'.map ψ = conjSub g (R.map ψ))
    {W R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ 𝓕) (hR₂ : R₂ ∈ 𝓕)
    (hW : Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂) (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨θ, c, -, hθk, hcase⟩ := hW
  obtain ⟨hA, hB⟩ : ((B12 (GaloisField 3 2) 3 1).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈ 𝓕 ∧
      ((B23 (GaloisField 3 2) 3 1).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈ 𝓕 := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ hR₁, h2 ▸ hR₂⟩
    · exact ⟨h1 ▸ hR₂, h2 ▸ hR₁⟩
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hθk.trans center_su3_eq_bot.le
  obtain ⟨i, hi⟩ := Q3T8.Asc77.s3_exists_sq_neg_one_F9
  obtain ⟨hac₀, ha₀2, hu₀2, hx₀2, hux₀, hua₀, hxa₀, hd₀1, hyd₀⟩ := up_facts hi
  set κ : Su F9 3 1 3 →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom with hκ
  have hκinj : Function.Injective κ := hθinj.comp (MulAut.conj c⁻¹).injective
  have hmemA : ∀ A : Su F9 3 1 2, κ (embU 2 A) ∈
      ((B12 (GaloisField 3 2) 3 1).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    fun A => ⟨_, ⟨embU 2 A, ⟨A, rfl⟩, rfl⟩, rfl⟩
  have hmemB : ∀ A : Su F9 3 1 2, κ (embU 0 A) ∈
      ((B23 (GaloisField 3 2) 3 1).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    fun A => ⟨_, ⟨embU 0 A, ⟨A, rfl⟩, rfl⟩, rfl⟩
  have hdZ : κ (embU 0 (negOneSU F9 3 1)) ∉ Subgroup.center G := by
    intro hc
    apply hyd₀
    apply hκinj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hc _)
  have hord : ∀ y : Su F9 3 1 3, y * y = embU 0 (negOneSU F9 3 1) → orderOf (κ y) = 4 := by
    intro y hy
    rw [orderOf_injective κ hκinj]
    have h1 : ¬ y ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hy]; exact hd₀1
    have h2 : y ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two y, hy, pow_two, ← map_mul,
        negOneSU_mul_self, map_one]
    simpa using orderOf_eq_prime_pow h1 h2
  have hxu₀ : embU 0 wElt * embU 0 (Q3T8.Asc77.jjSU hi) * (embU 0 wElt)⁻¹ =
      (embU 0 (Q3T8.Asc77.jjSU hi))⁻¹ := by
    calc embU 0 wElt * embU 0 (Q3T8.Asc77.jjSU hi) * (embU 0 wElt)⁻¹ =
        (embU 0 (Q3T8.Asc77.jjSU hi))⁻¹ * (embU 0 (Q3T8.Asc77.jjSU hi) * embU 0 wElt *
          embU 0 (Q3T8.Asc77.jjSU hi)) * (embU 0 wElt)⁻¹ := by group
      _ = (embU 0 (Q3T8.Asc77.jjSU hi))⁻¹ := by rw [hux₀]; group
  have hainv : (embU 2 (negOneSU F9 3 1))⁻¹ = embU 2 (negOneSU F9 3 1) :=
    inv_eq_of_mul_eq_one_right ha₀2
  have hcomm₀ : embU 0 wElt * embU 2 (negOneSU F9 3 1) * (embU 0 wElt)⁻¹ *
      (embU 2 (negOneSU F9 3 1))⁻¹ = embU 0 (negOneSU F9 3 1) := by
    rw [hxa₀, hainv]
    calc embU 0 (negOneSU F9 3 1) * embU 2 (negOneSU F9 3 1) * embU 0 wElt *
          (embU 0 wElt)⁻¹ * embU 2 (negOneSU F9 3 1) =
        embU 0 (negOneSU F9 3 1) * (embU 2 (negOneSU F9 3 1) * embU 2 (negOneSU F9 3 1)) := by
          group
      _ = embU 0 (negOneSU F9 3 1) := by rw [ha₀2, mul_one (embU 0 (negOneSU F9 3 1))]
  refine starNbr_of_pair (a := κ (embU 2 (negOneSU F9 3 1))) (u := κ (embU 0 (Q3T8.Asc77.jjSU hi)))
    (x := κ (embU 0 wElt)) hker hfund hcls hA hB (hmemA _) ?_ ?_ ?_ (hmemB _) (hmemB _)
    (hord _ hu₀2) (hord _ hx₀2) ?_ ?_ ?_ ?_ hR htr
  ·
    rintro _ ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    show κ (embU 2 (negOneSU F9 3 1)) * κ (embU 2 A) = κ (embU 2 A) * κ (embU 2 (negOneSU F9 3 1))
    have h := congrArg κ (hac₀ A)
    simpa only [map_mul] using h
  · rw [← map_mul κ, ha₀2, map_one]
  ·
    intro hc
    have h1 : κ (embU 0 wElt) * κ (embU 2 (negOneSU F9 3 1)) =
        κ (embU 2 (negOneSU F9 3 1)) * κ (embU 0 wElt) := Subgroup.mem_center_iff.mp hc _
    have h2 : κ (embU 0 wElt) * κ (embU 2 (negOneSU F9 3 1)) =
        κ (embU 0 (negOneSU F9 3 1)) * κ (embU 2 (negOneSU F9 3 1)) * κ (embU 0 wElt) := by
      have h := congrArg κ hxa₀
      simpa only [map_mul] using h
    have h3 : κ (embU 0 (negOneSU F9 3 1)) = 1 := by
      have h4 : κ (embU 0 (negOneSU F9 3 1)) *
          (κ (embU 2 (negOneSU F9 3 1)) * κ (embU 0 wElt)) =
            1 * (κ (embU 2 (negOneSU F9 3 1)) * κ (embU 0 wElt)) := by
        rw [one_mul, ← mul_assoc, ← h2, h1]
      exact mul_right_cancel h4
    exact hd₀1 (hκinj (h3.trans (map_one κ).symm))
  · rw [← map_mul κ, hu₀2]
    exact hdZ
  · have h := congrArg κ hxu₀
    simpa only [map_mul, map_inv] using h
  · have h := congrArg κ hua₀
    simpa only [map_mul] using h
  · have h := congrArg κ hcomm₀
    simp only [map_mul, map_inv] at h
    rw [h]
    exact hdZ

end Pair

end CFSG.ClassicalInvolution.Q3.TL4
