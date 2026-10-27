module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Ext
public import TauCeti.GroupTheory.Commutator

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm

theorem sec4S47_exists_index_two {X : Type*} [Group X] [Finite X]
    (ρ₀ : X →* Perm (Option (Fin 7)))
    (H : Subgroup X) [H.Normal] (hH : H ≤ ρ₀.ker) {t : X} (ht : t ∉ H) (htk : ρ₀ t = 1)
    (ht2 : t * t = 1) (hker : ∀ x : X, ρ₀ x = 1 → x ∈ H ∨ x * t ∈ H)
    (hcent : ∀ x : X, x * t * x⁻¹ * t⁻¹ ∈ H)
    (hA : alternatingGroup (Option (Fin 7)) ≤ ρ₀.range)
    (hlift : ∀ x : X, ρ₀ x none = none → ρ₀ x * ρ₀ x = 1 →
      ∃ y : X, ρ₀ y = ρ₀ x ∧ y * y ∈ H) :
    ∃ M₀ : Subgroup X, M₀.index = 2 ∧ t ∉ M₀ := by
  let q : X →* X ⧸ H := QuotientGroup.mk' H
  let ρ : X ⧸ H →* Perm (Option (Fin 7)) := QuotientGroup.lift H ρ₀ hH
  have hρq : ∀ x : X, ρ (q x) = ρ₀ x := fun x => QuotientGroup.lift_mk' H (φ := ρ₀) hH x
  have hτne : q t ≠ 1 := fun h => ht ((QuotientGroup.eq_one_iff t).mp h)
  have hτ2 : q t * q t = 1 := by rw [← map_mul, ht2, map_one]
  have hτcent : q t ∈ Subgroup.center (X ⧸ H) := by
    rw [Subgroup.mem_center_iff]
    intro n
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H n
    exact (QuotientGroup.commute_mk_iff.mpr (hcent x)).eq
  have hker_cases : ∀ n : X ⧸ H, ρ n = 1 → n = 1 ∨ n = q t := by
    intro n hn
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H n
    have hx : ρ₀ x = 1 := by rw [← hρq x]; exact hn
    rcases hker x hx with hxH | hxtH
    · exact Or.inl ((QuotientGroup.eq_one_iff x).mpr hxH)
    · refine Or.inr ?_
      have h1 : q x * q t = 1 := by
        rw [← map_mul]
        exact (QuotientGroup.eq_one_iff (x * t)).mpr hxtH
      calc q x = q x * 1 := (mul_one _).symm
        _ = q x * (q t * q t) := by rw [hτ2]
        _ = (q x * q t) * q t := by rw [mul_assoc]
        _ = 1 * q t := by rw [h1]
        _ = q t := one_mul _
  have hCρ : ρ.ker ≤ Subgroup.center (X ⧸ H) := by
    intro n hn
    rcases hker_cases n ((MonoidHom.mem_ker).mp hn) with h | h
    · rw [h]; exact (Subgroup.center (X ⧸ H)).one_mem
    · rw [h]; exact hτcent
  have h2ρ : ∀ k ∈ ρ.ker, k ^ 2 = 1 := by
    intro k hk
    rcases hker_cases k ((MonoidHom.mem_ker).mp hk) with h | h
    · rw [h, one_pow]
    · rw [h, pow_two]; exact hτ2
  have hrange : ρ.range = ρ₀.range := by
    ext b
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H n
      exact ⟨x, (hρq x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨q x, hρq x⟩
  have hAρ : alternatingGroup (Option (Fin 7)) ≤ ρ.range := by
    rw [hrange]; exact hA
  have hliftρ : ∀ b ∈ ρ.range, b none = none → b ^ 2 = 1 →
      ∃ y : X ⧸ H, ρ y = b ∧ y ^ 2 = 1 := by
    intro b hb hbnone hb2
    rw [hrange] at hb
    obtain ⟨x, rfl⟩ := hb
    have hx2 : ρ₀ x * ρ₀ x = 1 := by rwa [pow_two] at hb2
    obtain ⟨y, hy, hyH⟩ := hlift x hbnone hx2
    refine ⟨q y, ?_, ?_⟩
    · rw [hρq y]; exact hy
    · rw [pow_two, ← map_mul]
      exact (QuotientGroup.eq_one_iff (y * y)).mpr hyH
  obtain ⟨K, hKinf, hKsup⟩ := sec4S47_compl ρ hCρ h2ρ hAρ hliftρ
  have hτρker : q t ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hρq t, htk]
  have hqtK : q t ∉ K := by
    intro hK
    have hmem : q t ∈ K ⊓ ρ.ker := ⟨hK, hτρker⟩
    rw [hKinf] at hmem
    exact hτne (Subgroup.mem_bot.mp hmem)
  have hKindex : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨q t, hqtK, fun b => ?_⟩
    have hb : b ∈ K ⊔ ρ.ker := by rw [hKsup]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hb
    obtain ⟨k, hk, c, hc, hkc⟩ := hb
    rcases hker_cases c ((MonoidHom.mem_ker).mp hc) with hc1 | hcqt
    · right
      rw [← hkc, hc1, mul_one]
      exact hk
    · left
      rw [← hkc, hcqt, mul_assoc, hτ2, mul_one]
      exact hk
  refine ⟨K.comap q, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective (H := K) (f := q) (QuotientGroup.mk'_surjective H)]
    exact hKindex
  · intro htM
    exact hqtK (Subgroup.mem_comap.mp htM)

end CFSG.OddStandard.SmallF3.Omega
