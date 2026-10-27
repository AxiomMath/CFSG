module

public import CFSG.Holt.H78.Sec4FinalB2
import CFSG.Goldschmidt.Steps.G3MFSz8
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.Holt.H78


namespace IsNaturalSE

variable {Δ : Type*} {M : Subgroup (Equiv.Perm Δ)}

theorem exists_mulEquiv_sz (hM : IsNaturalSE M) (h29 : Nat.card M = 29120) :
    ∃ b : ℕ, 1 ≤ b ∧ Nonempty (M ≃* CFSG.Open.Sz b) := by
  obtain ⟨q, i, hB⟩ := hM
  have hcard : Nat.card (⊤ : Subgroup M) = 29120 := by rw [Subgroup.card_top, h29]
  rcases hB.model with ⟨-, f, hf, -, ⟨e⟩⟩ | ⟨-, b, hb, -, ⟨e⟩⟩ | ⟨-, f, hf, -, ⟨e⟩⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by omega)] at hcard
    have h4 : (2 ^ f) ^ 2 = 4 ^ f := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
      have hmod : 4 ^ f % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have hpos : 1 ≤ 4 ^ f := Nat.one_le_pow _ _ (by norm_num)
      rw [h4]
      omega
    have h := h3.mul_left (2 ^ f)
    rw [hcard] at h
    norm_num at h
  · exact ⟨b, hb, ⟨Subgroup.topEquiv.symm.trans e⟩⟩
  · exfalso
    have hc := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd
      (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv, hcard] at hc
    have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
    · norm_num at hc
    · have h8 : 8 ≤ 2 ^ f := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
      have h1 : 512 ≤ (2 ^ f) ^ 3 := by
        calc 512 = 8 ^ 3 := by norm_num
          _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h8 3
      have h2 : 63 ≤ (2 ^ f) ^ 2 - 1 := by
        have : 64 ≤ (2 ^ f) ^ 2 := by
          calc 64 = 8 ^ 2 := by norm_num
            _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h8 2
        omega
      have h3 : 513 ≤ (2 ^ f) ^ 3 + 1 := by omega
      have hbig : 512 * (63 * 513) ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
      have hsmall : 29120 * Nat.gcd 3 (2 ^ f + 1) ≤ 29120 * 3 := Nat.mul_le_mul_left _ hg
      omega

variable [Finite Δ]

theorem exists_sylow_commute (hM : IsNaturalSE M) {s : M} (hs : orderOf s = 2) :
    ∃ Q : Sylow 2 M, ∀ y ∈ (Q : Subgroup M), y * s = s * y := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  obtain ⟨δ, hδ, -⟩ := hM.existsUnique_fixed hs
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer δ
  have hJ : s ∈ longInvAt M Δ δ := ⟨⟨hs, hM.existsUnique_fixed hs⟩, hδ⟩
  have hZ := ((hA.mem_longInvAt_iff hQ).mp hJ).1
  exact ⟨Q, Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hZ).2⟩

end IsNaturalSE

theorem szEightTwoCoverConj : SzEightTwoCoverConj := by
  intro E _ _ Δ _ π hM h29 hZ hsq _ hperf a ha haK z hz
  have : Group.IsPerfect E := Group.isPerfect_def.mpr hperf
  obtain ⟨b, hb, ⟨e⟩⟩ := hM.exists_mulEquiv_sz h29
  obtain ⟨n, i, d, hA⟩ := hM.exists_isBenderAction
  have hf : Function.Surjective π.rangeRestrict := π.rangeRestrict_surjective
  have hkf : π.rangeRestrict.ker = π.ker := MonoidHom.ker_rangeRestrict π
  have hc : π.ker = Subgroup.center E := by
    refine le_antisymm hZ fun c hc => ?_
    have hfc : π.rangeRestrict c ∈ Subgroup.center π.range := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hf y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
    rw [hA.benderType.center_eq_bot, Subgroup.mem_bot] at hfc
    rw [← hkf]
    exact hfc
  have hzc : z ∈ Subgroup.center E := hc ▸ hz
  have hs : orderOf (π.rangeRestrict a) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => haK ?_
    · rw [← map_pow, sq, ha, map_one]
    · rw [← hkf]
      exact h1
  obtain ⟨Q, hQ⟩ := hM.exists_sylow_commute hs
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hf 2 Q
  have hcomm : ∀ x ∈ (T : Subgroup E), a * x * a⁻¹ * x⁻¹ ∈ Subgroup.center E := by
    intro x hx
    have hxQ : π.rangeRestrict x ∈ (Q : Subgroup π.range) := by
      rw [← hT, Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem _ hx
    rw [← hc, ← hkf, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← hQ _ hxQ]
    group
  let ρ : E →* CFSG.Open.Sz b := e.toMonoidHom.comp π.rangeRestrict
  have hρ : Function.Surjective ρ := e.surjective.comp hf
  have hkρ : ρ.ker = Subgroup.center E :=
    ((MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans hkf).trans hc
  have hZ2 : ∀ w ∈ Subgroup.center E, w ^ 2 = 1 := fun w hw => by
    rw [sq]
    exact hsq w (hc ▸ hw)
  obtain ⟨x, -, hx⟩ :=
    CFSG.Goldschmidt.MFSz8.exists_commutator_eq hb ρ hρ hkρ hZ2 T hcomm (hc ▸ haK) hzc
  refine ⟨x, ?_⟩
  rw [Subgroup.mem_center_iff.mp hzc a, ← hx]
  group

end CFSG.Holt.H78
