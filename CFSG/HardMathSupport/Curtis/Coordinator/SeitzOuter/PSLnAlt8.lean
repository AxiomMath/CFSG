module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnAlt8Blocks
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPlane

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Equiv Equiv.Perm CFSG.Open

@[expose] def altC1 : Perm (Fin 8) := cyc3 0 1 2

@[expose] def altC2 : Perm (Fin 8) := cyc3 3 4 5

theorem altC1_cube : altC1 * altC1 * altC1 = 1 := by decide +kernel

theorem altC2_cube : altC2 * altC2 * altC2 = 1 := by decide +kernel

theorem altC1_ne : altC1 ≠ 1 := by decide +kernel

theorem altC2_ne : altC2 ≠ 1 := by decide +kernel

theorem altC_comm : altC1 * altC2 = altC2 * altC1 := by decide +kernel

theorem isPGroup_zpowers_three {c : Perm (Fin 8)} (hc : c * c * c = 1) (hne : c ≠ 1) :
    IsPGroup 3 (Subgroup.zpowers c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : c ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact hc
  have hd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have ho : orderOf c = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, ho]
  norm_num

theorem isPGroup_altA0 :
    IsPGroup 3 (Subgroup.zpowers altC1 ⊔ Subgroup.zpowers altC2 : Subgroup (Perm (Fin 8))) := by
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_three altC1_cube altC1_ne)
    (isPGroup_zpowers_three altC2_cube altC2_ne) ?_
  have hmem : altC1 ∈ Subgroup.centralizer
      ((Subgroup.zpowers altC2 : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact ((Commute.zpow_right (altC_comm : Commute altC1 altC2) n).eq).symm
  rw [Subgroup.zpowers_le]
  exact Subgroup.centralizer_le_normalizer _ hmem

theorem card_perm_eight : Nat.card (Perm (Fin 8)) = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem factorization_perm_eight : (Nat.card (Perm (Fin 8))).factorization 3 = 2 := by
  rw [card_perm_eight]
  have h : (40320 : ℕ) = 3 ^ 2 * 4480 := by norm_num
  have h1 : (3 ^ 2 : ℕ).factorization 3 = 2 := by
    rw [Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have h2 : (4480 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h, Nat.factorization_mul_apply_of_coprime (by norm_num), h1, h2]

theorem alt8Init_comm : ∀ t ∈ alt8Init,
    altC1 * cycT t = cycT t * altC1 ∨ altC2 * cycT t = cycT t * altC2 := by decide +kernel

theorem cycT_mem_alt {t : Fin 8 × Fin 8 × Fin 8} (h1 : t.1 ≠ t.2.1) (h2 : t.2.1 ≠ t.2.2) :
    cycT t ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]
  simp [cycT, cyc3, Perm.sign_mul, Perm.sign_swap h1, Perm.sign_swap h2]

theorem alt8_planes {A : Subgroup (Perm (Fin 8))} (hc : Nat.card A = 9) :
    alternatingGroup (Fin 8) ≤ Subgroup.closure
      {x | x ∈ alternatingGroup (Fin 8) ∧ ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow 3 (Perm (Fin 8)) := Sylow.ofCard A (by rw [hc, factorization_perm_eight]; norm_num)
  obtain ⟨Q₀, hQ₀⟩ := isPGroup_altA0.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 8)) Q Q₀
  have key : ∀ c ∈ (Q₀ : Subgroup (Perm (Fin 8))), g⁻¹ * c * g ∈ A := by
    intro c hcQ
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hcQ
    obtain ⟨y, hy, rfl⟩ := hcQ
    have : g⁻¹ * (MulAut.conj g • y) * g = y := by
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  set H := Subgroup.closure
    {x | x ∈ alternatingGroup (Fin 8) ∧ ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x} with hH
  have hC1 : altC1 ∈ (Q₀ : Subgroup (Perm (Fin 8))) :=
    hQ₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hC2 : altC2 ∈ (Q₀ : Subgroup (Perm (Fin 8))) :=
    hQ₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  let H₁ : Subgroup (Perm (Fin 8)) := H.comap (MulAut.conj g⁻¹).toMonoidHom
  have hinit : ∀ t ∈ alt8Init, cycT t ∈ H₁ := by
    intro t ht
    have hd := alt8_distinct t (by simp [ht])
    have hx : cycT t ∈ alternatingGroup (Fin 8) := cycT_mem_alt hd.1 hd.2
    have hmem : g⁻¹ * cycT t * g ∈ H := by
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ hx g⁻¹
      · rcases alt8Init_comm t ht with hcm | hcm
        · refine ⟨g⁻¹ * altC1 * g, key _ hC1, ?_, ?_⟩
          · intro h1
            apply altC1_ne
            have := congrArg (fun z => g * z * g⁻¹) h1
            simpa [mul_assoc] using this
          · calc g⁻¹ * cycT t * g * (g⁻¹ * altC1 * g) = g⁻¹ * (cycT t * altC1) * g := by group
              _ = g⁻¹ * (altC1 * cycT t) * g := by rw [hcm]
              _ = g⁻¹ * altC1 * g * (g⁻¹ * cycT t * g) := by group
        · refine ⟨g⁻¹ * altC2 * g, key _ hC2, ?_, ?_⟩
          · intro h1
            apply altC2_ne
            have := congrArg (fun z => g * z * g⁻¹) h1
            simpa [mul_assoc] using this
          · calc g⁻¹ * cycT t * g * (g⁻¹ * altC2 * g) = g⁻¹ * (cycT t * altC2) * g := by group
              _ = g⁻¹ * (altC2 * cycT t) * g := by rw [hcm]
              _ = g⁻¹ * altC2 * g * (g⁻¹ * cycT t * g) := by group
    simpa [H₁, MulAut.conj_apply] using hmem
  have halt := alt8_le_of_blocks H₁ hinit
  intro y hy
  have hy' : g * y * g⁻¹ ∈ alternatingGroup (Fin 8) :=
    (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ hy g
  have h3 : g⁻¹ * (g * y * g⁻¹) * g ∈ H := by
    have := halt hy'
    simpa [H₁, MulAut.conj_apply] using this
  simpa [mul_assoc] using h3

theorem closure_cent_of_ambient {X P : Type*} [Group X] [Group P] (φ : X →* P)
    (hφ : Function.Injective φ) {A : Subgroup X}
    (h : φ.range ≤ Subgroup.closure
      {k | k ∈ φ.range ∧ ∃ b ∈ A.map φ, b ≠ 1 ∧ k * b = b * k}) :
    Subgroup.closure (centSet A) = ⊤ := by
  have h1 : φ.range ≤ (Subgroup.closure (centSet A)).map φ := by
    refine h.trans ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro k ⟨⟨x, rfl⟩, _, ⟨a, ha, rfl⟩, hb1, hkb⟩
    refine ⟨x, ⟨a, ha, fun h => hb1 (by rw [h, map_one]), hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hkb
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨w, hw, hwz⟩ := h1 ⟨z, rfl⟩
  rwa [← hφ hwz]

theorem planeCentGen_alt8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PlaneCentGen (alternatingGroup (Fin 8)) p := by
  intro A hA hAc
  have hcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup (α := Fin 8)]
    simp [Fintype.card_fin]
    decide
  by_cases hp3 : p = 3
  · subst hp3
    refine closure_cent_of_ambient (alternatingGroup (Fin 8)).subtype
      (alternatingGroup (Fin 8)).subtype_injective ?_
    rw [Subgroup.range_subtype]
    have hcA : Nat.card (A.map (alternatingGroup (Fin 8)).subtype) = 9 := by
      rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective, hAc]
      norm_num
    exact alt8_planes hcA
  · exfalso
    have h1 : p ^ 2 ∣ 20160 := hcard ▸ hAc ▸ Subgroup.card_subgroup_dvd_card A
    have h5 : p ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) h1
    have h6 : p ≤ 142 := by nlinarith
    have key : ∀ q : ℕ, q ≤ 142 → q.Prime → q ≠ 2 → q ≠ 3 → ¬ q ^ 2 ∣ 20160 := by decide +kernel
    exact key p h6 hp hp2 hp3 h1

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
