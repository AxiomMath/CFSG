module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

universe u

variable {G : Type u} [Group G]

section Basics

theorem odd_card_N [Finite G] (t : G) : Odd (Nat.card (N t)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))

theorem card_Z (t : G) (ht : orderOf t = 2) : Nat.card (Z t) = 2 := by
  rw [Nat.card_zpowers, tInC, Subgroup.orderOf_mk, ht]

theorem Z_le_centralizer (t : G) (X : Set (C t)) : Z t ≤ Subgroup.centralizer X := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.center_le_centralizer X (tInC_central t)

theorem N_inf_Z [Finite G] (t : G) (ht : orderOf t = 2) {D : Subgroup (C t)} :
    (D ⊓ N t) ⊓ Z t = ⊥ := by
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [card_Z t ht, Nat.coprime_two_right]
  exact Odd.of_dvd_nat (odd_card_N t) (Subgroup.card_dvd_of_le inf_le_right)

end Basics

section TwoParts

variable [Finite G]

theorem factorization_two_card_eq {n : ℕ} (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) : (Nat.card G).factorization 2 = n := by
  have hS0 : Nat.card S0 = 2 ^ n := by
    rw [← Nat.card_congr f0.toEquiv, card n (by omega)]
  have hcop := S0.card_coprime_index
  have hidx : ¬ 2 ∣ (S0 : Subgroup G).index := by
    intro h
    have h1 : 2 ∣ Nat.card S0 := by rw [hS0]; exact dvd_pow_self 2 (by omega)
    have := Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h hcop)
    norm_num at this
  have hidx0 : (S0 : Subgroup G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.card_mul_index (S0 : Subgroup G), Nat.factorization_mul (by rw [hS0]; positivity)
    hidx0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  change (Nat.card S0).factorization 2 = n
  rw [hS0, Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self, smul_eq_mul,
    mul_one]

theorem factorization_two_card_le {n : ℕ} (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) (t : G) (D : Subgroup (C t)) :
    (Nat.card D).factorization 2 ≤ n := by
  have hdvd : Nat.card D ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card D).trans (Subgroup.card_subgroup_dvd_card (C t))
  have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvd 2
  rwa [factorization_two_card_eq hn S0 f0] at h

theorem factorization_two_card_SL2 (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)).factorization 2 =
      (Nat.card F ^ 2 - 1).factorization 2 := by
  rw [CFSG.GorensteinWalter.sl2_card_formula]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hq2 : Nat.card F ^ 2 - 1 ≠ 0 := by
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq
    omega
  rw [Nat.factorization_mul Nat.card_pos.ne' hq2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => by
      rw [← even_iff_two_dvd] at h
      exact (Nat.not_even_iff_odd.mpr hodd) h), zero_add]

end TwoParts

section Dichotomy

variable [Finite G]

theorem kappa_centralizer_eq_bot_or_le (t : G)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    {ℓ : ℕ} [Fact ℓ.Prime] (P : Sylow ℓ (N t)) {D : Subgroup (C t)}
    (hD : D = Subgroup.centralizer
      (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) : Set (C t))) :
    D.map (kappa t) = ⊥ ∨ CFSG.generalizedFitting (Gamma t) ≤ D.map (kappa t) := by
  have hFr := Sylow.normalizer_sup_eq_top (N := N t) P
  have hBsurj : ∀ γ : Gamma t, ∃ b ∈ Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) : Set (C t)),
      kappa t b = γ := by
    intro γ
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (NZ t) γ
    have hc : c ∈ Subgroup.normalizer ((((P : Subgroup (N t)).map (N t).subtype :
        Subgroup (C t))) : Set (C t)) ⊔ N t := by
      rw [hFr]
      exact Subgroup.mem_top c
    obtain ⟨b, hb, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
    refine ⟨b, hb, ?_⟩
    have hm1 : kappa t m = 1 := (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_sup_left hm)
    change kappa t b = kappa t (b * m)
    rw [map_mul, hm1, mul_one]
  have hDnorm : ∀ b ∈ Subgroup.normalizer ((((P : Subgroup (N t)).map (N t).subtype :
      Subgroup (C t))) : Set (C t)), ∀ d ∈ D, b * d * b⁻¹ ∈ D := by
    intro b hb d hd
    rw [hD, Subgroup.mem_centralizer_iff] at hd ⊢
    intro y hy
    have hy' : b⁻¹ * y * b ∈ ((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) y).mp hy
      simpa using h1
    have h2 := hd _ hy'
    calc y * (b * d * b⁻¹) = b * ((b⁻¹ * y * b) * d) * b⁻¹ := by group
      _ = b * (d * (b⁻¹ * y * b)) * b⁻¹ := by rw [h2]
      _ = b * d * b⁻¹ * y := by group
  have hUnorm : (D.map (kappa t)).Normal := by
    constructor
    rintro _ ⟨d, hd, rfl⟩ γ
    obtain ⟨b, hb, rfl⟩ := hBsurj γ
    exact ⟨b * d * b⁻¹, hDnorm b hb d hd, by simp only [map_mul, map_inv]⟩
  have hLnorm := (CFSG.LocalCores.generalized_fitting_characteristic (G := Gamma t)).2
  have hinf : ((D.map (kappa t) ⊓ CFSG.generalizedFitting (Gamma t)).subgroupOf
      (CFSG.generalizedFitting (Gamma t))).Normal :=
    (Subgroup.normal_inf_normal _ _).subgroupOf _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.map (kappa t) ⊓
      CFSG.generalizedFitting (Gamma t)).subgroupOf (CFSG.generalizedFitting (Gamma t))) with h | h
  · left
    have hbot : D.map (kappa t) ⊓ CFSG.generalizedFitting (Gamma t) = ⊥ :=
      (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
    have hcomm : ⁅D.map (kappa t), CFSG.generalizedFitting (Gamma t)⁆ = ⊥ :=
      le_bot_iff.mp (hbot ▸ Subgroup.commutator_le_inf _ _)
    rw [← le_bot_iff, ← hcentral]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  · right
    exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left

theorem centralizer_eq_sup_of_le_NZ (t : G) (ht : orderOf t = 2) {D : Subgroup (C t)}
    (hZD : Z t ≤ D) (hDNZ : D ≤ NZ t) :
    D = (D ⊓ N t) ⊔ Z t ∧ (D ⊓ N t) ⊓ Z t = ⊥ ∧ (∀ a ∈ D ⊓ N t, ∀ b ∈ Z t, Commute a b) ∧
      2 ^ (Nat.card D).factorization 2 = 2 := by
  have hdecomp : ∀ d ∈ D, ∃ a ∈ D ⊓ N t, ∃ z ∈ Z t, a * z = d := by
    intro d hd
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hDNZ hd)
    refine ⟨a, ⟨?_, ha⟩, z, hz, rfl⟩
    have h := D.mul_mem hd (D.inv_mem (hZD hz))
    rwa [mul_inv_cancel_right] at h
  have hsup : D = (D ⊓ N t) ⊔ Z t := by
    apply le_antisymm
    · intro d hd
      obtain ⟨a, ha, z, hz, rfl⟩ := hdecomp d hd
      exact Subgroup.mul_mem_sup ha hz
    · exact sup_le inf_le_left hZD
  have hcomm : ∀ a ∈ D ⊓ N t, ∀ b ∈ Z t, Commute a b := fun a _ b hb =>
    Subgroup.mem_centralizer_iff.mp (Z_le_centralizer t Set.univ hb) a (Set.mem_univ a)
  have hbot := N_inf_Z t ht (D := D)
  refine ⟨hsup, hbot, hcomm, ?_⟩
  have hcard : Nat.card D = Nat.card (D ⊓ N t : Subgroup (C t)) * 2 := by
    rw [← card_Z t ht, ← Nat.card_prod]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨(x.1 : C t) * x.2, D.mul_mem x.1.2.1 (hZD x.2.2)⟩)
      ⟨?_, ?_⟩
    · rintro ⟨⟨a, ha⟩, ⟨z, hz⟩⟩ ⟨⟨a', ha'⟩, ⟨z', hz'⟩⟩ h
      have h1 : a * z = a' * z' := congrArg Subtype.val h
      have h2 : a'⁻¹ * a = z' * z⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * z) * z⁻¹ := by group
          _ = a'⁻¹ * (a' * z') * z⁻¹ := by rw [h1]
          _ = z' * z⁻¹ := by group
      have h3 : a'⁻¹ * a ∈ (D ⊓ N t) ⊓ Z t :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha, h2 ▸ Subgroup.mul_mem _ hz'
          (Subgroup.inv_mem _ hz)⟩
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
      subst h3
      have h4 : z = z' := mul_left_cancel h1
      subst h4
      rfl
    · rintro ⟨d, hd⟩
      obtain ⟨a, ha, z, hz, rfl⟩ := hdecomp d hd
      exact ⟨⟨⟨a, ha⟩, ⟨z, hz⟩⟩, rfl⟩
  have hodd : Odd (Nat.card (D ⊓ N t : Subgroup (C t))) :=
    Odd.of_dvd_nat (odd_card_N t) (Subgroup.card_dvd_of_le inf_le_right)
  rw [hcard, Nat.factorization_mul (Nat.pos_of_ne_zero (by
      intro h; rw [h] at hodd; exact (Nat.not_odd_zero hodd))).ne' (by norm_num),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun h => by
      rw [← even_iff_two_dvd] at h
      exact (Nat.not_even_iff_odd.mpr hodd) h), zero_add, Nat.prime_two.factorization_self,
    pow_one]

omit [Finite G] in
theorem coverage_of_le_kappa (t : G) {D : Subgroup (C t)} (hZD : Z t ≤ D)
    (hLU : CFSG.generalizedFitting (Gamma t) ≤ D.map (kappa t)) :
    (D ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact inf_le_right
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := hLU (Subgroup.mem_comap.mp hx)
    have hker : (nu t d)⁻¹ * x ∈ (barKappa t).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, barKappa_nu]
      change (kappa t d)⁻¹ * barKappa t x = 1
      rw [hdx, inv_mul_cancel]
    rw [barKappa_kernel] at hker
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hker
    have hxeq : x = nu t (d * tInC t ^ j) := by
      rw [map_mul, map_zpow, hj]
      group
    have hmem : d * tInC t ^ j ∈ D := D.mul_mem hd (D.zpow_mem (hZD (Subgroup.mem_zpowers _)) j)
    refine ⟨d * tInC t ^ j, ⟨hmem, ?_⟩, hxeq.symm⟩
    show nu t (d * tInC t ^ j) ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    rw [← hxeq]
    exact hx

end Dichotomy

end CFSG.Semidihedral.Local
