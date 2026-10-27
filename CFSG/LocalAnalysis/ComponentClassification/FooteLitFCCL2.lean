module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCBase
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Field

public section

namespace CFSG.ComponentClassification.FooteLit.FCC

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem eq_bot_of_odd_normal_psl2 {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (N : Subgroup (PSL2 K)) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_cases h3 : Nat.card K = 3
  · have h12 : Nat.card (PSL2 K) = 12 := by
      rw [psl2_card_formula _ hK, h3]
      norm_num
    have hd : Nat.card N ∣ 3 * 4 := by
      have := Subgroup.card_subgroup_dvd_card N
      rwa [h12] at this
    have hcop : Nat.Coprime (Nat.card N) 4 := (Nat.coprime_two_right.mpr hodd).pow_right 2
    have hd3 : Nat.card N ∣ 3 := hcop.dvd_of_dvd_mul_right hd
    have hP3 : IsPGroup 3 N := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    exact normal_pSubgroup_eq_bot_of_psl2_odd K hK 3 Nat.prime_three ⟨1, rfl⟩ N hN hP3
  · have h4 : 4 ≤ Nat.card K := by
      obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hK
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases hpodd with ⟨m, hm⟩
        omega
      have h3' : 3 ≤ Nat.card K := by
        rw [hc]
        calc 3 ≤ p := hp3
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
      have hne : Nat.card K ≠ 4 := by
        intro h4
        rw [h4] at hc
        have : 2 ∣ p ^ n := ⟨2, by omega⟩
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
        rcases hpodd with ⟨m, hm⟩
        omega
      omega
    have hsimple : IsSimpleGroup (PSL2 K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      exact Nat.not_even_iff_odd.mpr hodd (even_psl2_card hK)

theorem exists_commuting_involutions_psl2 {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (N : Subgroup (PSL2 K)) (hN : N.Normal) (hN1 : N ≠ ⊥) :
    ∃ a ∈ N, ∃ b ∈ N, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card N := by
    by_contra h
    exact hN1 (eq_bot_of_odd_normal_psl2 hK N hN (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)))
  obtain ⟨⟨t, htN⟩, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [Subgroup.orderOf_mk] at ht
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht, sq] at h1
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htp : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := htp.exists_le_sylow
  have htS : t ∈ (S : Subgroup (PSL2 K)) := hS (mem_zpowers t)
  obtain ⟨m, hm, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 K)) hK S
  have heven : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  have hn2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hρt2 : ρ ⟨t, htS⟩ * ρ ⟨t, htS⟩ = 1 := by
    rw [← map_mul, ← map_one ρ]
    congr 1
    exact Subtype.ext htt
  have hρt1 : ρ ⟨t, htS⟩ ≠ 1 := by
    intro h
    rw [← map_one ρ] at h
    exact ht1 (congrArg Subtype.val (ρ.injective h))
  obtain ⟨u', hu'2, hu'1, hu't, hu'c⟩ :=
    dihedral_exists_commuting_involution heven hn2 _ hρt2 hρt1
  have huu : ((ρ.symm u' : S) : PSL2 K) * ((ρ.symm u' : S) : PSL2 K) = 1 := by
    have h1 : ρ.symm u' * ρ.symm u' = 1 := by rw [← map_mul, hu'2, map_one]
    exact congrArg Subtype.val h1
  have hu1 : ((ρ.symm u' : S) : PSL2 K) ≠ 1 := by
    intro h
    apply hu'1
    have h1 : ρ.symm u' = 1 := Subtype.ext h
    rw [← ρ.apply_symm_apply u', h1, map_one]
  have hut : ((ρ.symm u' : S) : PSL2 K) ≠ t := by
    intro h
    apply hu't
    have h1 : ρ.symm u' = ⟨t, htS⟩ := Subtype.ext h
    rw [← h1, MulEquiv.apply_symm_apply]
  have huc : ((ρ.symm u' : S) : PSL2 K) * t = t * ((ρ.symm u' : S) : PSL2 K) := by
    have h1 : ρ.symm u' * ⟨t, htS⟩ = ⟨t, htS⟩ * ρ.symm u' := by
      apply ρ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hu'c]
    exact congrArg Subtype.val h1
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power K hK t _
    ⟨ht1, by rw [sq]; exact htt⟩ ⟨hu1, by rw [sq]; exact huu⟩
  have huN : ((ρ.symm u' : S) : PSL2 K) ∈ N := by
    rw [← hg]
    exact hN.conj_mem t htN g
  exact ⟨t, htN, _, huN, htt, huu, ht1, hu1, fun h => hut h.symm, huc.symm⟩

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

include e in
theorem fcc_l2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (β : MulAut Y) (hβ2 : β * β = 1) (hβ : β ∉ innAut5 Y)
    (hR : ∃ R : Sylow 2 Y, ∀ r ∈ (R : Subgroup Y), β r = r) : ∃ M, FCConcl Y β M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hx2 : autEquiv e β * autEquiv e β = 1 := by rw [← map_mul, hβ2, map_one]
  by_cases hxr : (autEquiv e β).right = 1
  ·
    exfalso
    obtain ⟨R, hRβ⟩ := hR
    have h1 := Aut5L2.pgl_fixed_l2 e hodd R β ((Aut5L2.mem_linL2 e β).mpr hxr) hβ hβ2
    have hRle : (R : Subgroup Y) ⊓ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Y) = R :=
      inf_eq_left.mpr fun r hr => hRβ r hr
    rw [hRle] at h1
    obtain ⟨m, hm, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv e hodd R
    have hcard : Nat.card (R : Subgroup Y) = 2 ^ (m + 1) := by
      rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
    have : 2 ^ 2 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hxo, hσ, -⟩ := Aut5L2.field_involution_facts hp hF hx2 hxr
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd _ hxo hxr
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield _ hσ
  have hσσ : ∀ z, (autEquiv e β).right ((autEquiv e β).right z) = z := fun z => by
    have h1 : (autEquiv e β).right * (autEquiv e β).right = 1 := by
      have h2 := pow_orderOf_eq_one (autEquiv e β).right
      rwa [hσ, sq] at h2
    have := congrArg (fun τ : F ≃+* F => τ z) h1
    simpa using this
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := by
    apply isOddPrimePower_of_odd_card
    have hFodd : Odd (Nat.card F) := by
      obtain ⟨p', n, -, hpodd, -, hc⟩ := hodd
      rw [hc]
      exact hpodd.pow
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  set c : MulAut (PSL2 F) := semilinearAction F (SemidirectProduct.inl C) with hc
  have hsx : semilinearAction F (autEquiv e β) = c * psl2FieldAut F (autEquiv e β).right * c⁻¹ := by
    have h1 : autEquiv e β = SemidirectProduct.inl C * SemidirectProduct.inr (autEquiv e β).right *
        (SemidirectProduct.inl C)⁻¹ := by
      rw [← hC]
      group
    conv_lhs => rw [h1]
    rw [map_mul, map_mul, map_inv, semilinearAction_inr]
  set ψ : PSL2 K₀ →* Y := e.symm.toMonoidHom.comp (c.toMonoidHom.comp (psl2Sub K₀)) with hψ
  have hψinj : Function.Injective ψ :=
    e.symm.injective.comp (c.injective.comp (psl2Sub_injective K₀))
  have heψ : ∀ g, e (ψ g) = c (psl2Sub K₀ g) := fun g => by simp [ψ]
  refine ⟨ψ.range, ?_, ?_, fun N hNM hNn hN1 => ?_, fun α hα => ?_⟩
  ·
    rintro _ ⟨g, rfl⟩
    apply e.injective
    rw [← semilinearAction_autEquiv_apply, hsx, heψ, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
    congr 1
    exact psl2Sub_mem_fieldCent hK₀ g
  ·
    obtain ⟨-, ⟨ρ⟩⟩ := eqLocus_equiv_fieldCent hodd e β hx2 hxr
    rw [Nat.card_congr ρ.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      ← pgl2_card_eq_two_mul hK₀odd]
    exact card_fieldCent_le hK₀ h90 hσσ
  ·
    have hN'n : (N.comap ψ).Normal := ⟨fun n hn g => by
      show ψ (g * n * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNn (ψ g) ⟨g, rfl⟩ (ψ n) hn⟩
    have hN'1 : N.comap ψ ≠ ⊥ := by
      intro hbot
      apply hN1
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨g, rfl⟩ := hNM hy
      have hg : g ∈ N.comap ψ := hy
      rw [hbot, mem_bot] at hg
      rw [hg, map_one]
      exact one_mem _
    obtain ⟨a, ha, b, hb, haa, hbb, ha1, hb1, hab, habc⟩ :=
      exists_commuting_involutions_psl2 hK₀odd _ hN'n hN'1
    exact ⟨ψ a, ha, ψ b, hb, by rw [← map_mul, haa, map_one], by rw [← map_mul, hbb, map_one],
      fun h => ha1 (hψinj (by rw [h, map_one])), fun h => hb1 (hψinj (by rw [h, map_one])),
      fun h => hab (hψinj h), by rw [← map_mul, ← map_mul, habc]⟩
  ·
    have hfix : ∀ g : PSL2 K₀, semilinearAction F ((SemidirectProduct.inl C)⁻¹ * autEquiv e α *
        SemidirectProduct.inl C) (psl2Sub K₀ g) = psl2Sub K₀ g := by
      intro g
      have h1 : semilinearAction F (autEquiv e α) (c (psl2Sub K₀ g)) = c (psl2Sub K₀ g) := by
        rw [← heψ, semilinearAction_autEquiv_apply, hα (ψ g) ⟨g, rfl⟩]
      rw [map_mul, map_mul, map_inv, ← hc, MulAut.mul_apply, MulAut.mul_apply, h1,
        MulAut.inv_apply_self]
    have hconj : autEquiv e α = SemidirectProduct.inl C *
        ((SemidirectProduct.inl C)⁻¹ * autEquiv e α * SemidirectProduct.inl C) *
          (SemidirectProduct.inl C)⁻¹ := by group
    rcases eq_of_fixes_psl2Sub hxr hK₀ hcard _ hfix with h | h
    · left
      apply (autEquiv e).injective
      rw [hconj, h, map_one]
      group
    · right
      apply (autEquiv e).injective
      rw [hconj, h, ← hC]
      group

end CFSG.ComponentClassification.FooteLit.FCC
