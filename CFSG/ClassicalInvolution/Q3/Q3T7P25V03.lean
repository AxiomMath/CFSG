module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25V02
public import CFSG.ClassicalInvolution.Asc77.AscCX8E
public import CFSG.ClassicalInvolution.Asc77.AscCX4

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Main

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem exists_badCompl_of_bad {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
    {t u₁ u₂ : G} (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) {y : G}
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hya : y * a = a * y) (hy2 : C25W.InFour a z (y * y))
    (hyc : ∀ s ∈ (S : Subgroup G), C25W.InFour a z (s * y * s⁻¹ * y⁻¹))
    (hyV : ¬ C25W.InFour a z y) {b : G}
    (hbA : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb1 : b ≠ 1) (hbbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G))) :
    ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      b ∈ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
      ∀ g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g ∈ D ∨ g * z ∈ D := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hD₀A : Subgroup.zpowers b ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hbA
  have hD₀bad : z ∉ zStarOf (Subgroup.centralizer (Subgroup.zpowers b : Set G)) := by
    rwa [centralizer_zpowers_eq_singleton']
  have hD₀1 : Subgroup.zpowers b ≠ ⊥ := by
    intro h
    apply hb1
    have : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rwa [h, Subgroup.mem_bot] at this
  have hsmall : Nat.card (Subgroup.zpowers b) < 4 → ∃ x ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), x ∉ Subgroup.zpowers b ∧
        x * z ∉ Subgroup.zpowers b ∧ (∀ d ∈ Subgroup.zpowers b, x * d = d * x) ∧
        (x * x ∈ Subgroup.zpowers b ∨ x * x * z ∈ Subgroup.zpowers b) := by
    intro hlt
    have hb2 : b * b = 1 := by
      have h2 : IsPGroup 2 (Subgroup.zpowers b) :=
        S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hbA.1)
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      rw [Nat.card_zpowers] at hn hlt
      have hn1 : n ≤ 1 := by
        by_contra h
        push Not at h
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
        omega
      have hdvd : orderOf b ∣ 2 ^ 1 := by
        rw [hn]
        exact Nat.pow_dvd_pow 2 hn1
      have h := orderOf_dvd_iff_pow_eq_one.mp hdvd
      rwa [pow_one, pow_two] at h
    obtain ⟨x, hxset, hx1, hxb, hxz1, hxzb, hxbc, hxx⟩ := exists_witness_of_ext hz2 hz1
      hyp.hzS haA.1 ha2 ha1 haz hconj hyA.1 hya hy2 hyc hyV hbA.1 hb2
    have hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxset
      rcases hxset with rfl | rfl | rfl
      · exact haA
      · exact hyA
      · exact Subgroup.mul_mem _ hyA haA
    have hmem : ∀ g ∈ Subgroup.zpowers b, g = 1 ∨ g = b := fun g hg =>
      mem_zpowers_of_sq hb2 hg
    refine ⟨x, hxA, ?_, ?_, ?_, ?_⟩
    · intro h
      rcases hmem x h with h | h
      · exact hx1 h
      · exact hxb h
    · intro h
      rcases hmem _ h with h | h
      · exact hxz1 h
      · exact hxzb h
    · intro d hd
      rcases hmem d hd with rfl | rfl
      · simp
      · exact hxbc
    · rcases hxx with h | h | h | h
      · left
        rw [h]
        exact one_mem _
      · left
        rw [h]
        exact Subgroup.mem_zpowers b
      · right
        rw [h, hz2]
        exact one_mem _
      · right
        rw [h, mul_assoc, hz2, mul_one]
        exact Subgroup.mem_zpowers b
  obtain ⟨D, hDA, hD₀D, hDbad, hcov⟩ := exists_bad_complement h6 hyp hD₀A hD₀bad hD₀1 hsmall
  exact ⟨D, hDA, hD₀D (Subgroup.mem_zpowers b), hDbad, hcov⟩

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem centExtMix_of (h6 : Layer6Twin 3 1) : C25W.CentExtMix := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc
    hmix
  by_contra hyV
  obtain ⟨x, hxA, hxz, -, hxgood⟩ := hmix
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    T7T.z_mem_centralizer_of_hyp hyp
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hA
  set 𝒟 : Set (Subgroup G) := {D | D ≤ A ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
    ∀ g ∈ A, g ∈ D ∨ g * z ∈ D} with h𝒟
  set N : Subgroup G := A ⊓ ⨅ D ∈ 𝒟, D with hN
  have hmemN : ∀ g, g ∈ N ↔ g ∈ A ∧ ∀ D ∈ 𝒟, g ∈ D := by
    intro g
    simp only [hN, Subgroup.mem_inf, Subgroup.mem_iInf]
  obtain ⟨D₁, hD₁A, -, hD₁bad, hD₁cov, -⟩ :=
    exists_bad_complement_of_ext h6 hyp haA ha2 ha1 haz hbad hyA hya hy2 hyV
  have hD₁ : D₁ ∈ 𝒟 := ⟨hD₁A, hD₁bad, hD₁cov⟩
  have hzD : ∀ D ∈ 𝒟, z ∉ D := fun D hD => not_mem_of_badSub hyp hD.1 hD.2.1
  have hbadD : ∀ D ∈ 𝒟, ∀ g ∈ D, g ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({g} : Set G)) :=
    fun D hD g hg _ => C25W.not_mem_zStarOf_of_mem_badSub hg
      (fun y hy => hzS y (hD.1 hy).1) hD.2.1
  have hNA : N ≤ A := inf_le_left
  have hND : ∀ D ∈ 𝒟, N ≤ D := fun D hD g hg => ((hmemN g).mp hg).2 D hD
  have hxN : x ∈ N := by
    refine (hmemN x).mpr ⟨hxA, fun D hD => ?_⟩
    rcases hD.2.2 x hxA with h | h
    · exact h
    · exfalso
      by_cases hxz1 : x * z = 1
      · apply hxz
        have : x = z := by
          calc x = x * z * z := by rw [mul_assoc, hz2, mul_one]
            _ = z := by rw [hxz1, one_mul]
        rw [this]
        exact Subgroup.mem_zpowers z
      · exact hbadD D hD _ h hxz1 hxgood
  have hN1 : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxN
    apply hxz
    rw [hxN]
    exact one_mem _
  have hNbad : ∀ n ∈ N, n ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({n} : Set G)) :=
    fun n hn hn1 => hbadD D₁ hD₁ n (hND D₁ hD₁ hn) hn1
  have hNgood : ∀ n ∈ N, n ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({n * z} : Set G)) := by
    intro n hn hn1
    by_contra hng
    have hnz1 : n * z ≠ 1 := by
      intro h
      apply hzD D₁ hD₁
      have : n = z := by
        calc n = n * z * z := by rw [mul_assoc, hz2, mul_one]
          _ = z := by rw [h, one_mul]
      rw [← this]
      exact hND D₁ hD₁ hn
    obtain ⟨D', hD'A, hnzD', hD'bad, hD'cov⟩ := exists_badCompl_of_bad h6 hyp haA ha2 ha1 haz
      hconj hyA hya hy2 hyc hyV (A.mul_mem (hNA hn) hzA) hnz1 hng
    have hD' : D' ∈ 𝒟 := ⟨hD'A, hD'bad, hD'cov⟩
    apply hzD D' hD'
    have e1 : z = n⁻¹ * (n * z) := by group
    rw [e1]
    exact D'.mul_mem (D'.inv_mem (hND D' hD' hn)) hnzD'
  have hAsc : ∀ g ∈ A, ∀ c : G, c * z * c⁻¹ = z → c * g * c⁻¹ ∈ (S : Subgroup G) →
      c * g * c⁻¹ ∈ A := by
    intro g hg c hc hcS
    have h1 := mem_trivialOnQuot_of_mem_A hyp hg
    exact C25Y.conj_mem_Csub hyp h1.1 h1.2 hc hcS
  have hsc := C25W.stronglyClosed_inter_of_good hz2 hAsc 𝒟 (fun D hD => hD.2.2) hzD hbadD hNA
    hND (fun g hg hall => (hmemN g).mpr ⟨hg, hall⟩) hNgood
  exact false_of_mixedClosed h6 (ModelFacts.L6C.layer6Cen4_proved 3 1) hyp hNA hN1 hsc hNbad
    hNgood

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem centExt_of_noMixParity (h6 : Layer6Twin 3 1) (h : NoMixParity) :
    C25W.CentExt :=
  centExt_of h6 (centExtMix_of h6) h
end Main
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem centExt_of_noMixParity' (h : NoMixParity) : C25W.CentExt :=
  centExt_of_noMixParity (layer6Twin_proved 3 1) h
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Residual

@[expose] def ParityE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ d₁ d₂ : G,
        d₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        d₂ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        d₁ * d₁ = 1 → d₂ * d₂ = 1 → d₁ * d₂ = d₂ * d₁ →
        d₁ ≠ 1 → d₂ ≠ 1 → d₁ ≠ d₂ → z ≠ d₁ → z ≠ d₂ → z ≠ d₁ * d₂ →
        z ∉ zStarOf (Subgroup.centralizer ({d₁, d₂} : Set G)) →
        (∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G),
          z ∉ zStarOf (Subgroup.centralizer ({d} : Set G)) ∧
            z ∉ zStarOf (Subgroup.centralizer ({d * z} : Set G))) →
        (∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G),
          (LayerOrthType Ω d 5 true ∨ LayerOrthType Ω d 6 (!piSign 3 1)) ∧
            (LayerOrthType Ω (d * z) 5 true ∨
              LayerOrthType Ω (d * z) 6 (!piSign 3 1))) →
        False
end Residual
section Reduction

theorem noMixParity_of_parityE4 (h : ParityE4) : NoMixParity := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp D hDA hDbad hcov h4 hsq hcomm hnomix htyp
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzD : z ∉ D := not_mem_of_badSub hyp hDA hDbad
  have hbadD : ∀ x ∈ D, z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) := fun x hx =>
    C25W.not_mem_zStarOf_of_mem_badSub hx (fun y hy => hzS y (hDA hy).1) hDbad
  obtain ⟨d₁, hd₁D, hd₁1⟩ : ∃ d₁ ∈ D, d₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (a := 1) (b := 1) fun x hx => Or.inl (hcon x hx)
    omega
  obtain ⟨d₂, hd₂D, hd₂1, hd₂₁⟩ : ∃ d₂ ∈ D, d₂ ≠ 1 ∧ d₂ ≠ d₁ := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (a := 1) (b := d₁) fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx hx1)
    omega
  have hd₁₂D : d₁ * d₂ ∈ D := D.mul_mem hd₁D hd₂D
  have hmemD : ∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G), d ∈ D := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact hd₁D
    · exact hd₂D
    · exact hd₁₂D
  have hzne : ∀ d ∈ D, z ≠ d := fun d hd h => hzD (h ▸ hd)
  have hgood : ∀ d ∈ D, d ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({d} : Set G)) ∧
      z ∉ zStarOf (Subgroup.centralizer ({d * z} : Set G)) := by
    intro d hd hd1
    refine ⟨hbadD d hd, hnomix d (hDA hd) ?_ (hbadD d hd)⟩
    intro hdz
    rcases mem_zpowers_of_sq hz2 hdz with h1 | h1
    · exact hd1 h1
    · exact hzne d hd h1.symm
  have hne1 : ∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G), d ≠ 1 := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact hd₁1
    · exact hd₂1
    · intro h1
      apply hd₂₁
      calc d₂ = d₁⁻¹ * (d₁ * d₂) := by group
        _ = d₁ := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right (hsq d₁ hd₁D)]
  refine h G Ω K K' W S R R' z t u₁ u₂ hyp d₁ d₂ (hDA hd₁D) (hDA hd₂D) (hsq d₁ hd₁D)
    (hsq d₂ hd₂D) (hcomm d₁ hd₁D d₂ hd₂D) hd₁1 hd₂1 hd₂₁.symm (hzne d₁ hd₁D) (hzne d₂ hd₂D)
    (hzne _ hd₁₂D) ?_ (fun d hd => hgood d (hmemD d hd) (hne1 d hd)) fun d hd => ?_
  ·
    intro hz
    apply hDbad
    refine T7T.mem_zStarOf_of_le ?_ hz ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      rintro x (rfl | rfl)
      · exact hg _ hd₁D
      · exact hg _ hd₂D
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hDA hg).1
  ·
    have hdD := hmemD d hd
    have hdA := hDA hdD
    have hdz : d * z = z * d := hzS d hdA.1
    have hdzA : d * z ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ hdA (T7T.z_mem_centralizer_of_hyp hyp)
    refine ⟨htyp d hdA (hsq d hdD) (hne1 d hd) (hgood d hdD (hne1 d hd)).1, ?_⟩
    refine htyp (d * z) hdzA ?_ ?_ (hgood d hdD (hne1 d hd)).2
    · calc d * z * (d * z) = (d * d) * (z * z) := by
            rw [show d * z * (d * z) = d * (z * d) * z by group, ← hdz]
            group
        _ = 1 := by rw [hsq d hdD, hz2, one_mul]
    · intro h1
      apply hzne d hdD
      calc z = d⁻¹ * (d * z) := by group
        _ = d := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right (hsq d hdD)]

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem centExt_of_parityE4 (h : ParityE4) : C25W.CentExt :=
  centExt_of_noMixParity' (noMixParity_of_parityE4 h)
end Reduction
end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
