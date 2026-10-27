module

public import CFSG.Sporadic.Co1Block.TwoCCent
public import Certificates.Certificate129072
public import Certificates.Certificate129073
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier

theorem exists_conj_le_sylow {G : Type} [Group G] [Finite G] {P S B : Subgroup G} (hSP : S ≤ P)
    (hS : Nat.card S = 2 ^ (Nat.card P).factorization 2) (hBP : B ≤ P)
    (hsq : ∀ x ∈ B, x * x = 1) : ∃ g ∈ P, ∀ x ∈ B, g⁻¹ * x * g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Nat.card (S.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv, hS]
  let S' : Sylow 2 P := Sylow.ofCard (S.subgroupOf P) hT
  have hB2 : IsPGroup 2 (B.subgroupOf P) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa [sq] using hsq _ (Subgroup.mem_subgroupOf.1 x.2)
  obtain ⟨T, hTle⟩ := hB2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq P S' T
  refine ⟨x, x.2, fun b hb => ?_⟩
  have hbT : (⟨b, hBP hb⟩ : P) ∈ (T : Subgroup P) :=
    hTle (Subgroup.mem_subgroupOf.2 hb)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbT
  obtain ⟨s, hs, hst⟩ := hbT
  have hsS : (s : G) ∈ S := by
    have : s ∈ S.subgroupOf P := by
      rwa [show ((S' : Subgroup P)) = S.subgroupOf P from Sylow.coe_ofCard _ _] at hs
    exact Subgroup.mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨b, hBP hb⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem conj_facts {B : Subgroup GL24}
    (hBGA : B ≤ GA) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hnonA : ∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) {g : GL24} (hg : g ∈ GA) :
    Nat.card (B.map (MulAut.conj g).toMonoidHom) = Nat.card B ∧
      B.map (MulAut.conj g).toMonoidHom ≤ GA ∧
      (∀ x ∈ B.map (MulAut.conj g).toMonoidHom, ∀ y ∈ B.map (MulAut.conj g).toMonoidHom,
        x * y = y * x) ∧
      (∀ x ∈ B.map (MulAut.conj g).toMonoidHom, x * x = 1) ∧
      (∀ x ∈ B.map (MulAut.conj g).toMonoidHom, x ≠ 1 → (xFix x).ncard ≠ 2280) := by
  refine ⟨Subgroup.card_map_of_injective (MulAut.conj g).injective, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact GA.mul_mem (GA.mul_mem hg (hBGA hb)) (GA.inv_mem hg)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  · rintro _ ⟨a, ha, rfl⟩ h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 ⊢
    have ha1 : a ≠ 1 := fun h => h1 (by rw [h]; group)
    rw [ncard_fix_conj hg]
    exact hnonA a ha ha1

theorem closure_le_inf_cent {gg : ℕ → GL24} {n : ℕ} {t : GL24}
    (h : ∀ g < n, gg g ∈ GA ∧ gg g * t = t * gg g) :
    Subgroup.closure (gg '' {g | g < n}) ≤ GA ⊓ Subgroup.centralizer {t} := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact Subgroup.mem_inf.2 ⟨(h g hg).1, Subgroup.mem_centralizer_singleton_iff.2 (h g hg).2⟩

theorem card_lt_of_sylow
    {S : Subgroup GL24} {t : GL24} (hSP : S ≤ GA ⊓ Subgroup.centralizer {t})
    (hcard : Nat.card S =
      2 ^ (Nat.card (GA ⊓ Subgroup.centralizer {t} : Subgroup GL24)).factorization 2)
    (hS : ∀ B : Subgroup GL24, B ≤ S → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → t ∈ B → (∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) → Nat.card B ≤ 16)
    {B : Subgroup GL24} (hBGA : B ≤ GA) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (htB : t ∈ B) (hnonA : ∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) :
    Nat.card B < 64 := by
  have hBP : B ≤ GA ⊓ Subgroup.centralizer {t} := fun x hx =>
    Subgroup.mem_inf.2 ⟨hBGA hx, Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx t htB)⟩
  obtain ⟨g, hgP, hgS⟩ := exists_conj_le_sylow hSP hcard hBP hsq
  have hgGA : g⁻¹ ∈ GA := GA.inv_mem (Subgroup.mem_inf.1 hgP).1
  have hgt : g * t = t * g :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hgP).2 t (Set.mem_singleton t)).symm
  obtain ⟨hc, -, hcomm', hsq', hnonA'⟩ := conj_facts hBGA hcomm hsq hnonA hgGA
  have hmem : ∀ x, x ∈ B.map (MulAut.conj g⁻¹).toMonoidHom ↔ ∃ b ∈ B, g⁻¹ * b * g = x := by
    intro x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have htg : g⁻¹ * t * g = t := by
    calc g⁻¹ * t * g = g⁻¹ * (t * g) := by group
      _ = g⁻¹ * (g * t) := by rw [hgt]
      _ = t := by group
  have := hS (B.map (MulAut.conj g⁻¹).toMonoidHom)
    (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := (hmem x).1 hx
      exact hgS b hb) hcomm' hsq' ((hmem t).2 ⟨t, htB, htg⟩) hnonA'
  rw [hc] at this
  omega

theorem factorization_two_pow_mul_odd' {N r : ℕ} (hr : Odd r) : (2 ^ N * r).factorization 2 = N := by
  have hr2 : ¬ 2 ∣ r := by
    rintro ⟨k, rfl⟩
    exact (Nat.not_even_iff_odd.mpr hr) (even_two_mul k)
  rw [Nat.factorization_mul (by positivity) hr.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hr2, add_zero]

theorem card_lt_of_B
    {B : Subgroup GL24} (hBGA : B ≤ GA)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) (htB : A₁ ∈ B)
    (hnonA : ∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) : Nat.card B < 64 := by
  obtain ⟨hcard, hgens, hS⟩ := Certificates.certificate129072
  refine card_lt_of_sylow (closure_le_inf_cent hgens) ?_ hS hBGA hcomm hsq htB hnonA
  rw [hcard, card_GA_cent_A₁, (by norm_num : (2012774400 : ℕ) = 2 ^ 15 * 61425),
    factorization_two_pow_mul_odd' (by decide)]

theorem card_lt_of_C
    {B : Subgroup GL24}
    (hBGA : B ≤ GA) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (htB : cG ∈ B) (hnonA : ∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) : Nat.card B < 64 := by
  obtain ⟨hcard, hgens, hS⟩ := Certificates.certificate129073
  refine card_lt_of_sylow (t := cG) (closure_le_inf_cent hgens) ?_ hS hBGA hcomm hsq htB hnonA
  rw [hcard, card_cent_cG, (by norm_num : (389283840 : ℕ) = 2 ^ 18 * 1485),
    factorization_two_pow_mul_odd' (by decide)]

theorem noA_rank_GA
    {B : Subgroup GL24} (hBGA : B ≤ GA) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hnonA : ∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) :
    Nat.card B ≤ 2 ^ 5 := by
  have hlt : Nat.card B < 64 := by
    by_cases hB1 : ∀ x ∈ B, x = 1
    · have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hB1
      rw [this, Subgroup.card_bot]
      norm_num
    push Not at hB1
    obtain ⟨b, hb, hb1⟩ := hB1
    have hbo : orderOf (⟨b, hBGA hb⟩ : GA) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [sq]; exact hsq b hb) hb1
    rcases involution_classes.1 _ hbo with h | h | h
    · exfalso
      have := ncard_fix_isConj h
      rw [ncard_fix_aC] at this
      exact hnonA b hb hb1 this.symm
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      have hcG : (c : GL24) * b * (c : GL24)⁻¹ = cG := by
        have := congrArg Subtype.val hc
        simpa using this
      obtain ⟨hcard, hle, hcm, hsq', hna⟩ := conj_facts hBGA hcomm hsq hnonA c.2
      rw [← hcard]
      refine card_lt_of_C hle hcm hsq' ?_ hna
      exact ⟨b, hb, by simpa [MulAut.conj_apply] using hcG⟩
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      have hcG : (c : GL24) * b * (c : GL24)⁻¹ = A₁ := by
        have := congrArg Subtype.val hc
        simpa using this
      obtain ⟨hcard, hle, hcm, hsq', hna⟩ := conj_facts hBGA hcomm hsq hnonA c.2
      rw [← hcard]
      refine card_lt_of_B hle hcm hsq' ?_ hna
      exact ⟨b, hb, by simpa [MulAut.conj_apply] using hcG⟩
  have hp : IsPGroup 2 B := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa [sq] using hsq x x.2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hlt ⊢
  exact Nat.pow_le_pow_right (by norm_num) (by
    by_contra hk4
    push Not at hk4
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    omega)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
