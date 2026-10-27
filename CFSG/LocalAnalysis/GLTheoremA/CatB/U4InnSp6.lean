module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp6

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434Kit

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (H.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem conj_mem_map_subtype (D : Subgroup H6) {K : Subgroup ↥D} (hK : K.Normal) :
    ∀ d : H6, d ∈ D → ∀ k : H6, k ∈ K.map D.subtype → d * k * d⁻¹ ∈ K.map D.subtype := by
  intro d hd k hk
  obtain ⟨k0, hk0, hk0e⟩ := Subgroup.mem_map.1 hk
  have hx : (⟨d, hd⟩ * k0 * ⟨d, hd⟩⁻¹ : ↥D) ∈ K := hK.conj_mem k0 hk0 ⟨d, hd⟩
  have hy : D.subtype ((⟨d, hd⟩ * k0 * ⟨d, hd⟩⁻¹ : ↥D)) = d * k * d⁻¹ := by
    rw [← hk0e]; simp
  rw [← hy]
  exact Subgroup.mem_map_of_mem _ hx


theorem pPrimeCore_eq_bot_of_dvd (D : Subgroup H6) (h81 : 81 ∣ Nat.card D) :
    CFSG.pPrimeCore 3 ↥D = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup H6, K' = K.map D.subtype := ⟨_, rfl⟩
  have hnorm : ∀ d : H6, d ∈ D → ∀ k : H6, k ∈ K' → d * k * d⁻¹ ∈ K' := by
    rw [hK']; exact conj_mem_map_subtype D hK
  have hK'card : Nat.card K' = Nat.card K := by
    rw [hK']; exact Subgroup.card_map_of_injective D.subtype_injective
  have hK'3 : ¬ 3 ∣ Nat.card K' := by
    rw [hK'card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥D) := inferInstance
  have hDpos : Nat.card D ≠ 0 := by
    haveI : Finite ↥D := inferInstance
    exact Nat.card_pos.ne'
  have hv : (Nat.card D).factorization 3 = 4 := by
    have h1 : 4 ≤ (Nat.card D).factorization 3 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hDpos]
      simpa using h81
    have h2 : (Nat.card D).factorization 3 ≤ (Nat.card H6).factorization 3 :=
      (Nat.factorization_le_iff_dvd hDpos (Nat.card_pos (α := H6)).ne').2
        (Subgroup.card_subgroup_dvd_card D) 3
    rw [factorization_card_H6] at h2
    omega
  set P' : Subgroup H6 := (P : Subgroup ↥D).map D.subtype with hP'
  have hP'card : Nat.card P' = 3 ^ (Nat.card H6).factorization 3 := by
    rw [hP', Subgroup.card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity, hv,
      factorization_card_H6]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := P') (E := wreathW zH tH) hP'card (isPGroup_wreathW wreathFacts_zH)
  have hP'D : ∀ p ∈ P', p ∈ D := by
    rintro _ ⟨p, -, rfl⟩
    exact p.2
  have hAN : baseA zH ≤ Subgroup.normalizer ((K'.map (MulAut.conj g).toMonoidHom : Subgroup H6) : Set H6) := by
    refine le_normalizer_of_conj_mem ?_
    intro a ha y hy
    have haW : a ∈ wreathW zH tH := (le_sup_left : baseA zH ≤ wreathW zH tH) ha
    obtain ⟨p, hp, rfl⟩ := hg haW
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨p * k * p⁻¹, hnorm p (hP'D p hp) k hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hYcard : Nat.card (K'.map (MulAut.conj g).toMonoidHom : Subgroup H6) = Nat.card K' :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hbot := eq_bot_of_baseA_le_normalizer (by rwa [hYcard]) hAN
  have hK'bot : K' = ⊥ := (Subgroup.map_eq_bot_iff_of_injective K' (MulAut.conj g).injective).1 hbot
  rw [hK'] at hK'bot
  exact (Subgroup.map_eq_bot_iff_of_injective K D.subtype_injective).1 hK'bot

end CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp6

end
