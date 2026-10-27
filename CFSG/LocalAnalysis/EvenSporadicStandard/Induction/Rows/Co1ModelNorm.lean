module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1NormSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCLocal

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Co1Cent

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.EvenSporadicStandard.Co1Pair
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction Subgroup

section Model


theorem co1_K_eq {H : Type} [Group H] {L K : Subgroup H} {u : H}
    (hQ : Co1Pair H L K u) {Ψ : ↥L →* GL24} (hΨ : Function.Injective Ψ)
    (hΨA : ∀ x, Ψ x ∈ GA) (hΨu : Ψ ⟨u, hQ.1⟩ = A₁) :
    (K.subgroupOf L).map Ψ = K₁.map ιC := by
  obtain ⟨hperf, hcard⟩ := K₁_facts
  have hQ2 := co1_quot2Data
  have hKL : K ≤ L := hQ.2.2.1
  have hperfKL : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L :=
    Subgroup.isPerfect_iff.1 (isPerfect_subgroupOf_of_le hKL hQ.2.2.2.2.1)
  have hcardKL : Nat.card ↥(K.subgroupOf L) = Nat.card twoBD := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hQ.2.2.2.2.2, card_twoBD]
  have hcent : ∀ k ∈ K.subgroupOf L, Ψ k ∈ GA ⊓ Subgroup.centralizer {A₁} := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨hΨA k, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hΨu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have hle : (K.subgroupOf L).map Ψ ≤ ιC.range := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨liftC (Ψ k) (hcent k hk), rfl⟩
  let KC : Subgroup C₁ := ((K.subgroupOf L).map Ψ).comap ιC
  have hKC : KC.map ιC = (K.subgroupOf L).map Ψ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hle]
  have hcommKC : ⁅KC, KC⁆ = KC := by
    apply Subgroup.map_injective ιC_injective
    rw [Subgroup.map_commutator, hKC, ← Subgroup.map_commutator, hperfKL]
  have hcardKC : Nat.card KC = Nat.card twoBD := by
    have h1 : Nat.card (KC.map ιC) = Nat.card KC := Subgroup.card_map_of_injective ιC_injective
    have h2 : Nat.card ((K.subgroupOf L).map Ψ) = Nat.card (K.subgroupOf L) :=
      Subgroup.card_map_of_injective hΨ
    rw [← hcardKL, ← h1, hKC, h2]
  have hKCK : KC = K₁ :=
    hQ2.eq_of_perfect hperf hcard (Subgroup.isPerfect_iff.2 hcommKC) hcardKC
  rw [← hKC, hKCK]

theorem co1_normal_elts
    {H : Type} [Group H] [Finite H]
    {L K N₀ : Subgroup H} {u : H} (hQ : Co1Pair H L K u) (hcan : CanLoc K N₀)
    {Ψ : ↥L →* GL24} (hΨ : Function.Injective Ψ) (hΨA : ∀ x, Ψ x ∈ GA)
    (hΨu : Ψ ⟨u, hQ.1⟩ = A₁) :
    ∃ p ∈ K₁, ∀ j < 6, ∃ k : ↥L, (k : H) ∈ N₀ ∧ Ψ k = ιC (p * sElt j * p⁻¹) := by
  have hKe := co1_K_eq hQ hΨ hΨA hΨu
  have hKL : K ≤ L := hQ.2.2.1
  have hlift : ∀ c ∈ K₁, ∃ k : ↥L, (k : H) ∈ K ∧ Ψ k = ιC c := by
    intro c hc
    have : ιC c ∈ (K.subgroupOf L).map Ψ := hKe ▸ ⟨c, hc, rfl⟩
    obtain ⟨k, hk, hkc⟩ := this
    exact ⟨k, Subgroup.mem_subgroupOf.1 hk, hkc⟩
  rcases hcan with ⟨-, hN⟩ | ⟨-, R, hR0, hRK, hRc, hN⟩
  · rw [hN]
    refine ⟨1, K₁.one_mem, fun j _ => ?_⟩
    obtain ⟨k, hk, hkc⟩ := hlift (sElt j) (sElt_mem_K₁ j)
    exact ⟨k, hk, by simpa using hkc⟩
  · rw [hN]
    obtain ⟨R0, hR0K, hR0c, hR0n⟩ := R0_facts
    obtain ⟨-, hcardK₁⟩ := K₁_facts
    have hcardK : Nat.card K = 2 ^ 12 * 61425 := by rw [hQ.2.2.2.2.2]; norm_num
    have hfac : (Nat.card K).factorization 2 = 12 := by
      rw [hcardK]
      exact AutBound.factorization_two_of_odd (by decide)
    rw [hfac] at hRc
    have hRL : R ≤ L := hRK.trans hKL
    let RG : Subgroup GL24 := (R.subgroupOf L).map Ψ
    have hRG_le : RG ≤ K₁.map ιC := by
      rw [← hKe]
      exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
        (hRK (Subgroup.mem_subgroupOf.1 hx)))
    let RC : Subgroup C₁ := RG.comap ιC
    have hRCmap : RC.map ιC = RG := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 (hRG_le.trans (Subgroup.map_le_range _ _))]
    have hRCK : RC ≤ K₁ := by
      intro c hc
      obtain ⟨c', hc', he⟩ := hRG_le hc
      rw [← ιC_injective he]
      exact hc'
    have hRCc : Nat.card RC = 2 ^ 12 := by
      have h1 : Nat.card (RC.map ιC) = Nat.card RC := Subgroup.card_map_of_injective ιC_injective
      have h2 : Nat.card RG = Nat.card (R.subgroupOf L) := Subgroup.card_map_of_injective hΨ
      have h3 : Nat.card (R.subgroupOf L) = Nat.card R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
      rw [← h1, hRCmap, h2, h3, hRc]
    have hK₁card : Nat.card K₁ = 2 ^ 12 * 61425 := by rw [hcardK₁, card_twoBD]; norm_num
    obtain ⟨p, hpK, hconj⟩ := AutBound.exists_conj_of_card_eq K₁ R0 RC hR0K hRCK (a := 12)
      (m := 61425) (by decide) hK₁card hR0c hRCc
    refine ⟨p, hpK, fun j hj => ?_⟩
    have hs := hR0n j hj
    rw [Subgroup.mem_normalizer_iff] at hs
    have ht : p * sElt j * p⁻¹ ∈ K₁ :=
      K₁.mul_mem (K₁.mul_mem hpK (sElt_mem_K₁ j)) (K₁.inv_mem hpK)
    obtain ⟨k, hkK, hkc⟩ := hlift _ ht
    refine ⟨k, Subgroup.mem_inf.2 ⟨?_, hkK⟩, hkc⟩
    refine AutBound.mem_normalizer_of_map_le R (k : H) ?_
    rintro _ ⟨r, hr, rfl⟩
    have hrL : r ∈ L := hRL hr
    have hrG : Ψ ⟨r, hrL⟩ ∈ RG := ⟨⟨r, hrL⟩, Subgroup.mem_subgroupOf.2 hr, rfl⟩
    rw [← hRCmap] at hrG
    obtain ⟨c, hcRC, hc⟩ := hrG
    have hc' : p * sElt j * p⁻¹ * c * (p * sElt j * p⁻¹)⁻¹ ∈ RC := by
      refine (hconj _).2 ?_
      have h1 := (hs _).1 ((hconj c).1 hcRC)
      have e : p⁻¹ * (p * sElt j * p⁻¹ * c * (p * sElt j * p⁻¹)⁻¹) * p =
          sElt j * (p⁻¹ * c * p) * (sElt j)⁻¹ := by group
      rw [e]
      exact h1
    have hc'' : ιC (p * sElt j * p⁻¹ * c * (p * sElt j * p⁻¹)⁻¹) ∈ RG := by
      rw [← hRCmap]
      exact ⟨_, hc', rfl⟩
    obtain ⟨r'', hr'', hr''e⟩ := hc''
    have hEq : k * ⟨r, hrL⟩ * k⁻¹ = r'' := by
      apply hΨ
      rw [hr''e, map_mul, map_mul, map_inv, hkc, ← hc]
      simp only [map_mul, map_inv]
    have h4 : (k : H) * r * (k : H)⁻¹ = (r'' : H) := congrArg Subtype.val hEq
    show (k : H) * r * (k : H)⁻¹ ∈ R
    rw [h4]
    exact Subgroup.mem_subgroupOf.1 hr''

end Model

end CFSG.EvenSporadicStandard.Co1Cent
