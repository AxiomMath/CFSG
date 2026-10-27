module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open scoped commutatorElement

@[expose] def OddLieOuterCoreInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel S .PSL 2 p f) →
    ∀ i : MulAut S, orderOf i = 2 → ∀ R : Subgroup (MulAut S), Odd (Nat.card R) →
      (∀ r ∈ R, r * i = i * r) →
      (∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

section Reduction

variable {K : Type} [Group K] [Finite K]

theorem core_commutator_le_of_outerCore (hLB : FooteLBalanceInput) {a : K}
    (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (hcore : ∀ i : MulAut (Y ⧸ Open.fusionZStar Y), orderOf i = 2 →
      ∀ R : Subgroup (MulAut (Y ⧸ Open.fusionZStar Y)), Odd (Nat.card R) →
      (∀ r ∈ R, r * i = i * r) →
      (∀ s : Y ⧸ Open.fusionZStar Y, i s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Y.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hY
    exact h
  have hOK := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  obtain ⟨hWN, hcent⟩ := hLB K a ha Y hY
  set W := oddCoreOfCentralizer a
  have hWW := commutator_self_le W
  by_cases hswap : conjugate Y a ≠ Y
  · exact ((commutator_mono hWW le_rfl).trans (hcent (Or.inl hswap))).trans hOK
  have haN := mem_normalizer_of_conjugate_eq (not_not.mp hswap)
  set N := normalizer (Y : Set K)
  set ψ := Y.normalizerMonoidHom
  set α := ψ ⟨a, haN⟩ with hαdef
  set ᾱ := zStarAut Y α with hᾱ
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hone : (⟨a, haN⟩ : N) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
  by_cases hα1 : ᾱ = 1
  ·
    refine ((commutator_mono hWW le_rfl).trans (hcent (Or.inr fun x hx => ?_))).trans hOK
    have hc := commutator_mem_oddCore_of_zStarAut_eq_one hY haN hα1 hx
    have hc' := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
      (le_normalizer (inv_mem hx)) hc
    rw [show x⁻¹ * ⁅a, x⁆ * x⁻¹⁻¹ = x⁻¹ * a⁻¹ * x * a by
      rw [commutatorElement_def, hainv]; group] at hc'
    exact hc'
  have hα : ∀ y, α (α y) = y := fun y => by
    rw [← MulAut.mul_apply, hαdef, ← map_mul, hone, map_one, MulAut.one_apply]
  have hord : orderOf ᾱ = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [hᾱ, ← map_pow, hαdef, ← map_pow, sq, hone, map_one, map_one]
  set R := ((W.subgroupOf N).map ψ).map (zStarAut Y) with hR
  have hWodd : Odd (Nat.card W) := by
    have h : Nat.card W = Nat.card (pPrimeCore 2 ↥(centralizer ({a} : Set K))) :=
      card_map_of_injective (subtype_injective _)
    rw [h]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hRodd : Odd (Nat.card R) := by
    refine Odd.of_dvd_nat (Odd.of_dvd_nat ?_ (card_map_dvd _ _)) (card_map_dvd _ _)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv]
  have hWa : ∀ w ∈ W, w * a = a * w := fun w hw =>
    mem_centralizer_singleton_iff.mp (oddCoreOfCentralizer_le_centralizer a hw)
  have hRα : ∀ r ∈ R, r * ᾱ = ᾱ * r := by
    rintro _ ⟨_, ⟨⟨w, hwN⟩, hw, rfl⟩, rfl⟩
    have hc : ψ ⟨w, hwN⟩ * α = α * ψ ⟨w, hwN⟩ := by
      rw [hαdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hWa w (mem_subgroupOf.mp hw))
    rw [hᾱ, ← map_mul, hc, map_mul]
  have hRconj : ∀ s : Y ⧸ Open.fusionZStar Y, ᾱ s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R := by
    rintro s hsα hs _ ⟨_, ⟨⟨w, hwN⟩, hw, rfl⟩, rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_fixed_lift hα hs hsα
    have hcC : (c : K) ∈ centralizer ({a} : Set K) := by
      have h := congrArg Subtype.val hc
      rw [hαdef, normalizerMonoidHom_apply_apply_coe] at h
      apply mem_centralizer_singleton_iff.mpr
      calc (c : K) * a = a * c * a⁻¹ * a := by rw [h]
        _ = a * c := by group
    have hcw : (c : K) * w * (c : K)⁻¹ ∈ W :=
      conj_mem_oddCoreOfCentralizer hcC (mem_subgroupOf.mp hw)
    refine ⟨ψ (⟨(c : K), le_normalizer c.2⟩ * ⟨w, hwN⟩ * ⟨(c : K), le_normalizer c.2⟩⁻¹),
      ⟨_, mem_subgroupOf.mpr hcw, rfl⟩, ?_⟩
    have hψc : ψ ⟨(c : K), le_normalizer c.2⟩ = MulAut.conj c := normalizerMonoidHom_of_mem c.2
    simp only [map_mul, map_inv, hψc, zStarAut_conj]
  have hcomm := hcore ᾱ hord R hRodd hRα hRconj
  have hmemR : ∀ w (h : w ∈ W), zStarAut Y (ψ ⟨w, hWN h⟩) ∈ R := fun w h =>
    ⟨ψ ⟨w, hWN h⟩, ⟨⟨w, hWN h⟩, mem_subgroupOf.mpr h, rfl⟩, rfl⟩
  have hker : ⁅W, W⁆ ≤ ((zStarAut Y).comp ψ).ker.map N.subtype := by
    rw [commutator_le]
    intro w₁ hw₁ w₂ hw₂
    refine ⟨⁅(⟨w₁, hWN hw₁⟩ : N), ⟨w₂, hWN hw₂⟩⁆, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ (hmemR w₁ hw₁) _ (hmemR w₂ hw₂)
  rw [commutator_le]
  intro g hg y hy
  obtain ⟨n, hn, rfl⟩ := hker hg
  exact hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY n.2 (by simpa using hn) hy)

end Reduction

theorem footeCoreOddLieInput_of_outerCore (h : OddLieOuterCoreInput) : FooteCoreOddLieInput := by
  intro K _ _ _ a ha Y hY hodd hL2 _ _
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have := hsimple
  exact core_commutator_le_of_outerCore footeLBalanceInput_holds ha hY
    (h (Y ⧸ Open.fusionZStar Y) hna hodd hL2)

end CFSG.ComponentClassification.Foote5
