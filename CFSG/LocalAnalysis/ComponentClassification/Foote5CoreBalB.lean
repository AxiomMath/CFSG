module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreBal

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem core_commutator_le_of_outer_comm (hLB : FooteLBalanceInput) {a : K}
    (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (hbal : ∀ i : MulAut (Y ⧸ Open.fusionZStar Y), orderOf i = 2 →
      pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut (Y ⧸ Open.fusionZStar Y)))) = ⊥)
    (hOut : ∀ H : Subgroup (OuterAutomorphisms.Outer (Y ⧸ Open.fusionZStar Y)),
      Odd (Nat.card H) → ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) :
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
  set ψ := Y.normalizerMonoidHom
  set ᾱ := zStarAut Y (ψ ⟨a, haN⟩) with hᾱ
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  by_cases hα1 : ᾱ = 1
  · refine ((commutator_mono hWW le_rfl).trans (hcent (Or.inr fun x hx => ?_))).trans hOK
    have hc := commutator_mem_oddCore_of_zStarAut_eq_one hY haN hα1 hx
    have hc' := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
      (le_normalizer (inv_mem hx)) hc
    rw [show x⁻¹ * ⁅a, x⁆ * x⁻¹⁻¹ = x⁻¹ * a⁻¹ * x * a by
      rw [commutatorElement_def, hainv]; group] at hc'
    exact hc'
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hone : (⟨a, haN⟩ : normalizer (Y : Set K)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
  have hord : orderOf ᾱ = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [hᾱ, ← map_pow, ← map_pow, sq, hone, map_one, map_one]
  have hα : ∀ y, ψ ⟨a, haN⟩ (ψ ⟨a, haN⟩ y) = y := fun y => by
    rw [← MulAut.mul_apply, ← map_mul, hone, map_one, MulAut.one_apply]
  set A := (W.subgroupOf (normalizer (Y : Set K))).map ψ with hA
  have hinn := inf_inner_le_oddCore_centralizer hna hα A (odd_card_map_oddCore hWN)
    (map_oddCore_commute haN) (map_oddCore_conj haN)
  rw [← hᾱ, hbal _ hord, Subgroup.map_bot] at hinn
  have hb : ∀ w (h : w ∈ W), zStarAut Y (ψ ⟨w, hWN h⟩) ∈ A.map (zStarAut Y) :=
    fun w h => ⟨ψ ⟨w, hWN h⟩, ⟨⟨w, hWN h⟩, mem_subgroupOf.mpr h, rfl⟩, rfl⟩
  have hcomm : ∀ w₁ (h₁ : w₁ ∈ W) w₂ (h₂ : w₂ ∈ W),
      zStarAut Y (ψ ⟨w₁, hWN h₁⟩) * zStarAut Y (ψ ⟨w₂, hWN h₂⟩) =
        zStarAut Y (ψ ⟨w₂, hWN h₂⟩) * zStarAut Y (ψ ⟨w₁, hWN h₁⟩) := by
    intro w₁ h₁ w₂ h₂
    set H := (A.map (zStarAut Y)).map
      (QuotientGroup.mk' (OuterAutomorphisms.inner (Y ⧸ Open.fusionZStar Y))) with hH
    have hHodd : Odd (Nat.card H) := Odd.of_dvd_nat
      (Odd.of_dvd_nat (odd_card_map_oddCore hWN) (card_map_dvd _ _)) (card_map_dvd _ _)
    have hq := hOut H hHodd _ (mem_map_of_mem _ (hb w₁ h₁)) _ (mem_map_of_mem _ (hb w₂ h₂))
    simp only [QuotientGroup.mk'_apply] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hq
    have hmem := hinn (mem_inf.mpr ⟨mul_mem (inv_mem (mul_mem (hb w₁ h₁) (hb w₂ h₂)))
      (mul_mem (hb w₂ h₂) (hb w₁ h₁)), hq⟩)
    rw [mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  have hker : ⁅W, W⁆ ≤ ((zStarAut Y).comp ψ).ker.map (normalizer (Y : Set K)).subtype := by
    rw [commutator_le]
    intro w₁ hw₁ w₂ hw₂
    refine ⟨⁅(⟨w₁, hWN hw₁⟩ : normalizer (Y : Set K)), ⟨w₂, hWN hw₂⟩⁆, ?_,
      by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm w₁ hw₁ w₂ hw₂
  rw [commutator_le]
  intro g hg y hy
  obtain ⟨n, hn, rfl⟩ := hker hg
  exact hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY n.2 (by simpa using hn) hy)

theorem core_commutator_le_of_lift (hLB : FooteLBalanceInput) {a : K} (ha : orderOf a = 2)
    {Y : Subgroup K} (hY : IsPComponent 2 Y) (hZ : Odd (Nat.card (Open.fusionZStar Y)))
    (hloc : ∀ X : Subgroup (MulAut (Y ⧸ Open.fusionZStar Y)),
      (MulAut.conj : (Y ⧸ Open.fusionZStar Y) →* MulAut (Y ⧸ Open.fusionZStar Y)).range ≤ X →
      ∀ z : X, orderOf z = 2 → pPrimeCore 2 ↥(centralizer ({z} : Set X)) = ⊥) :
    ⁅oddCoreOfCentralizer a, Y⁆ ≤ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Y.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hY
    exact h
  have hOK := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  obtain ⟨hWN, hcent⟩ := hLB K a ha Y hY
  set W := oddCoreOfCentralizer a
  by_cases hswap : conjugate Y a ≠ Y
  · exact (hcent (Or.inl hswap)).trans hOK
  have haN := mem_normalizer_of_conjugate_eq (not_not.mp hswap)
  set ψ := Y.normalizerMonoidHom
  set ᾱ := zStarAut Y (ψ ⟨a, haN⟩) with hᾱ
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  by_cases hα1 : ᾱ = 1
  · refine (hcent (Or.inr fun x hx => ?_)).trans hOK
    have hc := commutator_mem_oddCore_of_zStarAut_eq_one hY haN hα1 hx
    have hc' := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
      (le_normalizer (inv_mem hx)) hc
    rw [show x⁻¹ * ⁅a, x⁆ * x⁻¹⁻¹ = x⁻¹ * a⁻¹ * x * a by
      rw [commutatorElement_def, hainv]; group] at hc'
    exact hc'
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hone : (⟨a, haN⟩ : normalizer (Y : Set K)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
  have hord : orderOf ᾱ = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [hᾱ, ← map_pow, ← map_pow, sq, hone, map_one, map_one]
  have hα : ∀ y, ψ ⟨a, haN⟩ (ψ ⟨a, haN⟩ y) = y := fun y => by
    rw [← MulAut.mul_apply, ← map_mul, hone, map_one, MulAut.one_apply]
  set S := Y ⧸ Open.fusionZStar Y
  have hκ := mulAut_conj_injective (center_eq_bot_of_isSimpleGroup hna)
  set A := (W.subgroupOf (normalizer (Y : Set K))).map ψ with hA
  set B : Subgroup (MulAut S) := A.map (zStarAut Y) with hB
  have hBodd : Odd (Nat.card B) := Odd.of_dvd_nat (odd_card_map_oddCore hWN) (card_map_dvd _ _)
  have hBα : ∀ b ∈ B, b * ᾱ = ᾱ * b := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [hᾱ, ← map_mul, ← map_mul, map_oddCore_commute haN β hβ]
  have hBconj : ∀ s : S, ᾱ s = s → ∀ b ∈ B, MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈ B := by
    rintro s hs _ ⟨β, hβ, rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_fixed_lift_of_odd_zStar hZ hα hs
    refine ⟨MulAut.conj c * β * (MulAut.conj c)⁻¹, map_oddCore_conj haN c hc β hβ, ?_⟩
    rw [map_mul, map_mul, map_inv, zStarAut_conj]
  set Inn := (MulAut.conj : S →* MulAut S).range with hInndef
  have : Inn.Normal := ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    exact ⟨g s, mulAut_conj_map g s⟩⟩
  set D := normalizer (B : Set (MulAut S)) ⊓ centralizer ({ᾱ} : Set (MulAut S)) with hD
  set X := Inn ⊔ D with hX
  have hαD : ᾱ ∈ D := by
    refine ⟨mem_normalizer_iff.mpr fun n => ⟨fun hn => ?_, fun hn => ?_⟩,
      mem_centralizer_singleton_iff.mpr rfl⟩
    · rw [← hBα n hn, mul_inv_cancel_right]
      exact hn
    · have h := hBα _ hn
      have h' : ᾱ * n = ᾱ * (ᾱ * n * ᾱ⁻¹) := by
        rw [← h]
        group
      rw [mul_left_cancel h']
      exact hn
  have hBD : B ≤ D := fun b hb =>
    ⟨le_normalizer hb, mem_centralizer_singleton_iff.mpr (hBα b hb)⟩
  have hXn : ∀ x ∈ X, x * ᾱ = ᾱ * x → ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
    intro x hx hxα b hb
    obtain ⟨i, hi, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hx
    have hdα : d * ᾱ = ᾱ * d := mem_centralizer_singleton_iff.mp hd.2
    have hiα : i * ᾱ = ᾱ * i := by
      have h : i * ᾱ * d = ᾱ * i * d :=
        calc i * ᾱ * d = i * (ᾱ * d) := mul_assoc _ _ _
          _ = i * (d * ᾱ) := by rw [hdα]
          _ = i * d * ᾱ := (mul_assoc _ _ _).symm
          _ = ᾱ * (i * d) := hxα
          _ = ᾱ * i * d := (mul_assoc _ _ _).symm
      exact mul_right_cancel h
    obtain ⟨s, rfl⟩ := hi
    have hs : ᾱ s = s := by
      apply hκ
      rw [mulAut_conj_map, ← hiα, mul_inv_cancel_right]
    have hdb : d * b * d⁻¹ ∈ B := (mem_normalizer_iff.mp hd.1 b).mp hb
    rw [show MulAut.conj s * d * b * (MulAut.conj s * d)⁻¹ =
      MulAut.conj s * (d * b * d⁻¹) * (MulAut.conj s)⁻¹ by group]
    exact hBconj s hs _ hdb
  have hαX : ᾱ ∈ X := mem_sup_right hαD
  have hbot := hloc X le_sup_left ⟨ᾱ, hαX⟩ (by rw [Subgroup.orderOf_mk]; exact hord)
  set C := centralizer ({(⟨ᾱ, hαX⟩ : X)} : Set X) with hC
  set f : C →* MulAut S := X.subtype.comp C.subtype with hf
  have hfinj : Function.Injective f := X.subtype_injective.comp C.subtype_injective
  have hB₁N : (B.comap f).Normal := ⟨fun n hn g => by
    show f (g * n * g⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv]
    have hgα : f g * ᾱ = ᾱ * f g :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2)
    exact hXn (f g) (g : X).2 hgα _ hn⟩
  have hB₁odd : Nat.Coprime 2 (Nat.card (B.comap f)) := by
    have hdvd : Nat.card (B.comap f) ∣ Nat.card B := by
      rw [← card_map_of_injective hfinj]
      exact card_dvd_of_le (map_comap_le _ _)
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat hBodd hdvd)
  have hB₁le : B.comap f ≤ pPrimeCore 2 C := le_sSup ⟨hB₁N, hB₁odd⟩
  rw [hbot] at hB₁le
  have hBbot : ∀ b ∈ B, b = 1 := by
    intro b hb
    have hbX : b ∈ X := mem_sup_right (hBD hb)
    have hbC : (⟨b, hbX⟩ : X) ∈ C :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext (hBα b hb))
    have h1 := hB₁le (show (⟨⟨b, hbX⟩, hbC⟩ : C) ∈ B.comap f from hb)
    rw [mem_bot] at h1
    simpa using congrArg (fun z : C => ((z : X) : MulAut S)) h1
  rw [commutator_le]
  intro w hw y hy
  refine hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY (hWN hw) ?_ hy)
  exact hBbot _ ⟨ψ ⟨w, hWN hw⟩, ⟨⟨w, hWN hw⟩, mem_subgroupOf.mpr hw, rfl⟩, rfl⟩

end CFSG.ComponentClassification.Foote5
