module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped commutatorElement

section Levi

variable {K F : Type} [Field K] [Field F] [CharP K 2] {N ε : ℕ} {hε : ε ≤ 1}
  {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem perfectCore_centralizer_ctuEmbed_rootTorus_le (hK : 4 ≤ Nat.card K) (l : Fin N) :
    perfectCore (centralizer (((rootTorusSp K l).map (ctuEmbed ε hε σ ι hι) :
      Subgroup (SU σ (2 * N + ε))) : Set (SU σ (2 * N + ε)))) ≤
        ctuBlock σ ε ({l} : Finset (Fin N)) := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  set C := centralizer (((rootTorusSp K l).map (ctuEmbed ε hε σ ι hι) :
    Subgroup (SU σ (2 * N + ε))) : Set (SU σ (2 * N + ε))) with hC
  refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1).trans ?_
  rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero,
    Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hc : ⁅g₁, g₂⁆ ∈ C := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have hsupp : ∀ x ∈ C, ∀ a b, a ≠ b → (a ∈ ctuPlanes ε ({l} : Finset (Fin N)) ∨
      b ∈ ctuPlanes ε ({l} : Finset (Fin N))) →
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b = 0 := by
    intro x hx a b hab hl
    have hcomm := mem_centralizer_iff.1 hx (ctuEmbed ε hε σ ι hι
      (rootTorusHom K N l κ)) ⟨_, ⟨κ, rfl⟩, rfl⟩
    exact ctua_apply_eq_zero_of_commute_rootTorus hκ hcomm hab hl
  set a₀ := ctuCoord N ε (Sum.inl (Sum.inl l)) with ha₀def
  have ha₀ : a₀ ∈ ctuPlanes ε ({l} : Finset (Fin N)) := by
    rw [ha₀def, ctuCoord_mem_ctuPlanes]
    simp
  have hmul : ∀ x ∈ C, ∀ y : SU σ (2 * N + ε),
      (((x * y : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ =
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ *
        ((y : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ := by
    intro x hx y
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a₀]
    · intro b _ hb
      rw [hsupp x hx a₀ b (Ne.symm hb) (Or.inl ha₀), zero_mul]
    · simp
  have hinv : ∀ x ∈ C,
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ *
        (((x⁻¹ : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ = 1 := by
    intro x hx
    rw [← hmul x hx x⁻¹, mul_inv_cancel]
    exact one_apply_eq a₀
  have hχ : (((⁅g₁, g₂⁆ : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀ = 1 := by
    rw [commutatorElement_def, hmul _ (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)),
      hmul _ (mul_mem hg₁ hg₂), hmul _ hg₁]
    calc _ = (((g₁ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
            a₀ a₀ * (((g₁⁻¹ : SU σ (2 * N + ε)) :
              GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀) *
          (((g₂ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
            a₀ a₀ * (((g₂⁻¹ : SU σ (2 * N + ε)) :
              GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a₀ a₀) := by
          ring
      _ = 1 := by rw [hinv _ hg₁, hinv _ hg₂, one_mul]
  rw [mem_ctuBlock]
  intro a b hab
  by_cases h : a = b
  · subst h
    have ha : a ∈ ctuPlanes ε ({l} : Finset (Fin N)) := hab.elim id id
    rcases eq_or_eq_of_mem_ctuPlanes_singleton ha with rfl | rfl
    · rw [hχ, one_apply_eq]
    · have hu := sum_mat_mul_mat (⁅g₁, g₂⁆ : SU σ (2 * N + ε)) a₀ (Fin.rev a₀)
      rw [Finset.sum_eq_single a₀, ite_eq_left rfl] at hu
      · rw [mat_apply, hχ, map_one, one_mul, ha₀def, ctuCoord_rev hε, ctuPar_inl, par_inl] at hu
        rw [hu, one_apply_eq]
      · intro t _ ht
        change σ (((⁅g₁, g₂⁆ : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) t a₀) * _ = 0
        rw [hsupp _ hc t a₀ ht (Or.inr ha₀), map_zero, zero_mul]
      · simp
  · rw [one_apply_ne h]
    exact hsupp _ hc a b h hab

end Levi

section Std

variable {K F : Type} [Field K] [Field F] [Finite F] [CharP F 2] [CharP K 2] {f N ε : ℕ}

theorem ctuBlock_le_perfectCore_centralizer_ctuEmbed_rootTorus (hF : Nat.card F = (2 ^ f) ^ 2)
    (hε : ε ≤ 1) {ι : K →+* F} (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) {l : Fin N}
    (h3 : 3 ≤ 2 * ({l} : Finset (Fin N))ᶜ.card + ε)
    (hq : ¬(2 * ({l} : Finset (Fin N))ᶜ.card + ε = 3 ∧ 2 ^ f = 2)) :
    ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)) ≤
      perfectCore (centralizer (((rootTorusSp K l).map
        (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) :
          Subgroup (SU (unitaryInvolution F 2 f) (2 * N + ε))) :
            Set (SU (unitaryInvolution F 2 f) (2 * N + ε)))) := by
  refine le_perfectCore_of_perfect ?_ (commutator_ctuBlock_eq hF hε h3 hq)
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hyl : y ∈ spBlock K ({l} : Finset (Fin N)) := by
    rw [spBlock_singleton]
    exact rootTorusSp_le_longRootSp2 l hy
  exact (commute_ctuBlock_ctuEmbed hx hyl).symm

theorem perfectCore_centralizer_ctuEmbed_rootTorus_eq (hF : Nat.card F = (2 ^ f) ^ 2)
    (hε : ε ≤ 1) {ι : K →+* F} (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c)
    (hK : 4 ≤ Nat.card K) {l : Fin N} (h3 : 3 ≤ 2 * ({l} : Finset (Fin N))ᶜ.card + ε)
    (hq : ¬(2 * ({l} : Finset (Fin N))ᶜ.card + ε = 3 ∧ 2 ^ f = 2)) :
    perfectCore (centralizer (((rootTorusSp K l).map
      (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) :
        Subgroup (SU (unitaryInvolution F 2 f) (2 * N + ε))) :
          Set (SU (unitaryInvolution F 2 f) (2 * N + ε)))) =
      ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)) :=
  le_antisymm (perfectCore_centralizer_ctuEmbed_rootTorus_le hK l)
    (ctuBlock_le_perfectCore_centralizer_ctuEmbed_rootTorus hF hε hι h3 hq)

omit [CharP F 2] [CharP K 2] in
theorem natCard_ctuBlock_zero_two [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))) =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
  rw [Nat.card_congr (ctuBlockEquiv (unitaryInvolution F 2 f) le_rfl (0 : Fin (1 + 1))).toEquiv]
  exact CFSG.LieType.Steinberg.card_SU_three (p := 2) hF

omit [CharP K 2] in
theorem natCard_map_ctuBlock_zero_two (hF : Nat.card F = (2 ^ f) ^ 2) {E : Type*} [Group E]
    {Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* E}
    (hker : Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1))) :
    Nat.card ((ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ) =
      Nat.card (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))) := by
  have hinj : Function.Injective
      (Φ.comp (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).subtype) := by
    intro x y hxy
    exact Subtype.ext (injOn_ctuBlock_of_ker_le_center (p := 2) hF (by norm_num)
      (fun h => by have := (Prod.mk.inj h).1; omega) hker (Finset.mem_singleton_self 0)
      x.2 y.2 hxy)
  have hr : (Φ.comp (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).subtype).range =
      (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end Std

section Tw

variable {K F : Type} [Field K] [Field F] [Finite F] [CharP F 2] [CharP K 2] {f : ℕ}

omit [Finite F] [CharP F 2] in
theorem ctuEmbed_tauSp_rootTorusHom_zero {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}
    (κ : Kˣ) : ctuEmbed 1 le_rfl σ ι hι (tauSp (rootTorusHom K 2 0 κ)) =
      ctuEmbed 1 le_rfl σ ι hι (diagSp K 2 ![κ, κ]) := by
  rw [tauSp_rootTorusHom_zero]

theorem rankOne_zero_le_perfectCore_centralizer_twTorus (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) {ι : K →+* F} (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) :
    rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) (2 * 2 + 1))
        (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) ≤
      perfectCore (centralizer ((((rootTorusSp K 0).map tauSp).map
        (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι) :
          Subgroup (SU (unitaryInvolution F 2 f) (2 * 2 + 1))) :
            Set (SU (unitaryInvolution F 2 f) (2 * 2 + 1)))) := by
  refine le_perfectCore_of_perfect ?_
    (Subgroup.isPerfect_iff.1 (isPerfect_rankOne hF hf (n := 2 * 2 + 1) (by norm_num) _))
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨y, ⟨κ, rfl⟩, rfl⟩, rfl⟩
  rw [ctuEmbed_tauSp_rootTorusHom_zero]
  exact (commute_rankOne_short_ctuEmbed_diagSp (N := 2) (ε := 1) (hε := le_rfl)
    (j := ⟨0, by norm_num⟩) (by norm_num) (t := ![κ, κ]) rfl hx).symm

omit [CharP K 2] in
theorem natCard_map_rankOne_zero (hF : Nat.card F = (2 ^ f) ^ 2) {E : Type*} [Group E]
    {Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* E}
    (hker : Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1))) :
    Nat.card ((rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2))).map Φ) =
        Nat.card (SpecialLinearGroup (Fin 2) F) := by
  set R := rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
    (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) with hR
  set eR := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := unitaryInvolution_involutive hF)
    (n := 2 * 2 + 1) (k := ⟨0, by norm_num⟩) (by norm_num) with heR
  have hinj : Function.Injective (Φ.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) ∈
        center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) := hker hx
    have hex : eR x ∈ center (SpecialLinearGroup (Fin 2) F) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eR.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_center_iff.1 hxc y)
    rw [center_SL_two_eq_bot_of_charTwo, mem_bot] at hex
    exact eR.injective (hex.trans (map_one eR).symm)
  have hr : (Φ.comp R.subtype).range = R.map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr eR.toEquiv

end Tw

theorem sq_add_one_dvd_ordSL_two_sq (q : ℕ) : q ^ 2 + 1 ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ _
  obtain ⟨a, ha⟩ : ∃ a, a = q ^ 2 := ⟨_, rfl⟩
  rw [← ha]
  rcases a with _ | b
  · simp
  · exact ⟨b, Nat.sub_eq_of_eq_add (by ring)⟩

theorem not_sq_add_one_dvd_card_SU_three {q : ℕ} (hq2 : 2 ∣ q) (hq : 2 ≤ q) :
    ¬ q ^ 2 + 1 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  intro h
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hmq : Nat.Coprime (q ^ 2 + 1) q := by
    rw [show q ^ 2 + 1 = 1 + q * q by ring, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left q
  have hodd : Odd (q ^ 2 - 1) := by
    have hev : Even (q ^ 2) := Nat.even_pow.2 ⟨even_iff_two_dvd.2 hq2, two_ne_zero⟩
    exact Nat.Even.sub_odd hq1 hev odd_one
  have hm1 : Nat.Coprime (q ^ 2 + 1) (q ^ 2 - 1) := by
    rw [show q ^ 2 + 1 = 2 + (q ^ 2 - 1) * 1 by omega, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_two_left.2 hodd
  have h3 : q ^ 2 + 1 ∣ q ^ 3 + 1 :=
    (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hmq) hm1).dvd_of_dvd_mul_left h
  have h4 : q ^ 2 + 1 ∣ q * (q ^ 2 + 1) - (q ^ 3 + 1) := Nat.dvd_sub (dvd_mul_left _ q) h3
  rw [show q * (q ^ 2 + 1) = q ^ 3 + q by ring, Nat.add_sub_add_left] at h4
  have := Nat.le_of_dvd (by omega) h4
  omega

end CFSG.SeitzReduction.SymplecticPilot
