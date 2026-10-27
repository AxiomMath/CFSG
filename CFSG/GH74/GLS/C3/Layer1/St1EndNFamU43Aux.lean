module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL43Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.U43

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LieType.Multipliers.U43 (F9)
open scoped commutatorElement

theorem hudF9 : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num⟩

abbrev PU43 : Type := primeFormP hudF9 ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)

theorem aut_odd_inner_u43 (τ : MulAut PU43) (hτ : Odd (orderOf τ)) :
    τ ∈ (MulAut.conj : PU43 →* MulAut PU43).range := by
  have hn : 3 ≤ 4 := by norm_num
  have hq : ¬(4 = 3 ∧ 3 ^ 1 = 2) := by decide
  have hout := (unitary_full_diagonal_outer_order hudF9 hn hq).2.2.2.1
  have hfin : Finite (MulAut PU43) :=
    Finite.of_injective (fun f : MulAut PU43 => (f : PU43 → PU43)) DFunLike.coe_injective
  have h8 : Nat.card (Outer PU43) = 8 := by
    rw [hout]; norm_num
  set τ' : Outer PU43 := QuotientGroup.mk τ
  have hfin' : Finite (Outer PU43) := Quotient.finite _
  have h1 : orderOf τ' ∣ 8 := h8 ▸ orderOf_dvd_natCard τ'
  have h2 : orderOf τ' ∣ orderOf τ := orderOf_map_dvd (QuotientGroup.mk' (inner PU43)) τ
  have h3 : Odd (orderOf τ') := Odd.of_dvd_nat hτ h2
  have h4 : orderOf τ' = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf τ' ∣ 2 ^ 3 by simpa using h1)
    rcases k with _ | k
    · simpa using hk
    · exfalso
      rw [hk] at h3
      exact (Nat.not_even_iff_odd.2 h3) (by rw [pow_succ]; exact even_two.mul_left _)
  have h5 : τ' = 1 := orderOf_eq_one_iff.1 h4
  exact (QuotientGroup.eq_one_iff τ).1 h5


end CFSG.GH74.GLS.C3.Layer1.EndN.U43

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 CFSG.GH74.GLS.C3.Layer1.EndN.L43
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Multipliers.U43 (F9)
open scoped commutatorElement

theorem lem711_u43_aux
    (hrowS : ∀ {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X},
        Lem711Cfg X L K x y → LieModel ↥L .PSU 4 3 1 →
        ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 9 ∧ Nonempty (↥K ≃* projectiveSL 2 E))
    (zS : PU43) (hz5 : orderOf zS = 5)
    (hwit : ∀ α : MulAut PU43, α * α = 1 → α zS = zS →
      ∃ g, α g = g ∧ Even (orderOf (zS * (g * zS * g⁻¹)))) :
    Lem711Empty (fun X _ => LieModel X .PSU 4 3 1) := by
  intro X _ _ L K x y h hL
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hL
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hst
  have : Fintype F := Fintype.ofFinite F
  have hFF9 : Fintype.card F = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hF, F9.card_eq]; norm_num
  let ι : F ≃+* F9 := FiniteField.ringEquivOfCardEq hFF9
  let e2 := e.trans (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv ι 4 (3 ^ 1))
  obtain ⟨eT⟩ := nonempty_primeFormP_mulEquiv hudF9 (isPrimeFormGram_one (n := 4) (K := F9))
  let eP : ↥L ≃* PU43 := (e2.trans (unitaryPSUEquiv hudF9 (by norm_num)).symm).trans eT.symm
  have hLn := h.normal
  have hZP : center PU43 = ⊥ := by
    rw [← Subgroup.map_center_eq eP, h.center_L_eq_bot, Subgroup.map_bot]
  obtain ⟨ρ, hρinj, hρW, -, hρconj⟩ := CFSG.ComponentClassification.OutcomeLocal.socle_extension
    (W := L) h.centralizer_eq_bot eP hZP
  obtain ⟨E, _, _, hE9, ⟨eK⟩⟩ := hrowS h hL
  obtain ⟨w, hwO, h5w⟩ := lem711_l43_five h hE9 eK
  have hP : ¬ 25 ∣ Nat.card PU43 := by
    have hst' := CFSG.GH74.Generic.stated_of_lieModel_PSU hL
    obtain ⟨h1, -⟩ := unitary_model_outer_two_part_bound ↥L 4 3 1 hst'
    have hcard : Nat.card ↥L = 3265920 := by
      have h2 : (Nat.card ↥L : ℤ) = 3265920 := by
        have h3 : (Nat.gcd 4 (3 ^ 1 + 1) : ℤ) = 4 := by norm_num
        rw [h3] at h1
        have h4 : (Nat.card ↥L : ℤ) * 4 = 13063680 := by
          rw [h1]
          norm_num [Finset.prod_Icc_succ_top]
        omega
      exact_mod_cast h2
    rw [← Nat.card_congr eP.toEquiv, hcard]
    norm_num
  set O := pPrimeCoreOf 2 (centralizer ({y} : Set X)) with hO
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h.hy, pow_two] at this
  have hwy : w ∈ centralizer ({y} : Set X) := (TwoThin.pPrimeCoreOf_le _) hwO
  set z0 : X := w ^ (orderOf w / 5) with hz0
  have hz0O : z0 ∈ O := pow_mem hwO _
  have hz0ord : orderOf z0 = 5 := orderOf_pow_orderOf_div (orderOf_pos w).ne' h5w
  have hz0y : y * z0 = z0 * y := by
    have h1 : w * y = y * w := mem_centralizer_singleton_iff.1 hwy
    exact ((Commute.pow_right (show Commute y w from h1.symm) _).eq)
  have hρz0 : ρ z0 ∈ (MulAut.conj : PU43 →* MulAut PU43).range := by
    refine aut_odd_inner_u43 (ρ z0) ?_
    have : orderOf (ρ z0) ∣ 5 := hz0ord ▸ orderOf_map_dvd ρ z0
    exact Odd.of_dvd_nat (by decide) this
  obtain ⟨ζ, hζ⟩ := hρz0
  let ℓ0 : ↥L := eP.symm ζ
  have hℓ0 : ((ℓ0 : ↥L) : X) = z0 := by
    apply hρinj
    rw [hρW ℓ0]
    simp [ℓ0, hζ]
  have hζord : orderOf ζ = 5 := by
    have h1 : orderOf (eP ℓ0) = orderOf ℓ0 := MulEquiv.orderOf_eq eP ℓ0
    have h2 : orderOf ((ℓ0 : ↥L) : X) = orderOf ℓ0 := Subgroup.orderOf_coe ℓ0
    have h3 : eP ℓ0 = ζ := by simp [ℓ0]
    rw [← h3, h1, ← h2, hℓ0, hz0ord]
  obtain ⟨s, i, hs⟩ := exists_conj_pow_of_order_five hP hζord hz5
  have hρyζ : ρ y ζ = ζ := by
    have h1 := hρconj y ℓ0
    have h2 : eP ℓ0 = ζ := by simp [ℓ0]
    rw [h2] at h1
    rw [h1]
    have : MulAut.conjNormal y ℓ0 = ℓ0 := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hℓ0]
      calc y * z0 * y⁻¹ = (z0 * y) * y⁻¹ := by rw [hz0y]
        _ = z0 := by group
    rw [this]
    simp [ℓ0]
  let α : MulAut PU43 := MulAut.conj s * ρ y * (MulAut.conj s)⁻¹
  have hαα : α * α = 1 := by
    have h1 : ρ y * ρ y = 1 := by rw [← map_mul, hyy, map_one]
    calc α * α = MulAut.conj s * (ρ y * ρ y) * (MulAut.conj s)⁻¹ := by simp only [α]; group
      _ = 1 := by rw [h1]; group
  have hconjinv : (MulAut.conj s : MulAut PU43)⁻¹ = MulAut.conj s⁻¹ :=
    (map_inv (MulAut.conj : PU43 →* MulAut PU43) s).symm
  have hαz : α zS = zS := by
    have hρyζi : ρ y (ζ ^ i) = ζ ^ i := by
      rw [map_zpow, hρyζ]
    have h1 : α (s * ζ ^ i * s⁻¹) = s * ζ ^ i * s⁻¹ := by
      show (MulAut.conj s * ρ y * (MulAut.conj s)⁻¹) (s * ζ ^ i * s⁻¹) = _
      rw [MulAut.mul_apply, MulAut.mul_apply, hconjinv, MulAut.conj_apply, MulAut.conj_apply]
      have : s⁻¹ * (s * ζ ^ i * s⁻¹) * s⁻¹⁻¹ = ζ ^ i := by group
      rw [this, hρyζi]
    rwa [hs] at h1
  obtain ⟨g, hαg, hev⟩ := hwit α hαα hαz
  set g₁ : PU43 := s⁻¹ * g * s with hg₁
  have hρyg₁ : ρ y g₁ = g₁ := by
    have h1 : (MulAut.conj s * ρ y * (MulAut.conj s)⁻¹) g = g := hαg
    rw [MulAut.mul_apply, MulAut.mul_apply, hconjinv, MulAut.conj_apply, MulAut.conj_apply] at h1
    have h2 : ρ y (s⁻¹ * g * s⁻¹⁻¹) = s⁻¹ * g * s⁻¹⁻¹ := by
      have := congrArg (fun t => s⁻¹ * t * s) h1
      calc ρ y (s⁻¹ * g * s⁻¹⁻¹) = s⁻¹ * (s * ρ y (s⁻¹ * g * s⁻¹⁻¹) * s⁻¹) * s := by group
        _ = s⁻¹ * g * s := this
        _ = s⁻¹ * g * s⁻¹⁻¹ := by group
    simpa [hg₁] using h2
  let gL : ↥L := eP.symm g₁
  have hgL : ((gL : ↥L) : X) * y = y * ((gL : ↥L) : X) := by
    have h1 := hρconj y gL
    have h2 : eP gL = g₁ := by simp [gL]
    rw [h2, hρyg₁] at h1
    have h3 : MulAut.conjNormal y gL = gL := by
      apply eP.injective
      rw [← h1, h2]
    have h4 := congrArg Subtype.val h3
    rw [MulAut.conjNormal_apply] at h4
    calc ((gL : ↥L) : X) * y = (y * ((gL : ↥L) : X) * y⁻¹) * y := by rw [h4]
      _ = y * ((gL : ↥L) : X) := by group
  have hgC : ((gL : ↥L) : X) ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.2 hgL
  have ha₁ : ((eP.symm (ζ ^ i) : ↥L) : X) = z0 ^ i := by
    rw [map_zpow]
    change (((eP.symm ζ) ^ i : ↥L) : X) = z0 ^ i
    rw [Subgroup.coe_zpow]
    change (((ℓ0 : ↥L) : X)) ^ i = z0 ^ i
    rw [hℓ0]
  have ha₁O : ((eP.symm (ζ ^ i) : ↥L) : X) ∈ O := by rw [ha₁]; exact zpow_mem hz0O i
  have hb₁O : ((gL : ↥L) : X) * ((eP.symm (ζ ^ i) : ↥L) : X) * ((gL : ↥L) : X)⁻¹ ∈ O :=
    TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (Subgroup.le_normalizer hgC) ha₁O
  have hprodO := O.mul_mem ha₁O hb₁O
  have hodd := odd_orderOf_of_mem_pPrimeCoreOf hprodO
  have hζi : ζ ^ i = s⁻¹ * zS * s := by
    rw [← hs]; group
  have hprod : ((eP.symm (ζ ^ i) : ↥L) : X) * (((gL : ↥L) : X) * ((eP.symm (ζ ^ i) : ↥L) : X) * ((gL : ↥L) : X)⁻¹) =
      ((eP.symm (s⁻¹ * (zS * (g * zS * g⁻¹)) * s) : ↥L) : X) := by
    have h1 : s⁻¹ * (zS * (g * zS * g⁻¹)) * s = ζ ^ i * (g₁ * ζ ^ i * g₁⁻¹) := by
      rw [hζi, hg₁]; group
    rw [h1, map_mul, map_mul, map_mul, map_inv]
    simp [gL]
  have horder : orderOf (((eP.symm (s⁻¹ * (zS * (g * zS * g⁻¹)) * s) : ↥L) : X)) =
      orderOf (zS * (g * zS * g⁻¹)) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    have := MulEquiv.orderOf_eq (MulAut.conj s⁻¹ : PU43 ≃* PU43) (zS * (g * zS * g⁻¹))
    rw [MulAut.conj_apply] at this
    simpa using this
  rw [hprod, horder] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) hev

end CFSG.GH74.GLS
