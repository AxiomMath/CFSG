module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.QPlusPieces
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.QPlusCommute
public import CFSG.LieType.Steinberg.TwistedD4.Weyl
public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import Certificates.Certificate117
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PlaneAbstract
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2OddQPlusAll
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Sup
public import CFSG.RankThree.PartOne.SEITZ3.PlanePair
import CFSG.GH74.Filter.Lie.TwistedE6Odd
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenAPI

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal

theorem exists_sl2_orderOf (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpq : p ∣ Nat.card F + 1) : ∃ M : Matrix.SpecialLinearGroup (Fin 2) F, orderOf M = p := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [card_specialLinearGroup_fin_two]
    refine Dvd.dvd.mul_left ?_ _
    have : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      zify [hq, Nat.one_le_pow 2 _ hq]
      ring
    rw [this]
    exact Dvd.dvd.mul_right hpq _
  exact exists_prime_orderOf_dvd_card' p hdvd

section Ambient

variable {K : Type} [Field K]

theorem slLong_coe_mem_central (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    (A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    (slLong σ hσ A : adjointGroup d4 K) ∈
      rootGroup (rootOperatorFamily d4) K (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) ⊔
        rootGroup (rootOperatorFamily d4) K (-Pi.single (nd 2) 1 : Fin d4.rank → ℤ) := by
  rw [slLong_val]
  simp only [slLongE, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact Subtype.property _

theorem slShort_coe_mem_outer (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (slShort σ hσ A : adjointGroup d4 K) ∈ (outerRankOne : Subgroup (adjointGroup d4 K)) := by
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, phiShortTw_val,
    phiShort_apply]
  set y := (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm A with hy
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact rankOne_zero_le_outer y.2
  · exact rankOne_one_le_outer (twistC_mem_rankOne_zero σ y.2)
  · exact rankOne_three_le_outer (twistC_twistC_mem_rankOne_zero σ y.2)

theorem sl_map_injective {F K : Type} [Field F] [Field K] (f : F →+* K) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) :=
  CFSG.GH74.Filter.Lie.sl2_map_injective f

theorem sq_eq_one_of_mem_center {K : Type} [Field K]
    {L : Matrix.SpecialLinearGroup (Fin 2) K}
    (hL : L ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) : L ^ 2 = 1 := by
  obtain ⟨r, hr, hrL⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hL
  simp only [Fintype.card_fin] at hr
  refine Subtype.ext ?_
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hrL, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal]
  have : r * r = 1 := by rw [← pow_two]; exact hr
  simp [this]

open Subgroup CFSG.GH74.GLS.Stage4.Hex in
theorem closure_cenGen_twistedGroup_qplus [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) (hqodd : Odd q)
    {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ q + 1)
    (hshape : SylowShape p 2 e (twistedGroup σ.toRingHom))
    (F : Subgroup (twistedGroup σ.toRingHom)) (hFp : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) : Subgroup.closure (cenGen F) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hσ3' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have hcardF : Nat.card (fixedField σ.toRingHom) = q :=
    card_fixedField_of_cube σ.toRingHom hq hK hσq
  have hcardX : Nat.card (fixSubfield σ) = q := hcardF
  obtain ⟨M, hM⟩ := exists_sl2_orderOf (fixedField σ.toRingHom) (p := p)
    (by rw [hcardF]; exact hpq)
  let nh : twistedGroup σ.toRingHom := nHat σ.toRingHom (ng 0) * nHat σ.toRingHom (ng 1)
  let b : twistedGroup σ.toRingHom := slLong σ.toRingHom hσ3' M
  let b₀ : twistedGroup σ.toRingHom := nh * b * nh⁻¹
  let L : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M
  let v : twistedGroup σ.toRingHom := slShort σ.toRingHom hσ3' L
  have hLfix : Matrix.SpecialLinearGroup.map σ.toRingHom L = L := by
    refine Subtype.ext ?_
    ext i j
    simp only [L, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (M.1 i j).2
  have hnhJ : nh ∈ FixedSub σ :=
    mul_mem (nHat_zero_mem_FixedSub σ hσ3) (nHat_one_mem_FixedSub σ hσ3)
  have hbJ : b ∈ FixedSub σ := slLong_mem_FixedSub σ hσ3 M
  have hb₀J : b₀ ∈ FixedSub σ := mul_mem (mul_mem hnhJ hbJ) (inv_mem hnhJ)
  have hvJ : v ∈ FixedSub σ := slShort_mem_FixedSub σ hσ3 L hLfix
  have hob : orderOf b = p := by
    rw [orderOf_injective (slLong σ.toRingHom hσ3') (slLong_injective hσ3') M, hM]
  have hob₀ : orderOf b₀ = p := by
    have := orderOf_injective (MulAut.conj nh).toMonoidHom (MulAut.conj nh).injective b
    rw [← hob]
    exact this
  have hoL : orderOf L = p := by
    rw [orderOf_injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (fixedField σ.toRingHom).subtype) (sl_map_injective _) M, hM]
  have hov : orderOf v = p := by
    rw [orderOf_injective (slShort σ.toRingHom hσ3') (slShort_injective hσ3') L, hoL]
  have hb₀theta : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      (thetaGroup : Subgroup (adjointGroup d4 K)) := by
    have e : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        (nHatE K (ng 0) * nHatE K (ng 1)) * (b : adjointGroup d4 K) *
          (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ := by
      have hn0 : (nHat σ.toRingHom (ng 0) : adjointGroup d4 K) = nHatE K (ng 0) := nHat_val _ _
      have hn1 : (nHat σ.toRingHom (ng 1) : adjointGroup d4 K) = nHatE K (ng 1) := nHat_val _ _
      simp only [b₀, nh, Subgroup.coe_mul, Subgroup.coe_inv, hn0, hn1, mul_assoc, mul_inv_rev]
    rw [e]
    exact conj_mem_thetaGroup (slLong_coe_mem_central σ.toRingHom hσ3' M)
  have hAb : ∀ a ∈ (slShort σ.toRingHom hσ3').range, a * b₀ = b₀ * a := by
    rintro _ ⟨B, rfl⟩
    refine Subtype.ext ?_
    exact (commute_thetaGroup_outerRankOne hb₀theta
      (slShort_coe_mem_outer σ.toRingHom hσ3' B)).eq.symm
  have hcomm : Commute b₀ v := (hAb v ⟨L, rfl⟩).symm
  have hnot : v ∉ zpowers b₀ := by
    intro hv'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hv'
    have hLc : L ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply slShort_injective hσ3'
      rw [map_mul, map_mul]
      have h1 : Commute b₀ (slShort σ.toRingHom hσ3' B) := (hAb _ ⟨B, rfl⟩).symm
      have h2 := (h1.zpow_left i).eq
      rw [hi] at h2
      exact h2.symm
    have h2 := sq_eq_one_of_mem_center hLc
    have h3 : orderOf L ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hoL] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  obtain ⟨E₀, hbE, hvE, hE₀p, hE₀c, hE₀le⟩ := exists_plane_of_commute hob₀ hov hcomm hnot
  have hE₀J : E₀ ≤ FixedSub σ := hE₀le _ hb₀J hvJ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    have h1 : p ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have h2 : 3 ≤ Nat.card (fixSubfield σ) := by omega
    have : Finite (fixSubfield σ) := inferInstance
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast h2
  let ε : ↥(FixedSub σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (fixedSubEquivJ σ hK2 hq hK hσq hσ3).trans (trialityFieldImageEquivG2 σ hk3)
  have hJgen : Subgroup.closure (cenGen (E₀.subgroupOf (FixedSub σ))) = ⊤ := by
    refine closure_cenGen_eq_top_of_map ε _ ?_
    refine closure_cenGen_adjointG2_odd_qplus_eq_top_all (fixSubfield σ)
      (by rw [hcardX]; exact hqodd) hp hp5 (by rw [hcardX]; exact hpq) _ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow]
      have : y ^ p = 1 := Subtype.ext (hE₀p _ hy)
      rw [this, map_one]
    · rw [Subgroup.card_map_of_injective ε.injective, ← hE₀c]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀J).toEquiv
  have hJA : FixedSub σ ⊔ (slShort σ.toRingHom hσ3').range = ⊤ := by
    have h := CFSG.ClassicalInvolution.G2D4Models.range_slLong_sup_range_slShort hσ3'
    rw [eq_top_iff, ← h]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨A, rfl⟩
    exact slLong_mem_FixedSub σ hσ3 A
  refine closure_cenGen_eq_top_of_subgroup_centralizer hshape (FixedSub σ)
    (slShort σ.toRingHom hσ3').range E₀ hE₀p hE₀c hJgen b₀ hbE ?_ hAb hJA F hFp hFc
  intro h1
  rw [h1, orderOf_one] at hob₀
  exact hp.one_lt.ne hob₀

end Ambient

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
