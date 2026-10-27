module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.Exact
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSP
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4Edge
public import CFSG.ClassicalInvolution.Q3.Q3T6DSetupA
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {K : Subgroup Y}

omit [Finite Y] in
theorem isPGroup_of_oddCoreOf_eq_bot (hΦ : TypeRHyp Φ) {M : Subgroup Y} (hM : M ∈ Φ)
    (h : oddCoreOf M = ⊥) : IsPGroup 2 M :=
  (hΦ.twoGroup M hM).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq (oddCore_eq_bot_of_oddCoreIn h)).trans
      QuotientGroup.quotientBot)

theorem mem_RSet_of_oddCoreOf_eq_bot (hΦ : TypeRHyp Φ) {M : Subgroup Y} (hM : M ∈ Φ)
    (h : oddCoreOf M = ⊥) : M ∈ RSet Φ :=
  TC.mem_RSet_of_isPGroup hM (isPGroup_of_oddCoreOf_eq_bot hΦ hM h)

theorem ne_of_mem_RSet_of_le (hΦ : HypOmegaGen Φ) {T L N : Subgroup Y} (hT : T ∈ RSet Φ)
    (hTL : T ≤ L) (hL : L ∈ Φ) (hN : N ∈ Φ) (hLN : L ≠ N) : T ≠ N := by
  rintro rfl
  obtain ⟨L', -, hTL'⟩ := exists_isSylow2In_of_mem_RSet hT
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΦ hT
  exact hLN (Sec6Gen.eq_of_le_of_le hΦ hL hN hTL'.2.1 (by omega) hTL le_rfl)

theorem mem_omegaNbr_of_aViol (hΦ : TypeRHyp Φ)
    (hex : ∀ N ∈ twinOrbit Φ K, oddCoreOf N = ⊥) {M J : Subgroup Y} {zM zJ : Y}
    (hM : M ∈ twinOrbit Φ K) (hv : AViol Φ M J zM zJ) {L : Subgroup Y} (hL : L ∈ Φ)
    (hLΔ : L ∉ twinOrbit Φ K) (hLM : L ∈ omegaNbr Φ M) {J' : Subgroup Y}
    (hJ' : J' ∈ twinSet Φ J) : L ∈ omegaNbr Φ J' := by
  have hΩ := hΦ.hyp
  have hsub : twinOrbit Φ K ⊆ Φ := twinOrbit_subset hΩ.conjInvariant
  have hne : ∀ N ∈ twinOrbit Φ K, L ≠ N := fun N hN h => hLΔ (h ▸ hN)
  obtain ⟨-, -, T, hT, hTL, hTN⟩ := hLM
  obtain ⟨L', -, hTL'⟩ := exists_isSylow2In_of_mem_RSet hT
  have hT2 : IsPGroup 2 T := hTL'.2.1
  have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hT
  have hcomm : ∀ N ∈ twinOrbit Φ K, T ≤ Subgroup.normalizer (N : Set Y) → Commutes N T :=
    fun N hN hTN' => TL4.commutes_of_le_normalizer hΩ
      (mem_RSet_of_oddCoreOf_eq_bot hΦ (hsub hN) (hex N hN)) hT
      (isPGroup_of_oddCoreOf_eq_bot hΦ (hsub hN) (hex N hN)) hT2
      (ne_of_mem_RSet_of_le hΩ hT hTL hL (hsub hN) (hne N hN)).symm hTN'
  have hc1 : Commutes M T := hcomm M hM hTN
  obtain ⟨v, Ms, hVU, hVJ, -, -, htw, hvv⟩ := Q3T6D.exists_hexagon_data3 hΩ (hsub hM) hv.mem
    hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hzJ : zJ ∈ M ⊔ Ms := Q3T6D.mem_sup_of_hexagon3 hΩ hv.hzJ hVU hVJ hvv
  have hMsT : Ms ∈ twinSet Φ M := by
    rw [htw]
    exact Or.inr rfl
  have hMs : Ms ∈ twinOrbit Φ K := twinSet_subset_twinOrbit hΩ.conjInvariant hM hMsT
  have hzMs : IsUniqueInvolution Ms zM := isUniqueInvolution_of_mem_twinSet hv.hzK hMsT
  have hTz : T ≤ Subgroup.centralizer ({zM} : Set Y) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc1 zM hv.hzK.mem t ht).symm
  have hc2 : Commutes Ms T := hcomm Ms hMs
    (Sec6Gen.le_normalizer_of_le_centralizer hΩ (hsub hMs) hL (hne Ms hMs).symm hzMs hTL hT2
      (by omega) hTz)
  have hle : M ⊔ Ms ≤ Subgroup.centralizer (T : Set Y) := sup_le
    (fun m hm => Subgroup.mem_centralizer_iff.mpr fun t ht => (hc1 m hm t ht).symm)
    (fun m hm => Subgroup.mem_centralizer_iff.mpr fun t ht => (hc2 m hm t ht).symm)
  have hTzJ : T ≤ Subgroup.centralizer ({zJ} : Set Y) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hle hzJ) t ht)
  have hJ'Δ : J' ∈ twinOrbit Φ K := twinSet_subset_twinOrbit hΩ.conjInvariant
    (mem_twinOrbit_of_aViol hΩ hM hv) hJ'
  exact ⟨hL, hne J' hJ'Δ, T, hT, hTL, Sec6Gen.le_normalizer_of_le_centralizer hΩ (hsub hJ'Δ) hL
    (hne J' hJ'Δ).symm (isUniqueInvolution_of_mem_twinSet hv.hzJ hJ') hTL hT2 (by omega) hTzJ⟩

theorem mem_omegaNbr_of_mem_aStar (hΦ : TypeRHyp Φ)
    (hex : ∀ N ∈ twinOrbit Φ K, oddCoreOf N = ⊥) {L : Subgroup Y} (hL : L ∈ Φ)
    (hLΔ : L ∉ twinOrbit Φ K) {M : Subgroup Y} (hM : M ∈ twinOrbit Φ K)
    (hLM : L ∈ omegaNbr Φ M) {N : Subgroup Y} (hN : N ∈ aStar Φ M) : L ∈ omegaNbr Φ N := by
  induction hN with
  | refl => exact hLM
  | @tail A B hA hAB ih =>
    have hAΔ : A ∈ twinOrbit Φ K := aStar_subset_twinOrbit hΦ.hyp hM hA
    have hBΔ : B ∈ twinOrbit Φ K := mem_twinOrbit_of_aGraphAdj hΦ.hyp hAΔ hAB
    obtain ⟨hBΦ, ⟨zA, zB, hv⟩ | ⟨zB, zA, hv⟩ | ⟨⟨-, w, hwA, hwB⟩, -⟩⟩ := hAB
    · exact mem_omegaNbr_of_aViol hΦ hex hAΔ hv hL hLΔ ih (mem_twinSet_self hBΦ hv.hzJ)
    · exact mem_omegaNbr_of_aViol hΦ hex hAΔ (aviol_symm_of_hypOmegaGen hΦ.hyp hBΦ hv) hL hLΔ
        ih (mem_twinSet_self hBΦ hv.hzK)
    · exact Frame.TwinExitPf4.omegaNbr_of_twin hΦ.hyp hBΦ hwA hwB ih (fun h => hLΔ (h ▸ hBΔ))

theorem mem_omegaNbr_of_mem_aStar_self (hΦ : TypeRHyp Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K)
    (hex : ∀ N ∈ twinOrbit Φ K, oddCoreOf N = ⊥) {L : Subgroup Y} (hL : L ∈ Φ)
    (hLΔ : L ∉ twinOrbit Φ K) {N : Subgroup Y} (hN : N ∈ aStar Φ K) : L ∈ omegaNbr Φ N := by
  have hΩ := hΦ.hyp
  have hsub : twinOrbit Φ K ⊆ Φ := twinOrbit_subset hΩ.conjInvariant
  obtain ⟨z, hz⟩ := (hΩ.omega1 K hK).1
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hz
  obtain ⟨T, hTs, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := L) IsPGroup.of_bot bot_le
  have hT : T ∈ RSet Φ := mem_RSet_of_isSylow2In hL hTs
  obtain ⟨S, hTS⟩ := hTs.2.1.exists_le_sylow
  set P := omegaGen (aStar Φ K)
  have hS : IsSylow2In (S : Subgroup Y) ⊤ :=
    ⟨le_top, S.isPGroup', fun V _ hV hle => S.is_maximal' hV hle⟩
  have hSP : IsSylow2In ((S : Subgroup Y) ⊓ P) P :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hS (isSubnormal_omegaGen_aStar hΦ hK hA hin htw)
  obtain ⟨V, hV, hKV⟩ := IsSylow2In.exists_ge (isPGroup_of_oddCoreOf_eq_bot hΦ hK (hex K hKΔ))
    (le_omegaGen (Relation.ReflTransGen.refl : K ∈ aStar Φ K))
  obtain ⟨x, hxP, hxV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hV hSP
  have hM₁S : conjSub x K ≤ S := (conjSub_mono hKV).trans (hxV.le.trans inf_le_left)
  have hM₁A : conjSub x K ∈ aStar Φ K := (mem_conjStab_iff.mp
    (T3Core.omegaGen_aStar_le_conjStab hΩ.conjInvariant hK hxP) K).mpr
      Relation.ReflTransGen.refl
  have hM₁Δ : conjSub x K ∈ twinOrbit Φ K := aStar_subset_twinOrbit hΩ hKΔ hM₁A
  have hc : Commutes T (conjSub x K) := Q3CP.l67Gen Y Φ hΩ S T hT (conjSub x K)
    (mem_RSet_of_oddCoreOf_eq_bot hΦ (hsub hM₁Δ) (hex _ hM₁Δ)) hTS hM₁S
    (ne_of_mem_RSet_of_le hΩ hT hTs.1 hL (hsub hM₁Δ) (fun h => hLΔ (h ▸ hM₁Δ)))
  have hLM₁ : L ∈ omegaNbr Φ (conjSub x K) :=
    ⟨hL, fun h => hLΔ (h ▸ hM₁Δ), T, hT, hTs.1, AscL62.le_normalizer_of_commutes hc⟩
  exact mem_omegaNbr_of_mem_aStar hΦ hex hL hLΔ hM₁Δ hLM₁
    ((mem_aStar_symm hK hM₁A).2.trans hN)

theorem mem_omegaNbr_of_not_mem_twinOrbit (hΦ : TypeRHyp Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K)
    (hex : ∀ N ∈ twinOrbit Φ K, oddCoreOf N = ⊥) {L : Subgroup Y} (hL : L ∈ Φ)
    (hLΔ : L ∉ twinOrbit Φ K) {M : Subgroup Y} (hM : M ∈ twinOrbit Φ K) :
    L ∈ omegaNbr Φ M := by
  obtain ⟨g, J, hJ, rfl⟩ := hM
  have hL' : conjSub g⁻¹ L ∉ twinOrbit Φ K := fun h => hLΔ (by
    have := twinOrbit_conjInvariant g _ h
    rwa [conjSub_conjSub_inv] at this)
  have h1 := mem_omegaNbr_of_mem_aStar_self hΦ hK hA hin htw hex
    (hΦ.hyp.conjInvariant g⁻¹ L hL) hL' (mem_aStar_of_mem_twinSet hJ)
  have h2 := omegaNbr_conj hΦ.hyp.conjInvariant h1 g
  rwa [conjSub_conjSub_inv] at h2

omit [Finite Y] in
theorem le_normalizer_oddCoreOf {L N : Subgroup Y} (h : N ≤ Subgroup.normalizer (L : Set Y)) :
    N ≤ Subgroup.normalizer (oddCoreOf L : Set Y) := by
  intro n hn
  rw [mem_normalizer_iff_conjSub_eq, ← AscFusion.oddCoreOf_conjSub',
    mem_normalizer_iff_conjSub_eq.mp (h hn)]

theorem commutator_eq_bot_of_not_mem_twinOrbit (hF : RowCentralizerFacts) (hΦ : TypeRHyp Φ)
    (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K)
    (hO : classicalInvolutionOddCore Y = ⊥) {L : Subgroup Y} (hL : L ∈ Φ)
    (hLΔ : L ∉ twinOrbit Φ K) {M : Subgroup Y} (hM : M ∈ twinOrbit Φ K) : ⁅L, M⁆ = ⊥ := by
  have hΩ := hΦ.hyp
  have hsub : twinOrbit Φ K ⊆ Φ := twinOrbit_subset hΩ.conjInvariant
  have hex : ∀ N ∈ twinOrbit Φ K, oddCoreOf N = ⊥ := fun N hN =>
    oddCoreOf_eq_bot_of_mem_twinOrbit hF hΦ hK hA hin htw hO hN
  have hΩL : ∀ N ∈ twinOrbit Φ K, L ∈ omegaNbr Φ N := fun N hN =>
    mem_omegaNbr_of_not_mem_twinOrbit hΦ hK hA hin htw hex hL hLΔ hN
  have hnorm : ∀ N ∈ twinOrbit Φ K, N ≤ Subgroup.normalizer (L : Set Y) := by
    intro N hN
    obtain ⟨-, -, R, hR, hRN, hRL⟩ :=
      Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (hsub hN) hL (hΩL N hN)
    have hRs : IsSylow2In R N := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ (hsub hN) hR hRN
    have hNR : N = R :=
      hRs.2.2 N le_rfl (isPGroup_of_oddCoreOf_eq_bot hΦ (hsub hN) (hex N hN)) hRN
    rw [hNR]
    exact hRL
  set X := omegaGen (twinOrbit Φ K)
  have hXn : X.Normal := omegaGen_normal twinOrbit_conjInvariant
  have hXL : X ≤ Subgroup.normalizer (oddCoreOf L : Set Y) :=
    le_normalizer_oddCoreOf (iSup₂_le fun N hN => hnorm N hN)
  have hMX : M ≤ X := le_omegaGen hM
  have hOX : Balance.oddCoreIn X = ⊥ := oddCoreIn_eq_bot (TL4.oddCore_eq_bot_of_normal hO hXn)
  have hle : oddCoreOf L ⊓ X ≤ Balance.oddCoreIn X := by
    refine Balance.le_oddCoreIn_of_normalizes inf_le_right (fun x hx => ?_)
      ((Balance.odd_card_oddCoreIn L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_inf]
    rw [(Subgroup.mem_normalizer_iff.mp (hXL hx) y),
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y)]
  have h3 : ⁅oddCoreOf L, M⁆ = ⊥ := by
    rw [eq_bot_iff, ← hOX]
    refine le_trans ?_ hle
    rw [Subgroup.commutator_le]
    intro a ha m hm
    refine ⟨?_, ?_⟩
    · have h1 : m * a⁻¹ * m⁻¹ ∈ oddCoreOf L :=
        (Subgroup.mem_normalizer_iff.mp (hXL (hMX hm)) a⁻¹).mp ((oddCoreOf L).inv_mem ha)
      have h2 : ⁅a, m⁆ = a * (m * a⁻¹ * m⁻¹) := by rw [commutatorElement_def]; group
      rw [h2]
      exact (oddCoreOf L).mul_mem ha h1
    · have h1 : a * m * a⁻¹ ∈ X := hXn.conj_mem m (hMX hm) a
      have h2 : ⁅a, m⁆ = (a * m * a⁻¹) * m⁻¹ := by rw [commutatorElement_def]
      rw [h2]
      exact X.mul_mem h1 (X.inv_mem (hMX hm))
  obtain ⟨-, hLM, T, hT, hTL, hTN⟩ := hΩL M hM
  have hTs : IsSylow2In T L := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hL hT hTL
  have hM2 : IsPGroup 2 M := isPGroup_of_oddCoreOf_eq_bot hΦ (hsub hM) (hex M hM)
  obtain ⟨hv1, hv2⟩ := hΩ.omega4 M (hsub hM) L hL hLM.symm
  have hMTle : ⁅M, T⁆ ≤ M ⊓ L := by
    rw [Subgroup.commutator_le]
    intro m hm t ht
    refine ⟨?_, ?_⟩
    · have h1 : t * m⁻¹ * t⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.mp (hTN ht) m⁻¹).mp (M.inv_mem hm)
      have h2 : ⁅m, t⁆ = m * (t * m⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
      rw [h2]
      exact M.mul_mem hm h1
    · have h1 : m * t * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hnorm M hM hm) t).mp (hTL ht)
      have h2 : ⁅m, t⁆ = (m * t * m⁻¹) * t⁻¹ := by rw [commutatorElement_def]
      rw [h2]
      exact L.mul_mem h1 (L.inv_mem (hTL ht))
  rcases Nat.lt_or_ge (padicValNat 2 (Nat.card ↥(M ⊓ L))) 1 with hlt | hge
  ·
    have hML : M ⊓ L = ⊥ := by
      obtain ⟨k, hk⟩ := (hM2.to_le (inf_le_left : M ⊓ L ≤ M)).exists_card_eq
      rw [hk, padicValNat.prime_pow] at hlt
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hMT : ⁅M, T⁆ = ⊥ := le_bot_iff.mp (hML ▸ hMTle)
    have hLC : L ≤ Subgroup.centralizer (M : Set Y) := by
      rw [eq_oddCoreOf_sup_of_isPGroup_quotient (hΦ.twoGroup L hL) hTs]
      exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
        (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMT))
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC
  ·
    have h1 := hv2 (le_antisymm hv1 hge)
    rw [hex M hM, bot_inf_eq, le_bot_iff] at h1
    rw [Subgroup.commutator_comm]
    exact h1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3
