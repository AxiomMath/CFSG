module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.FourUGeneric
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6LocalCore
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniField

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial

namespace U6LocalAux

section Model

theorem exists_model_of_isLieQuot {Y : Type} [Group Y] (hY : IsLieQuot Y IsU6EightIndex) :
    ∃ (K0 : Type) (_ : Field K0), ∃ h : UnitaryFieldData 2 3 K0,
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hY
  cases d with
  | twistedA r q =>
    obtain ⟨hr, hq⟩ := hd
    subst hr
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e
    obtain ⟨hp2, he3⟩ := hq
    rw [hp2, he3] at hm
    obtain ⟨-, K0, fK0, hfin, hcard, ⟨e'⟩⟩ := hm
    exact ⟨K0, fK0, ⟨Nat.prime_two, by norm_num, by rw [hcard]; norm_num⟩, ⟨e'⟩⟩
  | _ => exact absurd hd (by simp [IsU6EightIndex])

end Model

section FieldCore

theorem fieldCoreAt_of_fieldAutU6 {S : Type} [Group S] {φ : MulAut S} (hφ3 : φ ^ 3 = 1)
    (hφ1 : φ ≠ 1) (hφ : FieldAutU 6 S φ) : FieldCoreAt 3 φ := by
  obtain ⟨K0, fK0, h, e, σ, γ, hσ1, -, hγ⟩ := U6Bridge.exists_uFieldAut_of_fieldAutU6 hφ
  haveI := h.finite
  haveI : IsCyclic (K0 ≃+* K0) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K0
  set φ' := MulAut.congr e φ with hφ'
  have hφ'3 : φ' ^ 3 = 1 := by rw [hφ', ← map_pow, hφ3, map_one]
  have hφ'1 : φ' ≠ 1 := fun h1 => hφ1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  have hord : orderOf φ' = 3 := orderOf_eq_prime hφ'3 hφ'1
  have hfac : uFactor h (by norm_num) (by norm_num) φ' = σ := by
    have h1 := congrArg (uFactor h (by norm_num) (by norm_num)) hγ
    have h2 := uFactor_apply h (n := 6) (by norm_num) (by norm_num) 1 σ
    rw [map_one, one_mul] at h2
    rw [map_mul, map_mul, map_inv, h2] at h1
    have hcomm : ∀ a b : K0 ≃+* K0, a * b = b * a := fun a b =>
      (IsMulCommutative.is_comm.comm a b)
    calc uFactor h (by norm_num) (by norm_num) φ'
        = (uFactor h (by norm_num) (by norm_num) γ) * uFactor h (by norm_num) (by norm_num) φ' *
          (uFactor h (by norm_num) (by norm_num) γ)⁻¹ := by
          rw [hcomm (uFactor h (by norm_num) (by norm_num) γ), mul_assoc, mul_inv_cancel,
            mul_one]
      _ = σ := h1
  have hσ3 : σ ^ 3 = 1 := by rw [← hfac, ← map_pow, hφ'3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨M, hM⟩ := U6Bridge.conj_uFieldAut_of_order_three h φ' hord σ hσord hfac
  have hfc : FieldCoreAt 3 φ' := u6_fieldCoreAt h hσord ⟨M, hM⟩
  have hfc' := FieldCoreAt.congr hfc e.symm
  have hback : MulAut.congr e.symm φ' = φ := by
    rw [hφ']
    exact (MulAut.congr e).symm_apply_apply φ
  rwa [hback] at hfc'

end FieldCore

section Transfer

theorem localDeltaIn_eq_bot_of_map {p : ℕ} (hp : p.Prime) {Y S : Type*} [Group Y] [Group S]
    [Finite S]
    (ψ : MulAut Y →* MulAut S) (hψ : Function.Injective ψ)
    (hinn : innerAut S ≤ (innerAut Y).map ψ)
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    {H D : Subgroup (MulAut Y)} (hH : innerAut Y ≤ H) {d : MulAut Y} (hdD : d ∈ D) (hd1 : d ≠ 1)
    (hfc : FieldCoreAt p (ψ d)) : localDeltaIn p H D = ⊥ := by
  have h1 := map_localDeltaIn_le p ψ hψ H D
  have h2 : localDeltaIn p (H.map ψ) (D.map ψ) = ⊥ :=
    localDeltaIn_eq_bot_of_fieldCore hp hinj (hinn.trans (Subgroup.map_mono hH))
      (Subgroup.mem_map_of_mem ψ hdD) (fun h1 => hd1 (hψ (h1.trans (map_one ψ).symm))) hfc
  rw [h2, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h1

theorem commutator_quotient_eq_top {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    (N : Subgroup Y) [N.Normal] : commutator (Y ⧸ N) = ⊤ := by
  have := congrArg (Subgroup.map (QuotientGroup.mk' N)) hperf
  rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective N)] at this
  rw [commutator]
  exact this

@[expose] noncomputable def centerQuotEquiv {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    {N : Subgroup Y} [N.Normal] (hN : N ≤ Subgroup.center Y) :
    ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)) ≃* Y ⧸ Subgroup.center Y :=
  (QuotientGroup.quotientMulEquivOfEq (Bal209TwoInAux.center_quotient_eq_map hperf hN)).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center Y) hN)

theorem congr_centerQuotEquiv_barAut {X : Type} [Group X] {K : Subgroup X}
    (hperf : commutator ↥K = ⊤) (hN : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K)
    (γ : ↥(Subgroup.normalizer (K : Set X))) :
    MulAut.congr (centerQuotEquiv hperf hN) (autCenterQuot (barOf 3 K) (barAut 3 K γ)) =
      actHom K γ := by
  refine MulEquiv.ext fun z => ?_
  induction z using QuotientGroup.induction_on with
  | H k =>
    show centerQuotEquiv hperf hN (autCenterQuot (barOf 3 K) (barAut 3 K γ)
      ((centerQuotEquiv hperf hN).symm (QuotientGroup.mk k))) = actHom K γ (QuotientGroup.mk k)
    have h1 : (centerQuotEquiv hperf hN).symm (QuotientGroup.mk k) =
        (QuotientGroup.mk (QuotientGroup.mk k : barOf 3 K) :
          barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
      ((centerQuotEquiv hperf hN).symm_apply_eq).2 rfl
    rw [h1, autCenterQuot_mk, barAut_mk]
    rfl

end Transfer

end U6LocalAux

section Main

open U6LocalAux

theorem u6Local : FourULocal IsU6EightIndex (FieldAutU 6) := by
  intro X _ _ K A hK hLie hAN hAel hout
  classical
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  obtain ⟨K0, fK0, h, ⟨e⟩⟩ := exists_model_of_isLieQuot hLie
  haveI := h.finite
  have h3P : 3 ∣ Nat.card (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
    have := dvd_card_primeFormP_one h Nat.prime_three (n := 6) (by norm_num)
      (by norm_num : 3 ∣ 2 ^ 3 + 1)
    rwa [← Nat.card_congr (uTransport h (by norm_num : 1 ≤ 6)).toEquiv] at this
  have h3 : 3 ∣ Nat.card ↥K := by
    refine h3P.trans ?_
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_quotient_dvd_card (Subgroup.center ↥K)
  have hNZ : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    Bal209TwoInAux.pPrimeCore_le_center_of_quasisimple hq Nat.prime_three h3
  have hK3 : InnerOneBalanceThree (barOf 3 K) :=
    Bal209TwoInnerAux.innerOneBalanceThree_quotient_of_central hperf hNZ
      (Bal209TwoInAux.innerOneBalanceThree_of_mulEquiv e (u6_innerOneBalanceThree h))
  intro D hD H hH hDH
  obtain ⟨hDA, hDel, hDcard⟩ := hD
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hcon
    rw [hbot, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  obtain ⟨γ, hγ, rfl⟩ := hDA hdD
  have hγA : (γ : X) ∈ A := (Subgroup.mem_subgroupOf.1 hγ).1
  by_cases hin : InnerAt K (γ : X)
  · obtain ⟨k, hk, hkc⟩ := hin
    have hdinn : barAut 3 K γ ∈ innerAut (barOf 3 K) :=
      ⟨QuotientGroup.mk ⟨k, hk⟩, (barAut_eq_conj_of_inner hk hkc γ.2).symm⟩
    exact localDeltaIn_eq_bot_of_innerOneBalanceThree hK3 hDel hdD hdinn hd1 hH
  · have hfa := hout (γ : X) hγA hin
    have hperfY : commutator (barOf 3 K) = ⊤ :=
      commutator_quotient_eq_top hperf (GLAPPrimeCore 3 ↥K)
    have hψ : Function.Injective (autCenterQuot (barOf 3 K)) :=
      autCenterQuot_injective_of_perfect hperfY
    set ρ := centerQuotEquiv hperf hNZ with hρ
    have hcompat := congr_centerQuotEquiv_barAut hperf hNZ γ
    have hd3 : barAut 3 K γ ^ 3 = 1 := hDel.2 _ hdD
    have hφ3 : actHom K γ ^ 3 = 1 := by
      rw [← hcompat, ← map_pow, ← map_pow, hd3, map_one, map_one]
    have hφ1 : actHom K γ ≠ 1 := by
      intro h1
      apply hd1
      apply hψ
      rw [map_one]
      apply (MulAut.congr ρ).injective
      rw [hcompat, h1, map_one]
    have hfc := fieldCoreAt_of_fieldAutU6 hφ3 hφ1 hfa
    have hfc' : FieldCoreAt 3 (autCenterQuot (barOf 3 K) (barAut 3 K γ)) := by
      have h1 := FieldCoreAt.congr hfc ρ.symm
      have hb : MulAut.congr ρ.symm (actHom K γ) =
          autCenterQuot (barOf 3 K) (barAut 3 K γ) := by
        rw [← hcompat]
        exact (MulAut.congr ρ).symm_apply_apply _
      rwa [hb] at h1
    have hcenK : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_quot_eq_bot hq
    have hcenS : Subgroup.center (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) = ⊥ := by
      rw [← Subgroup.map_center_eq ρ.symm, hcenK, Subgroup.map_bot]
    have hinj : Function.Injective (MulAut.conj : (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) →*
        MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) := conj_inj_of_center_bot hcenS
    have hinn : innerAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) ≤
        (innerAut (barOf 3 K)).map (autCenterQuot (barOf 3 K)) := by
      rintro _ ⟨s, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      exact ⟨MulAut.conj y, ⟨y, rfl⟩, Bal209TwoInnerAux.autCenterQuot_conj y⟩
    exact localDeltaIn_eq_bot_of_map Nat.prime_three (autCenterQuot (barOf 3 K)) hψ hinn hinj hH
      hdD hd1 hfc'

end Main

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
