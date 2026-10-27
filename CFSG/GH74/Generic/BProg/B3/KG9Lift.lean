module

public import CFSG.GH74.Generic.BProg.B3.KG531BPairOther
public import CFSG.GH74.Generic.BProg.B3.KG9Form
public import CFSG.GH74.Generic.BProg.B3.KG9Quot

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

namespace KG9

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (GHOddLie BTwo fixedSubgroup_conj_eq_centralizer_gen
  orderOf_conj_eq_two)
open scoped MatrixGroups

theorem pPrimeCoreOf_eq_bot_of_oddLie {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsQuasisimple ↥M) (hodl : GHOddLie (↥M ⧸ center ↥M)) (hO : pPrimeCore 2 ↥M = ⊥)
    {t : X} (htM : t ∈ M) (ht2 : orderOf t = 2) (htZ : (⟨t, htM⟩ : ↥M) ∉ center ↥M)
    {L : Subgroup X} (hL : IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L) {F : Type} [Field F]
    [Fintype F] (h9 : Fintype.card F = 9) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) :
    pPrimeCoreOf 2 L = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup X := centralizer ({t} : Set X) ⊓ M
  have hKM : K ≤ M := inf_le_right
  set π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M) with hπ
  set t' : ↥M := ⟨t, htM⟩ with ht'
  set κ : ↥K →* ↥M := Subgroup.inclusion hKM with hκdef
  have hrange : κ.range = centralizer ({t'} : Set ↥M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).1
      simpa [ht', hκdef] using this
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, x.2⟩⟩,
        rfl⟩
      simpa [ht'] using congrArg Subtype.val hx
  set ρ : ↥K →* ↥M ⧸ center ↥M := π.comp κ with hρ
  have hρker : ρ.ker ≤ center ↥K := by
    intro k hk
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subgroup.inclusion_injective hKM
    simpa using (Subgroup.mem_center_iff.mp hk (κ g))
  have hZS : center (↥M ⧸ center ↥M) = ⊥ :=
    CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hM
  have hu1 : π t' ≠ 1 := by
    intro h
    exact htZ ((QuotientGroup.eq_one_iff _).1 h)
  have hu2 : orderOf (π t') = 2 := by
    refine orderOf_eq_prime ?_ hu1
    have ht'2 : t' ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← ht2]
      exact pow_orderOf_eq_one t
    rw [← map_pow, ht'2, map_one]
  have hB := bTwo_of_ghOddLie hZS hodl hu2
  rw [BTwo, fixedSubgroup_conj_eq_centralizer_gen] at hB
  obtain ⟨hBle, hBP⟩ := isPComponent_image κ hrange hL.2 (not_le_of_pComponent hL.2 hρker)
  have hBq : IsQuasisimple ↥((L.subgroupOf K).map ρ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBle) (hB _ hBP)
  have hJq : IsQuasisimple ↥(L.subgroupOf K) :=
    (CFSG.ComponentClassification.CatalogueBCentralQuotient.pComponent_quasisimple_iff ρ hρker 2
      _ hL.2).2 hBq
  have hsub : (((L.subgroupOf K).map ρ).subgroupOf
      (centralizer ({π t'} : Set (↥M ⧸ center ↥M)))).IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hBP
    exact h
  have hBc : IsComponent (((L.subgroupOf K).map ρ).subgroupOf
      (centralizer ({π t'} : Set (↥M ⧸ center ↥M)))) := ⟨hB _ hBP, hsub⟩
  have eL : ↥(L.subgroupOf K) ⧸ pPrimeCore 2 ↥(L.subgroupOf K) ≃* SL(2, F) := coreQuotEquiv hL.1 e
  have hOZ := pPrimeCore_le_center_of_sl2 hJq (by rw [h9]; exact ⟨4, rfl⟩) eL
  obtain ⟨eA⟩ := nonempty_centerQuot_alt6 hJq h9 eL
  set σ := ρ.subgroupMap (L.subgroupOf K)
  have hσs : Function.Surjective σ := ρ.subgroupMap_surjective _
  have hσk : σ.ker ≤ center ↥(L.subgroupOf K) := by
    intro x hx
    have hx' : ρ (x : ↥K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hc : (x : ↥K) ∈ center ↥K := hρker (MonoidHom.mem_ker.mpr hx')
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    exact Subtype.ext (hc (g : ↥K))
  obtain ⟨eLB⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hJq σ hσs hσk
  set eC := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizer_gen (π t')).symm
  have hK₀ := CFSG.LocalCores.isComponent_map_mulEquiv eC hBc
  have eK₀ := ((((L.subgroupOf K).map ρ).subgroupOf
      (centralizer ({π t'} : Set (↥M ⧸ center ↥M)))).equivMapOfInjective eC.toMonoidHom
      eC.injective).symm.trans (Subgroup.subgroupOfEquivOfLe hBle)
  have hZ₀ := a6CentreForm_of_ghOddLie hodl (MulAut.conj (π t')) (orderOf_conj_eq_two hZS hu2) _
    hK₀ ⟨(QuotientGroup.congr _ _ eK₀ (Subgroup.map_center_eq eK₀)).trans (eLB.symm.trans eA)⟩
  have hZB : IsPGroup 2 ↥(center ↥((L.subgroupOf K).map ρ)) :=
    hZ₀.of_equiv (Subgroup.centerCongr eK₀)
  have hO' : pPrimeCore 2 ↥(L.subgroupOf K) = ⊥ := by
    refine pPrimeCore_eq_bot_of_map hOZ σ hσs hZB fun N hN hodd => ?_
    have hι : Function.Injective (κ.comp (L.subgroupOf K).subtype) :=
      (Subgroup.inclusion_injective hKM).comp Subtype.val_injective
    have hNZ : N.map (κ.comp (L.subgroupOf K).subtype) ≤ center ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : ρ (x : ↥K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp (hN hx))
      rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hdvd : Nat.card ↥N ∣ Nat.card ↥(center ↥M) := by
      rw [← Subgroup.card_map_of_injective hι]
      exact Subgroup.card_dvd_of_le hNZ
    exact Subgroup.eq_bot_of_card_eq N
      (Nat.Coprime.eq_one_of_dvd (coprime_card_center hO hodd) hdvd)
  have hOL := pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hL.1)
  rw [hO', Subgroup.map_bot] at hOL
  rw [pPrimeCoreOf, ← hOL, Subgroup.map_bot]

end KG9

end KG531BP

end CFSG.GH74.Generic.BProg.B3
