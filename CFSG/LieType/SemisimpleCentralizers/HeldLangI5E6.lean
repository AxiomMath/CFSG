module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Torus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Cover
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.TauCetiBridge
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.LieType.Chevalley

section Certificates

theorem kd264I5Universal_E6 (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.E6 q).Valid)
    (h3q : 3 ∣ q.card - 1) (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.E6 q, hd⟩ L)
    (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) :
    ∃ E : Subgroup L, E ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β ∧ IsElemAbelian 3 E ∧
      5 + CFSG.Open.pRank 3 (Subgroup.center L) ≤ CFSG.Open.pRank 3 E := by
  classical
  haveI hcyc : IsCyclic ↥(Subgroup.center L) := hL.2.2.1
  obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hd
  obtain ⟨eX⟩ := hL.2.1
  let eA : (L ⧸ Subgroup.center L) ≃* adjointGroup Tag.E6 K := eX.trans eK
  have hK' : Nat.card K = q.p ^ q.exponent := hKcard.trans (TauCeti.PrimePower.card_def q)
  have h3K : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3q
  have hγ3 : onCenterQuotient β ^ 3 = 1 := by
    have := congrArg (centerQuotientHom L) hβ3
    rwa [map_pow, map_one] at this
  set x : MulAut (adjointGroup Tag.E6 K) := MulAut.congr eA (onCenterQuotient β) with hx
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hγ3, map_one]
  have hxo : x ∉ e6Inndiag K := fun hmem =>
    hout ((mem_innAutDerived_congr eA).1
      (commutator_le_innAutDerived _ (CFSG.HardMathSupport.Dickson.Sec6.I923.e6Inndiag_le_commutator (K := K) hmem)))
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP K q.p := hKchar
  obtain ⟨σ, hσord, h3f, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag q.prime_p q.exponent_pos K hK'
    Nat.prime_three (by norm_num) hx3 hxo
  have hσ3 : σ ^ 3 = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
  have hf3 : 3 ≤ q.exponent := Nat.le_of_dvd q.exponent_pos h3f
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK']
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ q.p ^ 3 := Nat.pow_le_pow_left q.prime_p.two_le 3
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos hf3
  haveI hMfin : Finite (e6Data_valid.minGroup K) := finite_minGroup' e6Data_valid
  have hperfM : Group.IsPerfect (e6Data_valid.minGroup K) := (CFSG.LieType.CurtisTits.isQuasisimple_e6 K).1
  have hperfL : Group.IsPerfect L := Group.isPerfect_def.2 hL.1.1
  let qC : e6Data_valid.minGroup K →* L ⧸ Subgroup.center L := eA.symm.toMonoidHom.comp (e6Isogeny K)
  let qL : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hkerC : qC.ker = Subgroup.center (e6Data_valid.minGroup K) := by
    rw [← e6Isogeny_ker_eq_center]
    ext y
    simp only [MonoidHom.mem_ker, qC, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff _ eA.symm.injective
  have hcardC : Nat.card qC.ker = 3 := by
    rw [hkerC, (card_center_e6 K).1, Nat.gcd_eq_left h3K]
  have hcardL : Nat.card qL.ker = 3 := by
    rw [show qL.ker = Subgroup.center L from QuotientGroup.ker_mk' _, hL.2.2.2]
    exact Nat.gcd_eq_left h3q
  obtain ⟨E, hEfix, hEab, hEcard⟩ := exists_torus3_E6 h3K hσ3
  let τb : MulAut (L ⧸ Subgroup.center L) := MulAut.congr eA.symm (entrywiseAdjointAut Tag.E6 σ)
  have hτ : ∀ y, qC (minBCAut σ y) = τb (qC y) := fun y => by
    show eA.symm (e6Isogeny K (minBCAut σ y)) =
      (MulAut.congr eA.symm (entrywiseAdjointAut Tag.E6 σ)) (eA.symm (e6Isogeny K y))
    rw [e6Isogeny_minBCAut]
    simp [MulAut.congr_apply]
  have hψ' : MulAut.congr eA.symm ψ * onCenterQuotient β * (MulAut.congr eA.symm ψ)⁻¹ = τb := by
    have h1 : MulAut.congr eA.symm (ψ * x * ψ⁻¹) = τb := by rw [hψ]
    have h2 : MulAut.congr eA.symm x = onCenterQuotient β := by
      refine MulEquiv.ext fun z => ?_
      simp [hx, MulAut.congr_apply]
    rw [← h1, map_mul, map_mul, map_inv, h2]
  obtain ⟨E', hE'fix, hE'ab, hE'card⟩ := exists_fixed_elemAbelian_of_cover qC qL
    (eA.symm.surjective.comp (e6Isogeny_surjective K)) (QuotientGroup.mk'_surjective _)
    (by rw [hkerC]) (by rw [show qL.ker = Subgroup.center L from QuotientGroup.ker_mk' _])
    hperfM hperfL (fun E _ _ π hπ hker => e6_exists_section_of_central hK5 hπ hker)
    (by rw [hcardC, hcardL]) β (minBCAut σ) (onCenterQuotient β) τb (MulAut.congr eA.symm ψ)
    (fun y => (onCenterQuotient_apply_mk β y).symm) hτ hψ' E hEfix hEab hEcard
  refine ⟨E', hE'fix, hE'ab, ?_⟩
  have h1 : 6 ≤ CFSG.Open.pRank 3 E' := le_pRank_of_card E' hE'ab hE'card
  have h2 : CFSG.Open.pRank 3 (Subgroup.center L) ≤ 1 := pRank_le_one_of_isCyclic _
  omega

end Certificates

end CFSG.LieType.SemisimpleCentralizers.HeldLang
