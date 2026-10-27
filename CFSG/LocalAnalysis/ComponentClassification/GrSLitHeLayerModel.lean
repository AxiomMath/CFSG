module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeLayerTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit.HeLay

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

@[expose] noncomputable def rho0 :
    ↥(centralizerIn heP (heGenPerm 0)) →* Equiv.Perm (Fin 105) :=
  heRho0.comp (MulEquiv.subgroupCongr heInnerGrp0_eq).symm.toMonoidHom


theorem rho0_range : rho0.range = heRho0.range := by
  rw [rho0, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
    (MulEquiv.subgroupCongr heInnerGrp0_eq).symm.surjective, ← MonoidHom.range_eq_map]

theorem card_rho0_ker : Nat.card rho0.ker = 4 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup rho0.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rho0).toEquiv, rho0_range,
    card_heRho0_range, card_heP_cent0] at h
  omega

theorem commutator_rho0_range_le :
    ⁅rho0.range, rho0.range⁆ ≤ genGroup 105 heDGens heDPerm := by
  obtain ⟨-, -, hDle, hDi⟩ := heD_facts
  rw [rho0_range]
  set R := heRho0.range
  set D' := (genGroup 105 heDGens heDPerm).subgroupOf R
  have : D'.Normal := normal_of_index_eq_two hDi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : Nat.card (↥R ⧸ D') = 2 := by rw [← index_eq_card, hDi]
  have : IsCyclic (↥R ⧸ D') := isCyclic_of_prime_card hQ
  have hcomm' : ∀ a b : ↥R ⧸ D', a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := ↥R ⧸ D')).is_comm.comm a b
  rw [commutator_le]
  intro x hx y hy
  have hmem : ⁅(⟨x, hx⟩ : ↥R), ⟨y, hy⟩⁆ ∈ D' := by
    have h1 : QuotientGroup.mk' D' ⁅(⟨x, hx⟩ : ↥R), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm' _ _
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact mem_subgroupOf.mp hmem

theorem oddCore_t0 : pPrimeCore 2 ↥(centralizerIn heP (heGenPerm 0)) = ⊥ := by
  rw [HeldFix.pPrimeCore_two_eq_oddCore]
  exact heInner0_oddCore card_heP_cent0

theorem layer_t0 :
    ∃ N : Subgroup ↥(centralizerIn heP (heGenPerm 0)), IsPComponent 2 N ∧ N ≠ ⊥ ∧
      pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 = N ∧ ⁅N, N⁆ = N ∧
      IsL34Type (↥N ⧸ center ↥N) ∧ N.Normal ∧ N.map rho0 = genGroup 105 heDGens heDPerm := by
  obtain ⟨⟨hDs, hDnab⟩, -, hDle, -⟩ := heD_facts
  have hDle' : genGroup 105 heDGens heDPerm ≤ rho0.range := by rw [rho0_range]; exact hDle
  obtain ⟨N, hNn, hNq, hNρ⟩ := exists_quasisimple_normal rho0 hDs hDnab hDle'
    commutator_rho0_range_le card_rho0_ker
  have hO := oddCore_t0
  have hNc : IsComponent N := ⟨hNq, Normal.isSubnormal hNn⟩
  have hne : N ≠ ⊥ := (nontrivial_iff_ne_bot N).mp (LocalCores.isQuasisimple_nontrivial hNq)
  have hNp : IsPComponent 2 N := by
    refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hNc ?_
    rw [hO]
    exact fun h => hne (le_bot_iff.mp h)
  have huniq : ∀ J, IsPComponent 2 J → J = N := fun J hJ =>
    eq_of_isComponent rho0 hDs hDnab commutator_rho0_range_le card_rho0_ker hNc hNρ
      (HeldFix.isComponent_of_isPComponent hO hJ)
  have hlayer : pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 = N :=
    le_antisymm (sSup_le fun J hJ => (huniq J hJ).le) (le_sSup hNp)
  have hZ := HeldFix.fusionZStar_eq_center_of_isPComponent hO hNp
  have hT := HeldFix.isL34Type_of_isPComponent_centralizer_heA0 N hNp
  exact ⟨N, hNp, hne, hlayer, isPerfect_iff.mp hNq.1,
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ) hT, hNn, hNρ⟩

theorem gsFixedLayer_t0 :
    gsFixedLayer heP (heGenPerm 0) ≠ ⊥ ∧
      ⁅gsFixedLayer heP (heGenPerm 0), gsFixedLayer heP (heGenPerm 0)⁆ =
        gsFixedLayer heP (heGenPerm 0) ∧
      IsL34Type (↥(gsFixedLayer heP (heGenPerm 0)) ⧸ center ↥(gsFixedLayer heP (heGenPerm 0))) := by
  obtain ⟨N, hNp, hne, hlayer, hNperf, hT, -, -⟩ := layer_t0
  have hK : gsFixedLayer heP (heGenPerm 0) = N.map (centralizerIn heP (heGenPerm 0)).subtype := by
    show (pLayer ↥(centralizerIn heP (heGenPerm 0)) 2).map _ = _
    rw [hlayer]
    rfl
  rw [hK]
  refine ⟨?_, ?_, ?_⟩
  · exact fun h => hne ((map_eq_bot_iff_of_injective N (subtype_injective _)).mp h)
  · rw [← map_commutator, hNperf]
  · exact LieType.CurtisTits.lieModel_of_mulEquiv
      (Sol78.centerQuotCongr (N.equivMapOfInjective _ (subtype_injective _))) hT

theorem gsFixedLayer_t1 :
    gsFixedLayer heP heT1P = ⊥ := by
  have h : pLayer ↥(heP ⊓ centralizer ({heT1P} : Set (Equiv.Perm (Fin 8330)))) 2 = ⊥ :=
    sSup_eq_bot.mpr fun J hJ => (HeldFix.not_isPComponent_centralizer_heT1P J hJ).elim
  unfold gsFixedLayer
  rw [h, Subgroup.map_bot]

theorem gsFixedLayer_conj {c : Equiv.Perm (Fin 8330)} (hc : c ∈ heP) (p : Equiv.Perm (Fin 8330)) :
    gsFixedLayer heP (c * p * c⁻¹) = (gsFixedLayer heP p).map (MulAut.conj c).toMonoidHom := by
  have h := GSLit.map_gsFixedLayer (MulAut.conj c) heP p
  have hP : heP.map (MulAut.conj c).toMonoidHom = heP :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hc)
  rw [hP, MulAut.conj_apply] at h
  exact h.symm

theorem heldTwoA_heP_iff
    {p : Equiv.Perm (Fin 8330)} (hp : p ∈ heP) (hp2 : orderOf p = 2) :
    HeldTwoA heP p ↔ p ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  constructor
  · rintro ⟨-, -, hK⟩
    rcases involution_conj_cases hp hp2 with h | ⟨c, hc, rfl⟩
    · exact h
    · exfalso
      apply hK
      rw [gsFixedLayer_conj hc, gsFixedLayer_t1, Subgroup.map_bot]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨hp, hp2, ?_⟩
    rw [gsFixedLayer_conj hc]
    intro h
    exact gsFixedLayer_t0.1 ((map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp h)

end CFSG.ComponentClassification.GrSLit.HeLay
