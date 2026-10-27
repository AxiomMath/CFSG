module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitHullTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStepFour
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

variable {X : Type} [Group X] [Finite X]

structure StarConfig (a δ₁ δ₂ : X) (N₁ N₂ E : Subgroup X) : Prop where
  ha : orderOf a = 2
  hδ₁ : orderOf δ₁ = 2
  hδ₂ : orderOf δ₂ = 2
  h12 : δ₁ * δ₂ = δ₂ * δ₁
  ha1 : a * δ₁ = δ₁ * a
  ha2 : a * δ₂ = δ₂ * a
  hN₁ : N₁ ≤ centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X)
  hN₁c : IsPComponent 2 (N₁.subgroupOf (centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X)))
  hN₂ : N₂ ≤ centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X)
  hN₂c : IsPComponent 2 (N₂.subgroupOf (centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X)))
  hδN₁ : δ₁ ∈ N₁
  hδN₂ : δ₂ ∈ N₂
  hSL : ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
    Nonempty (N₁ ⧸ pPrimeCore 2 N₁ ≃* SL(2, GaloisField p n)) ∧
    Nonempty (N₂ ⧸ pPrimeCore 2 N₂ ≃* SL(2, GaloisField p n))
  hEa : E ≤ oddCentralizerCore a
  hE : E ≤ centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X)
  hprop₁ : ActsProperly a E N₁ (oddCoreIn N₁)
  hprop₂ : ActsProperly a E N₂ (oddCoreIn N₂)

theorem eq_of_isPComponent_of_le {C A B : Subgroup X} (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : IsPComponent 2 (A.subgroupOf C)) (hB : IsPComponent 2 (B.subgroupOf C)) (hAB : A ≤ B) :
    A = B := by
  have h := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hA
    hB).1 (fun x hx => hAB hx)
  rwa [subgroupOf_inj, inf_eq_left.mpr hAC, inf_eq_left.mpr hBC] at h

theorem fixedLayer_SL2_false (hI : TBInputs) (hX : TBSetting X) {d e : X} (hd : orderOf d = 2)
    (he : orderOf e = 2) (hed : e * d = d * e) {H N : Subgroup X}
    (hH : H ≤ centralizer ({d} : Set X)) (hHc : IsPComponent 2 (H.subgroupOf (centralizer {d})))
    (heH : e ∈ normalizer (H : Set X)) (htriv : ∀ h ∈ H, ⁅h, e⁆ ∈ oddCoreIn H)
    (hN : N ≤ centralizer ({e} : Set X) ⊓ centralizer ({d} : Set X))
    (hNc : IsPComponent 2 (N.subgroupOf (centralizer ({e} : Set X) ⊓ centralizer ({d} : Set X))))
    (hNH : N ≤ H) (hNHc : IsPComponent 2 (N.subgroupOf (H ⊓ centralizer ({e} : Set X))))
    (hdN : d ∈ N) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (eN : N ⧸ pPrimeCore 2 N ≃* SL(2, GaloisField p n)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHsub, -, hHq⟩ := isPComponent_data hH hHc
  have heC : e ∈ centralizer ({d} : Set X) := mem_centralizer_singleton_iff.mpr hed
  have hcomm := (forall_commutator_mem_iff heH).mp htriv
  have hT := UnbalancedCorr.gsFixedLayer_isPComponent hH hHsub heC he heH hHq hcomm
  have hsup := UnbalancedLayer.gsFixedLayer_sup_map_pPrimeCore he hHq heH hcomm
  have hTle : UnbalancedGS.gsFixedLayer H e ≤
      centralizer ({e} : Set X) ⊓ centralizer ({d} : Set X) := by
    refine (UnbalancedGS.gsFixedLayer_le_inf H e).trans ?_
    exact le_inf inf_le_right (inf_le_left.trans hH)
  have hT' : IsPComponent 2 ((UnbalancedGS.gsFixedLayer H e).subgroupOf
      (centralizer ({e} : Set X) ⊓ centralizer ({d} : Set X))) := by
    rwa [inf_comm (centralizer ({e} : Set X))]
  have hNT : N ≤ UnbalancedGS.gsFixedLayer H e := by
    have h1 : N.subgroupOf (H ⊓ centralizer ({e} : Set X)) ≤
        pLayer ↥(H ⊓ centralizer ({e} : Set X)) 2 := le_sSup hNHc
    have h2 := map_mono (f := (H ⊓ centralizer ({e} : Set X)).subtype) h1
    rwa [map_subgroupOf_eq_of_le (le_inf hNH (hN.trans inf_le_left))] at h2
  have heq := eq_of_isPComponent_of_le hN hTle hNc hT' hNT
  rw [← heq] at hsup
  obtain ⟨-, φ, -⟩ := UnbalancedLayer.restriction_quotient_mulEquiv hNH hsup
  exact intrinsic_SL2_exclusion hI.classicalInvolution hI.catalogU hX hd hH hHc (hNH hdN) hp2 hn
    (φ.symm.trans eN)

theorem StarConfig.false (hI : TBInputs) (hX : TBSetting X)
    {a δ₁ δ₂ : X} {N₁ N₂ E : Subgroup X} (hS : StarConfig a δ₁ δ₂ N₁ N₂ E) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.simple
  obtain ⟨p, n, hpf, hp2, hn, ⟨e₁⟩, ⟨e₂⟩⟩ := hS.hSL
  have hKC := isKGroupCat_centralizer hX.kProper (hX.not_mem_center hS.hδ₁)
  have hδ₂C : δ₂ ∈ centralizer ({δ₁} : Set X) := mem_centralizer_singleton_iff.mpr hS.h12.symm
  have hN₁E := le_pLayer_of_isPComponent_inf hI.schreier hKC hδ₂C hS.hδ₂ hS.hN₁ hS.hN₁c
  have hN₂E := le_pLayer_of_isPComponent_inf hI.schreier hKC hδ₂C hS.hδ₂ hS.hN₂ hS.hN₂c
  have hpump : ∀ {N : Subgroup X}, N ≤ centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X) →
      IsPComponent 2 (N.subgroupOf (centralizer ({δ₂} : Set X) ⊓ centralizer ({δ₁} : Set X))) →
      N ≤ (pLayer (centralizer ({δ₁} : Set X)) 2).map (centralizer ({δ₁} : Set X)).subtype →
      ∃ H : Subgroup X, H ≤ centralizer ({δ₁} : Set X) ∧
        IsPComponent 2 (H.subgroupOf (centralizer ({δ₁} : Set X))) ∧
        δ₂ ∈ normalizer (H : Set X) ∧ N ≤ H ∧
        IsPComponent 2 (N.subgroupOf (H ⊓ centralizer ({δ₂} : Set X))) := by
    intro N hN hNc hNE
    obtain ⟨H, hH, hHc, hNH, hNHc⟩ :=
      UGSChain.exists_orbit_component_of_le_pLayer hS.hδ₂ hS.h12.symm hN hNc hNE
    have hδ₂H : δ₂ ∈ normalizer (H : Set X) :=
      UGSChain.map_pLayer_le_normalizer hH hHc (hN₂E hS.hδN₂)
    have hHH : H ⊔ conjugate H δ₂ = H := by
      rw [UnbalancedLayer.conjugate_eq_of_mem_normalizer hδ₂H, sup_idem]
    rw [hHH] at hNH hNHc
    exact ⟨H, hH, hHc, hδ₂H, hNH, hNHc⟩
  obtain ⟨H₁, hH₁, hH₁c, hδ₂H₁, hN₁H, hN₁Hc⟩ := hpump hS.hN₁ hS.hN₁c hN₁E
  obtain ⟨H₂, hH₂, hH₂c, -, hN₂H, hN₂Hc⟩ := hpump hS.hN₂ hS.hN₂c hN₂E
  have hnt : ¬ ∀ h ∈ H₁, ⁅h, δ₂⁆ ∈ oddCoreIn H₁ := fun htriv =>
    fixedLayer_SL2_false hI hX hS.hδ₁ hS.hδ₂ hS.h12.symm hH₁ hH₁c hδ₂H₁ htriv hS.hN₁ hS.hN₁c
      hN₁H hN₁Hc hS.hδN₁ hp2 hn e₁
  have hH12 : H₁ = H₂ := by
    by_contra hne
    exact hnt fun h hh => commutator_le_oddCoreIn_of_ne hH₁ hH₂ hH₁c hH₂c hne
      (commutator_mem_commutator hh (hN₂H hS.hδN₂))
  subst hH12
  have hN₁perf := commutator_self_of_isPComponent hS.hN₁ hS.hN₁c
  have haH : a ∈ normalizer (H₁ : Set X) :=
    mem_normalizer_of_isPComponent_centralizer hS.ha1 hH₁ hH₁c hN₁H hN₁perf hS.hδN₁ hS.hδ₁
      (hS.hprop₁.1 (subset_closure (Set.mem_insert a _))).1
  have hEH : E ≤ normalizer (H₁ : Set X) := fun e he =>
    mem_normalizer_of_isPComponent_centralizer
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (hS.hE he)).2) hH₁ hH₁c hN₁H hN₁perf
      hS.hδN₁ hS.hδ₁ (hS.hprop₁.1 (subset_closure (Set.mem_insert_of_mem a he))).1
  have hconf : IsUnbalancingConfig δ₁ a H₁ E :=
    isUnbalancingConfig_of_actsProperly hS.hδ₁ hS.ha hS.ha1 hH₁ hH₁c hS.hEa
      (hS.hE.trans inf_le_right) haH hEH hN₁H hS.hprop₁
  have hδ₁H₁ : δ₁ ∈ H₁ := hN₁H hS.hδN₁
  have hδ₂H₁' : δ₂ ∈ H₁ := hN₂H hS.hδN₂
  rcases intrinsic_config_types hI hX hconf hδ₁H₁ with ⟨hodd, hnot⟩ | hL34
  swap
  ·
    have hδ₂2 : δ₂ * δ₂ = 1 := by rw [← pow_two, ← hS.hδ₂, pow_orderOf_eq_one]
    exact L34StepFour.false_of_perfect_le_centralizer hL34 hδ₂H₁' hδ₂2 hnt hN₁H
      (hS.hN₁.trans inf_le_left) hN₁perf (L34StepFour.pPrimeCore_ne_top_of_isQuasisimple
        (isPComponent_data hS.hN₁ hS.hN₁c).2.2)
  obtain ⟨-, -, -, -, -, -, -, hYa, hYE⟩ := id hconf
  have hYn : (H₁.subgroupOf (hull H₁ a E)).Normal := hull_normal hYa.le hYE.le
  obtain ⟨hKq, hZ, hM4, haρ, hEρ⟩ := hull_data hconf hodd hnot
  have hH₁H : H₁ ≤ hull H₁ a E := le_hull_left H₁ a E
  have haH' : a ∈ hull H₁ a E := mem_hull_elem H₁ a E
  have hEH' : E ≤ hull H₁ a E := le_hull_right H₁ a E
  have hδ₁H : δ₁ ∈ hull H₁ a E := hH₁H hδ₁H₁
  have hδ₂H : δ₂ ∈ hull H₁ a E := hH₁H hδ₂H₁'
  have hN₁H' : N₁ ≤ hull H₁ a E := hN₁H.trans hH₁H
  have hN₂H' : N₂ ≤ hull H₁ a E := hN₂H.trans hH₁H
  obtain ⟨-, hN₁g, hN₁q⟩ := isPComponent_data hS.hN₁ hS.hN₁c
  obtain ⟨-, hN₂g, hN₂q⟩ := isPComponent_data hS.hN₂ hS.hN₂c
  obtain ⟨-, -, hH₁q⟩ := isPComponent_data hH₁ hH₁c
  have hN₁s := (isPComponent_data (le_inf hN₁H (hS.hN₁.trans inf_le_left)) hN₁Hc).1
  have hN₂s := (isPComponent_data (le_inf hN₂H (hS.hN₂.trans inf_le_left)) hN₂Hc).1
  have hB : H₁ ⊓ centralizer ({δ₂} : Set X) ≤ hull H₁ a E := inf_le_left.trans hH₁H
  have hsub : ∀ {N : Subgroup X}, N ≤ H₁ → N ≤ centralizer ({δ₂} : Set X) →
      N.subgroupOf (hull H₁ a E) ≤ H₁.subgroupOf (hull H₁ a E) ⊓
        centralizer ({(⟨δ₂, hδ₂H⟩ : hull H₁ a E)} : Set (hull H₁ a E)) := by
    intro N hNH hNδ x hx
    exact mem_inf.mpr ⟨hNH hx, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hNδ hx)))⟩
  have hY1 : (E.subgroupOf (hull H₁ a E)).map (conjQuotAction (H₁.subgroupOf (hull H₁ a E))
      (centralPreimage (pPrimeCore 2 (H₁.subgroupOf (hull H₁ a E))))).rangeRestrict ≠ ⊥ := by
    obtain ⟨e, he, s, hs, hes⟩ := hS.hprop₁.exists_nontrivial
    have heN : e ∈ normalizer (N₁ : Set X) :=
      (hS.hprop₁.1 (subset_closure (Set.mem_insert_of_mem a he))).1
    obtain ⟨k, hk, hke⟩ := exists_not_mem_oddCoreIn_of_le hN₁H heN (fun h => hes (h s hs))
    have hne := rangeRestrict_ne_one_of_not_trivial hH₁H hH₁q (hEH' he) (hEH he)
      (fun h => hke (h k hk))
    intro hbot
    apply hne
    have h1 := mem_map_of_mem (conjQuotAction (H₁.subgroupOf (hull H₁ a E))
      (centralPreimage (pPrimeCore 2 (H₁.subgroupOf (hull H₁ a E))))).rangeRestrict
      (show (⟨e, hEH' he⟩ : hull H₁ a E) ∈ E.subgroupOf (hull H₁ a E) from he)
    rw [hbot] at h1
    exact h1
  refine propC_false hI.propC hKq hZ hM4 haρ hY1 hEρ
    (δ₁ := ⟨δ₁, hδ₁H⟩) (δ₂ := ⟨δ₂, hδ₂H⟩) (by rw [Subgroup.orderOf_mk]; exact hS.hδ₂)
    hδ₁H₁ hδ₂H₁' (by rw [Subgroup.orderOf_mk]; exact hS.hδ₁) ?_ ?_
    (hsub hN₁H (hS.hN₁.trans inf_le_left)) ?_ (hsub hN₂H (hS.hN₂.trans inf_le_left)) ?_
    (CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2 (subgroupOfEquivOfLe hN₁H').symm hN₁g)
    (CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2 (subgroupOfEquivOfLe hN₂H').symm hN₂g)
    (CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2
      (subgroupOfEquivOfLe hN₁H').symm hN₁q)
    (CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2
      (subgroupOfEquivOfLe hN₂H').symm hN₂q)
    hS.hδN₁ hS.hδN₂ hp2 hn
    ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hN₁H')).trans e₁)
    ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hN₂H')).trans e₂) ?_ ?_
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hH₁ hx)))
  · intro h
    exact hnt fun y hy => (mem_oddCoreIn_subgroupOf_iff hH₁H _).mp (h ⟨y, hH₁H hy⟩ hy)
  · rw [← inf_centralizer_subgroupOf hδ₂H]
    exact isSubnormal_subgroupOf_subgroupOf hB hN₁s
  · rw [← inf_centralizer_subgroupOf hδ₂H]
    exact isSubnormal_subgroupOf_subgroupOf hB hN₂s
  · rw [oddCoreIn_subgroupOf hN₁H']
    exact hS.hprop₁.subgroupOf haH' hEH' hN₁H'
  · rw [oddCoreIn_subgroupOf hN₂H']
    exact hS.hprop₂.subgroupOf haH' hEH' hN₂H'


end CFSG.ComponentClassification.TBLit
