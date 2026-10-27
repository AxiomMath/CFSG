module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Aut
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

theorem fourClassesLarge_centralizer_of_mulEquiv {Y J : Type*} [Group Y] [Group J]
    (θ : Y ≃* J)
    (hJ : ∀ j : J, orderOf j = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({j} : Set J))) :
    ∀ y : Y, orderOf y = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({y} : Set Y)) := fun y hy =>
  CFSG.ComponentClassification.M12Cover.FourClassesLarge.of_mulEquiv
    (CFSG.ComponentClassification.M12Cover.centralizerEquiv θ y)
    (hJ (θ y) ((MulEquiv.orderOf_eq θ y).trans hy))

theorem fourClassesLarge_mulAut_of_mulEquiv {Y R : Type*} [Group Y] [Group R]
    (e : R ≃* MulAut Y)
    (hR : ∀ r : R, orderOf r = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R))) :
    ∀ x : MulAut Y, orderOf x = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({x} : Set (MulAut Y))) := by
  intro x hx
  obtain ⟨r, rfl⟩ := e.surjective x
  have hr : orderOf r = 2 := (MulEquiv.orderOf_eq e r).symm.trans hx
  exact CFSG.ComponentClassification.M12Cover.FourClassesLarge.of_mulEquiv
    (CFSG.ComponentClassification.M12Cover.centralizerEquiv e r).symm (hR r hr)

theorem oddCore_bot_of_subgroup_iso {G N : Type*} [Group G] [Group N] (K : Subgroup G)
    (L : Subgroup N) (e : K ≃* L) (hL : CFSG.oddCore ↥L = ⊥) : CFSG.oddCore ↥K = ⊥ :=
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv e.symm hL

theorem oddCore_bot_of_map {G N : Type*} [Group G] [Group N] (f : G →* N)
    (hf : Function.Injective f) (K : Subgroup G) (L : Subgroup N) (hL : K.map f = L)
    (hLodd : CFSG.oddCore ↥L = ⊥) : CFSG.oddCore ↥K = ⊥ := by
  subst hL
  exact oddCore_bot_of_subgroup_iso K (K.map f) (K.equivMapOfInjective f hf) hLodd

theorem oddCore_fixSub_of_fi24CJ
    {G : Type*} [Group G] (θ : G ≃* CFSG.Sporadic.Fi24.J) (α : MulAut G)
    (r : CFSG.Sporadic.Fi24.R) (hr : ∀ x : G, θ (α x) = CFSG.Sporadic.Fi24.conjJ r (θ x))
    (hCJ : CFSG.oddCore ↥(CFSG.Sporadic.FischerOddCore.fi24CJ r) = ⊥) :
    CFSG.oddCore ↥(CFSG.Sporadic.Schreier.fixSub α) = ⊥ :=
  oddCore_bot_of_subgroup_iso (CFSG.Sporadic.Schreier.fixSub α)
    (CFSG.Sporadic.FischerOddCore.fi24CJ r) (CFSG.Sporadic.FischerOddCore.fixSubEquivCJ θ α r hr)
    hCJ


theorem finite_fi24prime : Finite Blueprint.NativeSporadic.Fi24prime :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_Fi24prime]; norm_num)

theorem index_innAut_fi24prime_dvd_two :
    (CFSG.EvenSporadicStandard.Finkelstein77.innAut Blueprint.NativeSporadic.Fi24prime).index
      ∣ 2 :=
  @CFSG.EvenSporadicStandard.HypOne.index_dvd_two_of_card_le
    Blueprint.NativeSporadic.Fi24prime Units.instGroup finite_fi24prime
    (@CFSG.EvenSporadicStandard.HypOne.conj_injective_of_center_eq_bot
      Blueprint.NativeSporadic.Fi24prime Units.instGroup
      CFSG.Sporadic.FischerOddCore.center_fi24prime)
    (le_of_eq CFSG.Sporadic.Schreier.Fi24.card_mulAut_fi24prime)

theorem oddCore_centralizer_fi24prime (t : Blueprint.NativeSporadic.Fi24prime)
    (ht : orderOf t = 2) :
    CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Blueprint.NativeSporadic.Fi24prime)) = ⊥ := by
  haveI := finite_fi24prime
  have hC : Subgroup.centralizer ((⊤ : Subgroup Blueprint.NativeSporadic.Fi24prime) :
      Set Blueprint.NativeSporadic.Fi24prime) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ,
      CFSG.Sporadic.FischerOddCore.center_fi24prime]
  exact (CFSG.Sporadic.FischerOddCore.CTUC_Fi24prime_almost_simple_involution_centralizer_odd_core_trivial
    (⊤ : Subgroup Blueprint.NativeSporadic.Fi24prime) ⟨Subgroup.topEquiv⟩ hC).2 t ht

theorem fi24AutEquiv_apply_eq (r : CFSG.Sporadic.Fi24.R) (x : Blueprint.NativeSporadic.Fi24prime) :
    CFSG.Sporadic.FischerOddCore.fi24AutEquiv r x =
      CFSG.Sporadic.Fi24.fi24EquivJ.symm
        (CFSG.Sporadic.Fi24.conjJ r (CFSG.Sporadic.Fi24.fi24EquivJ x)) :=
  rfl

theorem oddCore_fixSub_fi24prime (α : MulAut Blueprint.NativeSporadic.Fi24prime)
    (hα2 : α * α = 1)
    (hαinn : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      Blueprint.NativeSporadic.Fi24prime) :
    CFSG.oddCore ↥(@CFSG.Sporadic.Schreier.fixSub Blueprint.NativeSporadic.Fi24prime
      Units.instGroup α) = ⊥ := by
  obtain ⟨r, rfl⟩ := CFSG.Sporadic.FischerOddCore.fi24AutEquiv.surjective α
  have hr2 : r * r = 1 := by
    apply CFSG.Sporadic.FischerOddCore.fi24AutEquiv.injective
    rw [map_mul, hα2, map_one]
  have hrJR : r ∉ CFSG.Sporadic.Fi24.JR := fun h => by
    obtain ⟨g, hg⟩ := (CFSG.Sporadic.FischerOddCore.fi24_mem_JR_iff r).1 h
    exact hαinn (MonoidHom.mem_range.2 ⟨g, hg.symm⟩)
  have hr1 : r ≠ 1 := fun h => hrJR (by rw [h]; exact Subgroup.one_mem _)
  have hr_sq : r ^ 2 = 1 := by rw [sq]; exact hr2
  have hrord : orderOf r = 2 := orderOf_eq_prime hr_sq hr1
  have hCJ : CFSG.oddCore ↥(CFSG.Sporadic.FischerOddCore.fi24CJ r) = ⊥ :=
    oddCore_bot_of_map CFSG.Sporadic.Fi24.jR CFSG.Sporadic.Fi24.jR_injective
      (CFSG.Sporadic.FischerOddCore.fi24CJ r)
      (CFSG.Sporadic.Fi24.JR ⊓ Subgroup.centralizer ({r} : Set CFSG.Sporadic.Fi24.R))
      (by rw [CFSG.Sporadic.FischerOddCore.fi24CJ, Subgroup.map_comap_eq,
        CFSG.Sporadic.Fi24.range_jR])
      (CFSG.Sporadic.FischerOddCore.CTUC_Fi24_all_extension_involution_centralizers_odd_core_trivial
        r hrord).2
  have hrel : ∀ x : Blueprint.NativeSporadic.Fi24prime,
      CFSG.Sporadic.Fi24.fi24EquivJ (CFSG.Sporadic.FischerOddCore.fi24AutEquiv r x) =
        CFSG.Sporadic.Fi24.conjJ r (CFSG.Sporadic.Fi24.fi24EquivJ x) := fun x => by
    rw [fi24AutEquiv_apply_eq, MulEquiv.apply_symm_apply]
  exact @oddCore_fixSub_of_fi24CJ Blueprint.NativeSporadic.Fi24prime Units.instGroup
    CFSG.Sporadic.Fi24.fi24EquivJ (CFSG.Sporadic.FischerOddCore.fi24AutEquiv r) r hrel hCJ

theorem hypothesisOne_fi24prime_of_leaves
    (hFin : ∀ j : CFSG.Sporadic.Fi24.J, orderOf j = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({j} : Set CFSG.Sporadic.Fi24.J)))
    (hFout : ∀ r : CFSG.Sporadic.Fi24.R, orderOf r = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set CFSG.Sporadic.Fi24.R))) :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      CFSG.Blueprint.NativeSporadic.Fi24prime :=
  @CFSG.EvenSporadicStandard.HypOne.hypothesisOne_of_aut Blueprint.NativeSporadic.Fi24prime
    Units.instGroup finite_fi24prime CFSG.Sporadic.FischerOddCore.center_fi24prime
    index_innAut_fi24prime_dvd_two oddCore_centralizer_fi24prime oddCore_fixSub_fi24prime
    (@fourClassesLarge_centralizer_of_mulEquiv Blueprint.NativeSporadic.Fi24prime
      CFSG.Sporadic.Fi24.J Units.instGroup CFSG.Sporadic.Fi24.J.toGroup
      CFSG.Sporadic.Fi24.fi24EquivJ hFin)
    (@fourClassesLarge_mulAut_of_mulEquiv Blueprint.NativeSporadic.Fi24prime
      CFSG.Sporadic.Fi24.R Units.instGroup CFSG.Sporadic.Fi24.R.toGroup
      CFSG.Sporadic.FischerOddCore.fi24AutEquiv hFout)

theorem hypothesisOne_carrier_fi24prime_of_leaves
    (hFin : ∀ j : CFSG.Sporadic.Fi24.J, orderOf j = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({j} : Set CFSG.Sporadic.Fi24.J)))
    (hFout : ∀ r : CFSG.Sporadic.Fi24.R, orderOf r = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set CFSG.Sporadic.Fi24.R))) :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
  @CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv Blueprint.NativeSporadic.Fi24prime
    (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) Units.instGroup
    (CFSG.Blueprint.NativeSporadic.carrierGroup .Fi24Prime)
    (MulEquiv.refl Blueprint.NativeSporadic.Fi24prime)
    (hypothesisOne_fi24prime_of_leaves hFin hFout)

end CFSG.EvenSporadicStandard.YS14

end
