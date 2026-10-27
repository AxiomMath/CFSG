module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4OrthComp
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsOrth
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrth
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthType
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem fixedLayer_of_isD42_component {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hK : Nat.card K = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : orthDerived Q} (hx3 : orderOf x = 3) {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))))
    (hiso : IsCatalogLieIso ↥L IsD42Index) :
    Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
      L = fixedComponentImage Q (x : V ≃ₗ[K] V) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hm : LieModel ↥L .POmegaPlus 4 2 1 := lieModel_of_isD42 hiso
  have hcardL : Nat.card ↥L = CFSG.Open.ordD 4 2 := by
    have h1 := CFSG.SeitzReduction.OmegaPilot.card_of_lieModel_POmega_two (X := ↥L)
      (Or.inl rfl) hm
    simpa only [CFSG.SeitzReduction.F4Pilot.evenLieOrder, pow_one] using h1
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hiso
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, hf⟩ := hd
    have hq2 : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hp, hf]; norm_num
    have : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group :=
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.isSimpleGroup_lie_typeD_two 4
        ⟨.D 4 q, hv⟩ q hq2 rfl
    have hsL : IsSimpleGroup ↥L := e.isSimpleGroup
    have hZ : Subgroup.center ↥L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
      · exact h
      · exfalso
        have hcomm : commutator ↥L = ⊥ := by
          rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
          intro a _ c _
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) c).symm
        rw [hL.2.2.1] at hcomm
        obtain ⟨x, y, hxy⟩ := hsL.toNontrivial
        have hx1 : x = 1 := Subgroup.mem_bot.mp (hcomm ▸ Subgroup.mem_top x)
        have hy1 : y = 1 := Subgroup.mem_bot.mp (hcomm ▸ Subgroup.mem_top y)
        exact hxy (hx1.trans hy1.symm)
    have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = CFSG.Open.ordD 4 2 := by
      rw [← hcardL]
      exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).toEquiv
    exact CFSG.LocalAnalysis.GLTheoremA.TriD4.eq_fixedComponentImage_of_card_two
      hK hQ x hx3 hL hcard
  | _ => exact hd.elim

theorem exists_lift_of_classicalModel_two {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S] {n : ℕ}
    (hG : StatedClassicalModel S t n 2 1) {b : S} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V) (e : S ≃* ProjOrthDerived Q)
      (x : orthDerived Q),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Nat.card K = 2 ∧ piOrth Q x = e b ∧
        orderOf x = 3 ∧ Module.finrank K V = 2 * n := by
  classical
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, -, hdim, hcard, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.exists_projOrth_model_two (t := t) ht hG
  have hK2 : Nat.card K = 2 := hcard.trans (pow_one 2)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl (hK2.trans (pow_one 2).symm)
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have := hV
    refine hb1 (e.injective ?_)
    obtain ⟨g, hg⟩ := piOrth_surjective (Q := Q) (e b)
    have hg1 : g = 1 := Subtype.ext (LinearEquiv.ext fun _ => Subsingleton.elim _ _)
    rw [← hg, hg1, map_one, map_one]
  obtain ⟨x, hx⟩ := piOrth_surjective (Q := Q) (e b)
  have hx3 : orderOf x = 3 := by
    rw [← orderOf_injective (piOrth Q) (piOrth_injective hQ) x, hx, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hb3 hb1
  exact ⟨K, inferInstance, inferInstance, V, inferInstance, inferInstance, inferInstance, Q, e, x,
    hQ, hK2, hx, hx3, hdim⟩

theorem map_component_eq_fixedLayer {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hK : Nat.card K = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : orthDerived Q} (hx3 : orderOf x = 3) {S : Type} [Group S]
    (e : S ≃* ProjOrthDerived Q) {b : S} {J : Subgroup S} (hx : piOrth Q x = e b)
    (hcomp : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({b} : Set S)))
    (hiso : IsCatalogLieIso ↥J IsD42Index) :
    Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
      J.map (e : S →* ProjOrthDerived Q) = fixedComponentImage Q (x : V ≃ₗ[K] V) := by
  have hcen : (Subgroup.centralizer ({b} : Set S)).map (e : S →* ProjOrthDerived Q) =
      Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q)) := by
    rw [hx]
    exact CFSG.RankThree.PartOne.map_centralizer_singleton_mulEquiv_good e b
  have hL := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hcomp
  rw [hcen] at hL
  have hiso' : IsCatalogLieIso ↥(J.map (e : S →* ProjOrthDerived Q)) IsD42Index := by
    obtain ⟨d, hd, ⟨f⟩⟩ := hiso
    exact ⟨d, hd, ⟨(Subgroup.equivMapOfInjective J (e : S →* ProjOrthDerived Q)
      e.injective).symm.trans f⟩⟩
  exact fixedLayer_of_isD42_component hK hQ hx3 hL hiso'

theorem exists_fixedLayer_of_isD42_component {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S] {n : ℕ}
    (hG : StatedClassicalModel S t n 2 1) {b : S} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    {J : Subgroup S} (hJ : GLAPComponent 3 (Subgroup.centralizer ({b} : Set S)) J)
    (hiso : IsCatalogLieIso ↥J IsD42Index) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V) (e : S ≃* ProjOrthDerived Q)
      (x : orthDerived Q),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Nat.card K = 2 ∧ piOrth Q x = e b ∧
        orderOf x = 3 ∧ Module.finrank K V = 2 * n ∧
        Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
        J.map (e : S →* ProjOrthDerived Q) = fixedComponentImage Q (x : V ≃ₗ[K] V) := by
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_omega
    (Or.inr ht) hG Nat.prime_three (by norm_num) (by norm_num) b hb3
  rw [← OrthBlocks.fixSubgroup_conj_eq_centralizer'] at hJ
  have hcomp : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({b} : Set S)) := by
    rw [← OrthBlocks.fixSubgroup_conj_eq_centralizer']
    exact (glaPComponent_isComponent_of_le_layer hJ
      (hlayer J hJ.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ))).1
  obtain ⟨K, _, _, V, _, _, _, Q, e, x, hrest⟩ :=
    exists_lift_of_classicalModel_two ht hG hb3 hb1
  obtain ⟨hQ, hK, hx, hx3, hdim⟩ := hrest
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl (hK.trans (pow_one 2).symm)
  obtain ⟨hW8, hfix⟩ := map_component_eq_fixedLayer hK hQ hx3 e hx hcomp hiso
  exact ⟨K, inferInstance, inferInstance, V, inferInstance, inferInstance, inferInstance, Q, e, x,
    hQ, hK, hx, hx3, hdim, hW8, hfix⟩

end CFSG.HardMathSupport.Dickson.Sec6

end
