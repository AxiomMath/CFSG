module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.ConjA0
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.D4G2All
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2
import CFSG.LieType.SteinbergBROddLinearThreeParabolic
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
  (d4FixedG2EquivAll d4FixedToG2_g2OrbitXUnitAll d4FixedToG2_g2OrbitYUnitAll)

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

section Leaves


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem card_fixSubfield_odd (P : D4ParOdd ℓ f X σ) : Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((ℓ ^ f) ^ 1) := fun c => by rw [pow_one]; exact P.frob c
  have h := card_orbitField_D4_orientation P.prime P.one_le P.card (Or.inl rfl) hσ'
    ⟨1, by decide⟩
  rw [show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_orbitField, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  rfl

theorem three_le_enatCard_fixSubfield_odd (P : D4ParOdd ℓ f X σ) :
    (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
  rw [ENat.card_eq_coe_natCard, card_fixSubfield_odd P]
  have h5 := P.five_le
  exact_mod_cast (by omega : 3 ≤ ℓ ^ f)

@[expose] noncomputable def trialityG2InclOdd (P : D4ParOdd ℓ f X σ) :
    adjointGroup Tag.G2 (fixSubfield σ) →* C0 σ :=
  (trialityFixIncl σ).comp
    (d4FixedG2EquivAll (fixSubfield σ) (three_le_enatCard_fixSubfield_odd P)).symm

theorem trialityG2InclOdd_injective (P : D4ParOdd ℓ f X σ) :
    Function.Injective (trialityG2InclOdd P) :=
  (trialityFixIncl_injective σ).comp (MulEquiv.injective _)

theorem trialityG2InclOdd_d4FixedG2EquivAll (P : D4ParOdd ℓ f X σ)
    (g : twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id _)) :
    trialityG2InclOdd P
        (d4FixedG2EquivAll (fixSubfield σ) (three_le_enatCard_fixSubfield_odd P) g) =
      trialityFixIncl σ g := by
  change trialityFixIncl σ ((d4FixedG2EquivAll (fixSubfield σ)
    (three_le_enatCard_fixSubfield_odd P)).symm (d4FixedG2EquivAll (fixSubfield σ)
      (three_le_enatCard_fixSubfield_odd P) g)) = _
  rw [MulEquiv.symm_apply_apply]

theorem fixSubfieldRestrict_toRingHom_eq_id_odd (σ : X ≃+* X) :
    (fixSubfieldRestrict σ σ).toRingHom = RingHom.id (fixSubfield σ) :=
  RingHom.ext fun c => Subtype.ext (by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_fixSubfieldRestrict]
    exact c.2)

theorem trialityFixImage_eq_trialityFieldImage_odd :
    trialityFixImage σ = trialityFieldImage σ σ := by
  unfold trialityFixImage trialityFieldImage
  rw [d4_twistedFixedGroup_id_eq_graphFixedRootGroup, fixSubfieldRestrict_toRingHom_eq_id_odd]

theorem mem_range_trialityFixIncl_iff_odd (P : D4ParOdd ℓ f X σ) (g : C0 σ) :
    g ∈ (trialityFixIncl σ).range ↔ tauAut σ g = g := by
  rw [show tauAut σ g = g ↔ fieldActor σ σ g = g from Iff.rfl,
    ← CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_mem_trialityFieldImage_self_iff σ P.sigma_cube g,
    ← trialityFixImage_eq_trialityFieldImage_odd]
  constructor
  · rintro ⟨g', rfl⟩
    exact ⟨g', g'.2, rfl⟩
  · rintro ⟨g', hg', hgg'⟩
    exact ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩

theorem mem_range_trialityG2InclOdd_iff (P : D4ParOdd ℓ f X σ) (g : C0 σ) :
    g ∈ (trialityG2InclOdd P).range ↔ tauAut σ g = g := by
  rw [← mem_range_trialityFixIncl_iff_odd P]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨d4FixedG2EquivAll (fixSubfield σ) (three_le_enatCard_fixSubfield_odd P) y,
      trialityG2InclOdd_d4FixedG2EquivAll P y⟩

theorem trialityG2InclOdd_range (P : D4ParOdd ℓ f X σ) : (trialityG2InclOdd P).range = Gsub σ := by
  ext g
  rw [mem_range_trialityG2InclOdd_iff P g]
  rfl

theorem g2RootSL2_short_upper_incl_odd (P : D4ParOdd ℓ f X σ) (c : fixSubfield σ) :
    trialityG2InclOdd P (g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Upper c)) =
      iotaAOdd P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
        (CFSG.LieType.Steinberg.sl2Upper c)) := by
  have hz : g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Upper c) =
      d4FixedG2EquivAll (fixSubfield σ) (three_le_enatCard_fixSubfield_odd P)
        ⟨g2OrbitXUnit (fixSubfield σ) g2s c, g2OrbitXUnit_mem g2s c⟩ :=
    Subtype.ext ((simpleRootSL2_uSL g2s c).trans (d4FixedToG2_g2OrbitXUnitAll g2s c).symm)
  have e : Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
      (CFSG.LieType.Steinberg.sl2Upper c) = CFSG.LieType.Steinberg.sl2Upper (c : X) :=
    map_uSL (f := (fixSubfield σ).subtype) c
  rw [hz, trialityG2InclOdd_d4FixedG2EquivAll]
  apply Subtype.ext
  rw [coe_trialityFixIncl_g2Upper σ c,
    g2OrbitXUnit_eq_orbitX_of_fixed ((mem_fixSubfield σ).1 c.2) g2s,
    e, coe_iotaAOdd P (CFSG.LieType.Steinberg.sl2Upper (c : X)),
    slShort_upper_eq_orbit_odd P (c : X), orbitRankOneHom_uSL]
  rfl

theorem g2RootSL2_short_lower_incl_odd (P : D4ParOdd ℓ f X σ) (c : fixSubfield σ) :
    trialityG2InclOdd P (g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Lower c)) =
      iotaAOdd P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
        (CFSG.LieType.Steinberg.sl2Lower c)) := by
  have hz : g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Lower c) =
      d4FixedG2EquivAll (fixSubfield σ) (three_le_enatCard_fixSubfield_odd P)
        ⟨g2OrbitYUnit (fixSubfield σ) g2s c, g2OrbitYUnit_mem g2s c⟩ :=
    Subtype.ext ((simpleRootSL2_vSL g2s c).trans (d4FixedToG2_g2OrbitYUnitAll g2s c).symm)
  have e : Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
      (CFSG.LieType.Steinberg.sl2Lower c) = CFSG.LieType.Steinberg.sl2Lower (c : X) :=
    map_vSL (f := (fixSubfield σ).subtype) c
  rw [hz, trialityG2InclOdd_d4FixedG2EquivAll]
  apply Subtype.ext
  rw [coe_trialityFixIncl_g2Lower σ c,
    g2OrbitYUnit_eq_orbitY_of_fixed ((mem_fixSubfield σ).1 c.2) g2s,
    e, coe_iotaAOdd P (CFSG.LieType.Steinberg.sl2Lower (c : X)),
    slShort_lower_eq_orbit_odd P (c : X), orbitRankOneHom_vSL]
  rfl

theorem g2RootSL2_short_hom_eq_odd (P : D4ParOdd ℓ f X σ) :
    (trialityG2InclOdd P).comp (g2RootSL2 g2s (fixSubfield σ)) =
      (iotaAOdd P).comp (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype) := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixSubfield σ)) ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact g2RootSL2_short_upper_incl_odd P c
  · exact g2RootSL2_short_lower_incl_odd P c

theorem exists_g2_short_preimage_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ}
    (hx : IsClassX σ x) (hxA : x ∈ A0sub σ) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
      trialityG2InclOdd P (g2RootSL2 g2s (fixSubfield σ) s) = x ∧
      (g2RootSL2 g2s (fixSubfield σ) s) ^ 3 = 1 ∧ g2RootSL2 g2s (fixSubfield σ) s ≠ 1 := by
  obtain ⟨s, hs⟩ := (mem_A0sub_iff_odd P).mp hxA
  have hxz : trialityG2InclOdd P (g2RootSL2 g2s (fixSubfield σ) s) = x := by
    rw [hs]
    exact DFunLike.congr_fun (g2RootSL2_short_hom_eq_odd P) s
  refine ⟨s, hxz, trialityG2InclOdd_injective P (by rw [map_pow, hxz, hx.1, map_one]),
    fun h => hx.2.1 ?_⟩
  rw [← hxz, h, map_one]

theorem exists_g2_layer_subgroup_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : IsClassX σ x)
    (hxA : x ∈ A0sub σ) :
    ∃ (M : Subgroup (C0 σ)) (z' : adjointGroup Tag.G2 (fixSubfield σ)),
      M ≤ cenX σ x ∧ M ≤ Gsub σ ∧ z' ∈ KS11Lie4Proof.g2ShortSL2 (fixSubfield σ) ∧ z' ^ 3 = 1 ∧
        z' ≠ 1 ∧ Nonempty
          (Subgroup.centralizer ({z'} : Set (adjointGroup Tag.G2 (fixSubfield σ))) ≃* M) := by
  obtain ⟨s, hxz, hz₁3, hz₁1⟩ := exists_g2_short_preimage_odd P hx hxA
  set z₁ := g2RootSL2 g2s (fixSubfield σ) s
  obtain ⟨hz3, hz1⟩ := conj_pow_three_ne_one (g2WeylRep (fixSubfield σ)) z₁ hz₁3 hz₁1
  refine ⟨(Subgroup.centralizer ({z₁} : Set (adjointGroup Tag.G2 (fixSubfield σ)))).map
      (trialityG2InclOdd P), g2WeylRep (fixSubfield σ) * z₁ * (g2WeylRep (fixSubfield σ))⁻¹, ?_, ?_,
    conj_g2RootSL2_short_mem (fixSubfield σ) s, hz3, hz1,
    ⟨(centralizerConjEquiv (g2WeylRep (fixSubfield σ)) z₁).symm.trans
      ((Subgroup.centralizer ({z₁} : Set (adjointGroup Tag.G2 (fixSubfield σ)))).equivMapOfInjective
        (trialityG2InclOdd P) (trialityG2InclOdd_injective P))⟩⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.centralizer ({z₁} : Set (adjointGroup Tag.G2 (fixSubfield σ))) := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    rw [← hxz, ← map_mul, ← map_mul, hg']
  · rintro _ ⟨g, -, rfl⟩
    rw [← trialityG2InclOdd_range P]
    exact ⟨g, rfl⟩

theorem card_centralizer_short_unitary_odd {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (h3 : 3 ∣ Nat.card K + 1)
    {z : adjointGroup .G2 K} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU (p := ℓ) (f := f) hK h3 hdeg
    hzS hz3 hz1
  have hL : Nat.card L = (ℓ ^ f) ^ 2 := by rw [KS11Lie4Proof.natCard_quadratic hdeg, hK]
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hL

theorem g2_layer_linear_odd (P : D4ParOdd ℓ f X σ) (hq1 : ℓ ^ f % 3 = 1) {x : C0 σ}
    (hx : IsClassX σ x) (hxA : x ∈ A0sub σ) :
    ∃ M : Subgroup (C0 σ), M ≤ cenX σ x ∧ M ≤ Gsub σ ∧ Group.IsPerfect M ∧
      Nat.card M = (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 - 1)) := by
  obtain ⟨M, z', hMC, hMG, hzS, hz3, hz1, ⟨eM⟩⟩ := exists_g2_layer_subgroup_odd P hx hxA
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_odd P
  have h31 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    rw [hkc]
    have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ P.prime.pos
    omega
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_SL3 h31 hzS hz3 hz1
  refine ⟨M, hMC, hMG,
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (eM.symm.trans e).symm
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))).1, ?_⟩
  rw [Nat.card_congr (eM.symm.trans e).toEquiv,
    CFSG.LieType.SteinbergBR.BlockPar.card_SL_three', hkc]

theorem g2_layer_unitary_odd (P : D4ParOdd ℓ f X σ) (hq2 : ℓ ^ f % 3 = 2) {x : C0 σ}
    (hx : IsClassX σ x) (hxA : x ∈ A0sub σ) :
    ∃ M : Subgroup (C0 σ), M ≤ cenX σ x ∧ M ≤ Gsub σ ∧ Group.IsPerfect M ∧
      Nat.card M = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  obtain ⟨M, z', hMC, hMG, hzS, hz3, hz1, ⟨eM⟩⟩ := exists_g2_layer_subgroup_odd P hx hxA
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_odd P
  have h3 : 3 ∣ Nat.card (fixSubfield σ) + 1 := by
    rw [hkc]
    omega
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hkc]
    have h5 := P.five_le
    omega
  refine ⟨M, hMC, hMG,
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eM
      (KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hk4 hzS hz3 hz1)).1, ?_⟩
  rw [← Nat.card_congr eM.toEquiv,
    card_centralizer_short_unitary_odd P.prime P.one_le hkc h3 hzS hz3 hz1]

theorem tau_fixes_layer_linear_odd (P : D4ParOdd ℓ f X σ) (hq1 : ℓ ^ f % 3 = 1) {x : C0 σ}
    (hx : IsClassX σ x) (hxA : x ∈ A0sub σ)
    (hcard : Nat.card (layerSub σ x) = (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 - 1))) :
    ∀ d ∈ layerSub σ x, tauAut σ d = d := by
  haveI : Finite (C0 σ) := finite_C0
  obtain ⟨M, hMC, hMG, hMp, hMcard⟩ := g2_layer_linear_odd P hq1 hx hxA
  exact layer_fixed_of_perfect_card M hMC hMG hMp (by rw [hcard, hMcard])

theorem tau_fixes_layer_unitary_odd (P : D4ParOdd ℓ f X σ) (hq2 : ℓ ^ f % 3 = 2) {x : C0 σ}
    (hx : IsClassX σ x) (hxA : x ∈ A0sub σ)
    (hcard : Nat.card (layerSub σ x) = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1)) :
    ∀ d ∈ layerSub σ x, tauAut σ d = d := by
  haveI : Finite (C0 σ) := finite_C0
  obtain ⟨M, hMC, hMG, hMp, hMcard⟩ := g2_layer_unitary_odd P hq2 hx hxA
  exact layer_fixed_of_perfect_card M hMC hMG hMp (by rw [hcard, hMcard])

end Leaves

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
