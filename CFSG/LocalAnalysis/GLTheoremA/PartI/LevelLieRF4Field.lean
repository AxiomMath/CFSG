module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Gen
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (commutator_reeGamma_F4_zero_data tits_valid)

theorem rf4_level_of_derived {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    (X : Subgroup G) {T : Type} [Group T] [IsSimpleGroup T]
    (e : ↥(commutator ↥X) ≃* T) (hnc : ∃ a b : T, a * b ≠ b * a) (hdvd : p ∣ Nat.card T)
    (hk : kLevel p T ≤ 2) (I : Subgroup G) (hI : GLAPComponent p X I) :
    kLevel p (PSimple p I) ≤ 2 := by
  have hDeq : (commutator ↥X).map X.subtype = ⁅X, X⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  let eD : ↥((commutator ↥X).map X.subtype) ≃* ↥(commutator ↥X) :=
    ((commutator ↥X).equivMapOfInjective X.subtype X.subtype_injective).symm
  haveI : IsSimpleGroup ↥((commutator ↥X).map X.subtype) := (eD.trans e).isSimpleGroup
  have hncD : ∃ a b : ↥((commutator ↥X).map X.subtype), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨(eD.trans e).symm x, (eD.trans e).symm y, fun h => hxy ?_⟩
    have h' := congrArg (eD.trans e) h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  have hdvd' : p ∣ Nat.card ↥((commutator ↥X).map X.subtype) := by
    rw [Nat.card_congr (eD.trans e).toEquiv]
    exact hdvd
  have hk' : kLevel p ↥((commutator ↥X).map X.subtype) ≤ 2 := by
    rw [kLevel_congr p (eD.trans e)]
    exact hk
  have hPD : ∀ P : Subgroup G, P ≤ X → ⁅P, P⁆ = P → P ≤ (commutator ↥X).map X.subtype := by
    intro P hPX hP
    rw [hDeq]
    exact hP.symm.le.trans (Subgroup.commutator_mono hPX hPX)
  exact rf4_level_of_simple_derived hp (D := (commutator ↥X).map X.subtype)
    (Subgroup.map_subtype_le _) hPD hncD hdvd' hk' I hI

theorem rf4_claim_one {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) (hdvd : p ∣ Nat.card G) (hk : kLevel p G ≤ 2) :
    ∀ I : Subgroup G, GLAPComponent p (fixSubgroup (1 : MulAut G)) I →
      kLevel p (PSimple p I) ≤ 2 := by
  have htop : fixSubgroup (1 : MulAut G) = ⊤ := by
    ext x
    rw [mem_fixSubgroup]
    simp
  intro I hI
  rw [htop] at hI
  haveI : IsSimpleGroup ↥(⊤ : Subgroup G) := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hnc' : ∃ a b : ↥(⊤ : Subgroup G), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨Subgroup.topEquiv.symm x, Subgroup.topEquiv.symm y, fun h => hxy ?_⟩
    have h' := congrArg Subgroup.topEquiv h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  have hdvd' : p ∣ Nat.card ↥(⊤ : Subgroup G) := by
    rw [Subgroup.card_top]
    exact hdvd
  have hk' : kLevel p ↥(⊤ : Subgroup G) ≤ 2 := by
    rw [kLevel_congr p (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G)]
    exact hk
  exact rf4_level_of_simple_derived hp (X := ⊤) (D := ⊤) le_rfl (fun _ _ _ => le_top) hnc'
    hdvd' hk' I hI

theorem rf4_claim_field {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p = 2 * a + 1) (hp35 : p = 3 ∨ p = 5) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∀ I : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a),
      GLAPComponent p (fixSubgroup (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a σ)) I →
        kLevel p (PSimple p I) ≤ 2 := by
  classical
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨b, hb, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  have hb0 : b = 0 := by
    have h1 : (2 * b + 1) * p = 1 * p := by rw [one_mul, hb, hpa]
    have h2 : 2 * b + 1 = 1 := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  have hk2 : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 := by simpa using hkcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
  haveI hchar : CharP (CFSG.LieType.Chevalley.fixSubfield σ) CFSG.LieType.Ree.ReeTag.F4.prime := by
    have : Fintype (CFSG.LieType.Chevalley.fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * 0 + 1) (by rw [← Nat.card_eq_fintype_card, hkcard]; rfl)
  have hFix : fixSubgroup (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a σ) =
      (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    rfl
  let eX : ↥(fixSubgroup (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a σ)) ≃*
      ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma (CFSG.LieType.Chevalley.fixSubfield σ) 0) :=
    (((fixSubgroup (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
        (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a).subtype
        (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((CFSG.LieType.Ree.ReeTag.F4.reeGamma (CFSG.LieType.Chevalley.fixSubfield σ) 0).equivMapOfInjective
      _ (CFSG.LieType.Chevalley.baseChangeGL_injective (τ := CFSG.LieType.Ree.ReeTag.F4.tag)
        (CFSG.LieType.Chevalley.fixSubfield σ).subtype)).symm
  obtain ⟨hs0, hnc0, hcat0⟩ :=
    commutator_reeGamma_F4_zero_data (k := CFSG.LieType.Chevalley.fixSubfield σ) hk2
  obtain ⟨hcat⟩ := hcat0
  haveI := hs0
  haveI hsT : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group :=
    (MulEquiv.isSimpleGroup_congr hcat).mp hs0
  have hncT : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnc0
    exact ⟨hcat x, hcat y, fun h => hxy (hcat.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcardT : Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group = 17971200 :=
    rf4_card_tits ⟨MulEquiv.refl _⟩
  have hdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group := by
    rw [hcardT]
    rcases hp35 with rfl | rfl <;> norm_num
  have hk : kLevel p (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group ≤ 2 := by
    apply rf4_kLevel_le_two
    exact ⟨TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩, by simpa [k2, k2Lie] using hp35,
      ⟨MulEquiv.refl _⟩⟩
  intro I hI
  exact rf4_level_of_derived hp _ ((rf4_commutatorEquiv eX).trans hcat) hncT hdvd hk I hI

end CFSG.LocalAnalysis.GLTheoremA
