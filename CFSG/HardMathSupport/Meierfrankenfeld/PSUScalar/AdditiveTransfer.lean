module

public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.GroupTheory.OddKernelImage
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral
public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
  CFSG.HardMathSupport.GuralnickMalle

@[expose] noncomputable def binRepOfHom {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} {Γ : Type*} [Group Γ]
    (φ : Γ →* ↥L) : Representation (ZMod 2) Γ W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ).toMonoidHom.comp (L.subtype.comp φ))

theorem binRepOfHom_apply {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {Γ : Type*} [Group Γ] (φ : Γ →* ↥L) (γ : Γ) (w : W) :
    binRepOfHom θ φ γ w = binPsi θ ((φ γ : ↥L) : MulAut V) w := rfl

theorem binRepOfHom_eq_one_iff {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {Γ : Type*} [Group Γ] (φ : Γ →* ↥L) (γ : Γ) :
    binRepOfHom θ φ γ = 1 ↔ φ γ = 1 := by
  constructor
  · intro h
    have h1 : binPsi θ ((φ γ : ↥L) : MulAut V) = 1 := by
      ext w
      have h2 := LinearMap.congr_fun h w
      rw [binRepOfHom_apply] at h2
      simpa using h2
    apply Subtype.ext
    exact (binPsi θ).injective (h1.trans (map_one _).symm)
  · intro h
    have h1 : ((φ γ : ↥L) : MulAut V) = 1 := by rw [h]; rfl
    change (binPsi θ ((φ γ : ↥L) : MulAut V)).toLinearMap = 1
    rw [h1, map_one]
    rfl

theorem binRepOfHom_isIrreducible {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {Γ : Type*} [Group Γ] (φ : Γ →* ↥L) (hW : Nontrivial W)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hφ : Function.Surjective φ) :
    (binRepOfHom θ φ).IsIrreducible := by
  obtain ⟨-, hirr⟩ := hirr
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨hW, fun U hU => B42L2.irr_map θ hirr U ?_⟩
  rintro _ ⟨l, hl, rfl⟩ u hu
  obtain ⟨x, hx⟩ := hφ ⟨l, hl⟩
  have h1 := hU x u hu
  rw [binRepOfHom_apply, hx] at h1
  exact h1

theorem fixSubGen_eq_fixGL_map {k W Γ : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Group Γ] (ρ : Γ →* (W ≃ₗ[k] W)) (P : Subgroup Γ) :
    fixSubGen (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) P =
      fixGL (P.map ρ) := by
  ext w
  constructor
  · rintro hw h ⟨a, ha, rfl⟩
    exact hw a ha
  · rintro hw a ha
    exact hw _ ⟨a, ha, rfl⟩

theorem natCard_fixSubGen_binRepOfHom {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {Γ : Type*} [Group Γ] (φ : Γ →* ↥L) (P : Subgroup Γ) :
    Nat.card (fixSubGen (binRepOfHom θ φ) P) =
      Nat.card (fixV (P.map (L.subtype.comp φ))) := by
  change Nat.card (fixSubGen (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((binPsi θ).toMonoidHom.comp (L.subtype.comp φ))) P) = _
  rw [fixSubGen_eq_fixGL_map, ← Subgroup.map_map, natCard_fixGL_map]

theorem binRepOfHom_sub_mul_sub_eq_zero {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {Γ : Type*} [Group Γ] (φ : Γ →* ↥L) {Q : Subgroup (MulAut V)} (hQ : IsQuadratic Q)
    {P : Subgroup Γ} (hP : ∀ a ∈ P, ((φ a : ↥L) : MulAut V) ∈ Q) :
    ∀ a ∈ P, ∀ b ∈ P, (binRepOfHom θ φ a - 1) * (binRepOfHom θ φ b - 1) = 0 := by
  intro a ha b hb
  ext w
  have h := B42L2.quad_map θ hQ (binPsi θ ((φ b : ↥L) : MulAut V))
    (Subgroup.mem_map_of_mem ((binPsi θ).toMonoidHom) (hP b hb))
    (binPsi θ ((φ a : ↥L) : MulAut V))
    (Subgroup.mem_map_of_mem ((binPsi θ).toMonoidHom) (hP a ha)) w
  simpa [binRepOfHom_apply, Module.End.mul_apply, LinearMap.sub_apply, sub_eq_zero] using h

theorem exists_additive_of_scalar_core_data {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    {K : Type} [Field K] [Finite K] {m f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (φ : ↥(CFSG.Open.StatedSU m (2 ^ f) K) →* ↥L) (hφs : Function.Surjective φ)
    (hφk : φ.ker ≤
      (CFSG.Open.StatedScalars (Fin m) K).subgroupOf (CFSG.Open.StatedSU m (2 ^ f) K))
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hA1 : A ≠ ⊥)
    (hAel : CFSG.Quasithin.IsElemAbelian2 A) (hAq : CFSG.Quasithin.IsQuadratic A)
    (hAV : Nat.card V ≤ 2 * Nat.card A * Nat.card (CFSG.Quasithin.fixV A)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (ρ : Representation (ZMod 2) ↥(CFSG.Open.StatedSU m (2 ^ f) K) W),
      ρ.IsIrreducible ∧ (∀ g, ρ g = 1 ↔ φ g = 1) ∧
      ∃ P : Subgroup ↥(CFSG.Open.StatedSU m (2 ^ f) K), P ≠ ⊥ ∧ CFSG.Open.IsElemAbelian 2 P ∧
        (∀ a ∈ P, ∀ b ∈ P, (ρ a - 1) * (ρ b - 1) = 0) ∧
        Nat.card W ≤ 2 * CFSG.HardMathSupport.GuralnickMalle.weight1Gen ρ P := by
  classical
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨θ⟩⟩ := exists_binModel_of_binary hV
  let _ : AddCommGroup W := hWadd
  let _ : Module (ZMod 2) W := hWmod
  let _ : Finite W := hWfin
  have hWnt : Nontrivial W := θ.toEquiv.nontrivial_congr.mp hirr.1
  let ρ : Representation (ZMod 2) ↥(CFSG.Open.StatedSU m (2 ^ f) K) W := binRepOfHom θ φ
  have hirrρ : ρ.IsIrreducible := binRepOfHom_isIrreducible θ φ hWnt hirr hφs
  have hker : ∀ g, ρ g = 1 ↔ φ g = 1 := fun g => binRepOfHom_eq_one_iff θ φ g
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · rw [hf0, Nat.pow_zero, one_pow] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact hfpos
  have hcardK : Nat.card K = 2 ^ (2 * f) := by
    rw [hK, ← pow_mul]
    congr 1
    omega
  have hoddK : Odd (Nat.card K - 1) := by
    rw [hcardK]
    obtain ⟨k, hk⟩ : ∃ k, 2 * f = k + 1 := ⟨2 * f - 1, by omega⟩
    rw [hk, pow_succ]
    refine ⟨2 ^ k - 1, ?_⟩
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
    omega
  have hdvdScal : Nat.card ((CFSG.Open.StatedScalars (Fin m) K).subgroupOf
      (CFSG.Open.StatedSU m (2 ^ f) K)) ∣ Nat.card K - 1 :=
    CFSG.Quasithin.Vol2.Ch11.SecA.card_scalars_subgroupOf_dvd _
  have hodd : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat hoddK ((Subgroup.card_dvd_of_le hφk).trans hdvdScal)
  let E : Subgroup ↥L := A.subgroupOf L
  have hE2 : IsPGroup 2 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro e
    refine ⟨1, ?_⟩
    have h2 : e ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hAel.2 ((e.1 : ↥L) : MulAut V) (show ((e.1 : ↥L) : MulAut V) ∈ A from e.2)
    simpa using h2
  have hErange : E ≤ φ.range := by
    rw [MonoidHom.range_eq_top_of_surjective φ hφs]
    exact le_top
  obtain ⟨P, _hP2, hPmap, hPinj⟩ :=
    CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd (Φ := φ) hodd hErange hE2
  have hrange : (φ.comp P.subtype).range = P.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hPcard : Nat.card P = Nat.card E := by
    have h1 : Nat.card ((⊤ : Subgroup P).map (φ.comp P.subtype)) = Nat.card P := by
      rw [Subgroup.card_map_of_injective hPinj, Subgroup.card_top]
    rw [Subgroup.map_top, hrange, hPmap] at h1
    exact h1.symm
  have hEA : Nat.card E = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hPA : Nat.card P = Nat.card A := hPcard.trans hEA
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have hE1 : Nat.card E = 1 := by
      rw [← hPmap, hbot, Subgroup.map_bot, Subgroup.card_bot]
    have hA1' : A = ⊥ := (Subgroup.eq_bot_iff_card A).2 (by rw [← hEA, hE1])
    exact hA1 hA1'
  have hPmem : ∀ a ∈ P, ((φ a : ↥L) : MulAut V) ∈ A := by
    intro a ha
    have hE : φ a ∈ E := hPmap ▸ Subgroup.mem_map_of_mem φ ha
    change φ a ∈ A.subgroupOf L at hE
    exact Subgroup.mem_subgroupOf.mp hE
  have hPcomm : IsMulCommutative P := IsMulCommutative.of_comm fun x y => by
    apply hPinj
    simp only [MonoidHom.comp_apply, map_mul]
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_subtype] using
      hAel.1 ((φ x : ↥L) : MulAut V) (hPmem x x.2)
        ((φ y : ↥L) : MulAut V) (hPmem y y.2)
  have hPsq : ∀ x ∈ P, x ^ 2 = 1 := by
    intro x hx
    have hx' := hPmem x hx
    have hsq : (⟨x, hx⟩ : P) ^ 2 = 1 := by
      apply hPinj
      rw [map_pow, map_one]
      exact Subtype.ext (hAel.2 ((φ x : ↥L) : MulAut V) hx')
    simpa using congrArg Subtype.val hsq
  have hPel : CFSG.Open.IsElemAbelian 2 P := ⟨hPcomm, hPsq⟩
  have hquad : ∀ a ∈ P, ∀ b ∈ P, (ρ a - 1) * (ρ b - 1) = 0 :=
    binRepOfHom_sub_mul_sub_eq_zero θ φ hAq hPmem
  have hmapA : P.map (L.subtype.comp φ) = A := by
    rw [← Subgroup.map_map, hPmap]
    change (A.subgroupOf L).map L.subtype = A
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAL]
  have hfix : Nat.card (fixSubGen ρ P) = Nat.card (fixV A) := by
    have := natCard_fixSubGen_binRepOfHom θ φ P
    rwa [hmapA] at this
  have hineq : Nat.card W ≤ 2 * weight1Gen ρ P := by
    rw [show Nat.card W = Nat.card V from (natCard_eq θ).symm, weight1Gen, hfix, hPA,
      ← mul_assoc]
    exact hAV
  exact ⟨W, hWadd, hWmod, hWfin, ρ, hirrρ, hker, P, hP1, hPel, hquad, hineq⟩

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
