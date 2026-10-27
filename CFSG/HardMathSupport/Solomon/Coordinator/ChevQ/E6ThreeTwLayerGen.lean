module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerShift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlaneStmt
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartTwo.KFacts

set_option linter.unusedSectionVars false

theorem exists_suConj_eq_conjSU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (γ : primeFormUnitary h (idGram K 3)) :
    ∃ γ' : unitaryIsom3 h, ∀ x, conjSU h γ x = suConj h γ' x := by
  have hγ : (γ : GL (Fin 3) K) ∈ unitaryIsom3 h := by
    have := mem_primeFormUnitary.mp γ.2
    rw [mem_unitaryIsom3]
    simpa [idGram, Matrix.mul_one] using this
  refine ⟨⟨γ, hγ⟩, fun x => Subtype.ext ?_⟩
  rw [coe_conjSU, coe_suConj]
  rfl

section Layer


theorem twLayer_le_seitzHyperGamma (hM : TwLayerModel) (hNC : TwFixedNonCentral)
    (hT : TwToralPlane) (hI : TwInnerHeisPlane) (hO : TwOuterHeisPlane)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} (hK3 : ringChar K ≠ 3)
    (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n) {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hs : ∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧
      MulAut.conj s ∈ E) (i : Fin 3) :
    L i ≤ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype := by
  obtain ⟨ℓ, f, h, ρ, hℓf, hinj, hrange, hact⟩ := hM K σ q hK3 hσ hKq h3 hq2 h₀ L T n hL
  obtain ⟨s, hsh, hsE⟩ := hs
  have hq3 : 3 ∣ ℓ ^ f + 1 := hℓf ▸ h3
  have hq : ℓ ^ f ≠ 2 := hℓf ▸ hq2
  have hYq : CFSG.IsQuasisimple (unitarySU ℓ f K 3) := by
    have e1 : unitarySU ℓ f K 3 ≃* (ρ 0).range := MonoidHom.ofInjective (hinj 0)
    have e2 : (ρ 0).range ≃* ((ρ 0).range.map (twistedE6RootGroup K σ).subtype) :=
      Subgroup.equivMapOfInjective _ _ (twistedE6RootGroup K σ).subtype_injective
    have e3 : ((ρ 0).range.map (twistedE6RootGroup K σ).subtype) ≃* L 0 :=
      MulEquiv.subgroupCongr (hrange 0)
    exact CFSG.IsQuasisimple.of_mulEquiv (e1.trans (e2.trans e3)) (hL.L_quasisimple 0)
  have M : TwLayerFacts (unitarySU ℓ f K 3) (suConj h).range :=
    twLayerFacts_of_stmts hNC hT hI hO h hq3 hq (shiftQs_exists_noncomm hYq)
      (fun N hN => shiftQs_normal_dichotomy hYq N)
  have hmem : ∀ i x, ((ρ i x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ L i := by
    intro i x
    rw [← hrange i]
    exact ⟨ρ i x, ⟨x, rfl⟩, rfl⟩
  have hcomm : ∀ i j, i ≠ j → ∀ x y, ρ i x * ρ j y = ρ j y * ρ i x := fun i j hij x y =>
    Subtype.ext (hL.L_commute i j hij _ (hmem i x) _ (hmem j y))
  have hcen : ∀ i, ∀ y ∈ L i, y * h₀ = h₀ * y := by
    intro i y hy
    have hc : (⟨h₀, hL.h₀_mem_L i⟩ : ↥(L i)) ∈ Subgroup.center ↥(L i) := by
      rw [hL.L_center_eq i]
      exact Subgroup.mem_zpowers h₀
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
  have hσρ : ∀ i x, MulAut.conj s (ρ i x) = ρ i x := by
    intro i x
    apply Subtype.ext
    show (s : ModGL TwistTag.E6.tag K) * (ρ i x : ModGL TwistTag.E6.tag K) *
      (s : ModGL TwistTag.E6.tag K)⁻¹ = ρ i x
    rw [hsh, mul_inv_eq_iff_eq_mul]
    exact (hcen i _ (hmem i x)).symm
  have hσ1 : MulAut.conj s ≠ 1 := by
    intro h1
    have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
      exceptional_fixed_center_trivial TwistTag.E6 K σ
    have hsc : s ∈ Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, Subgroup.mem_bot] at hsc
    exact hL.h₀_ne (by rw [← hsh, hsc]; rfl)
  have hdec : ∀ ε ∈ E, ∃ k : Fin 3,
      (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + k)).range) ∧
        (k = 0 → ∀ i, ∃ a ∈ (suConj h).range, ∀ x, ε (ρ i x) = ρ i (a x)) := by
    intro ε hε
    have hε3 : ε ^ 3 = 1 := hE.2 ε hε
    have hεc : ε * MulAut.conj s = MulAut.conj s * ε :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨ε, hε⟩ : E) ⟨MulAut.conj s, hsE⟩)
    obtain ⟨k, hk⟩ := twLayer_exists_shift_frames hL hsh hε3 hεc ρ hrange
    refine ⟨k, hk, fun hk0 i => ?_⟩
    subst hk0
    have hfix : ∀ i, (ρ i).range.map ε.toMonoidHom = (ρ i).range := fun i => by
      rw [hk i, add_zero]
    obtain ⟨γ, hγ⟩ := hact s hsh ε (hED hε) hεc hfix i
    obtain ⟨γ', hγ'⟩ := exists_suConj_eq_conjSU h γ
    exact ⟨suConj h γ', ⟨γ', rfl⟩, fun x => by rw [hγ x, hγ']⟩
  have hcard' : Nat.card E = 27 := by rw [hcard]; norm_num
  rw [← hrange i]
  exact Subgroup.map_mono (layerStep_abs M hE hcard' hinj hcomm hsE hσ1 hσρ hdec i)

theorem twE6ThreeLayerGen_of_model (hM : TwLayerModel) (hNC : TwFixedNonCentral)
    (hT : TwToralPlane) (hI : TwInnerHeisPlane) (hO : TwOuterHeisPlane) : TwE6ThreeLayerGen := by
  intro K _ _ σ q hK3 hσ hKq h3 hq2 h₀ L T n hL E hE hcard hED _ _ _ hs i
  exact twLayer_le_seitzHyperGamma hM hNC hT hI hO hK3 hσ hKq h3 hq2 hL hE hcard hED hs i

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
