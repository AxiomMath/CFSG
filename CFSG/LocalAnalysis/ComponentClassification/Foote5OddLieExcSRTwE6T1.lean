module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Comp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Row
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRTwE6

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.Burgoyne.E2 CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem outerCoreAt_of_component_induced {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    {α : MulAut S} {X : Subgroup S} (hX : GorensteinWalter.IsComponentOf X (oddFixed α))
    {G : Type*} [Group G] {Φ : S →* G} (hΦ : Function.Injective Φ) (Z : Set G)
    (hind : ∀ r : MulAut S, Odd (orderOf r) → r * α = α * r → (∀ y ∈ X, r y = y) →
      ∃ z ∈ Z, ∀ s, Φ (r s) = z * Φ s * z⁻¹)
    (hab : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) : OuterCoreAt α := by
  intro R hRodd hRi hRc r₁ h₁ r₂ h₂
  have hfix : ∀ r ∈ R, ∀ y ∈ X, r y = y := fun r hr _ hy =>
    fix_of_isComponentOf hRi hRc hZ hRodd hr hX hy
  obtain ⟨z₁, hz₁, hr₁⟩ := hind r₁ (odd_orderOf_of_mem hRodd h₁) (hRi r₁ h₁) (hfix r₁ h₁)
  obtain ⟨z₂, hz₂, hr₂⟩ := hind r₂ (odd_orderOf_of_mem hRodd h₂) (hRi r₂ h₂) (hfix r₂ h₂)
  refine MulEquiv.ext fun s => hΦ ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, hr₁, hr₂, hr₂, hr₁]
  calc z₁ * (z₂ * Φ s * z₂⁻¹) * z₁⁻¹ = (z₁ * z₂) * Φ s * (z₁ * z₂)⁻¹ := by group
    _ = (z₂ * z₁) * Φ s * (z₂ * z₁)⁻¹ := by rw [hab z₁ hz₁ z₂ hz₂]
    _ = z₂ * (z₁ * Φ s * z₁⁻¹) * z₂⁻¹ := by group

theorem outerCoreAt_t1 {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {L : Type}
    [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀G : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hg₀F : frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) g₀ = g₀)
    (hg₀t : g₀ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₀⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) :
    OuterCoreAt (MulAut.conj t) := by
  classical
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
    (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set d := rootDiagUnit TwistTag.E6.tag
    (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) with hd
  have hg₀R : g₀ ∈ R := mem_fixedPointsIn.2 ⟨hg₀G, hg₀F⟩
  set Φ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g₀).toMonoidHom.comp ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) with hΦ
  have hΦapp : ∀ s, Φ s =
      g₀ * baseChangeGL (algebraMap K L) (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ := fun s => rfl
  have hΦinj : Function.Injective Φ :=
    (MulAut.conj g₀).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)
  have hΦt : Φ t = d := hg₀t
  obtain ⟨CA, hqCA, hCAH, hCAn, hCAind⟩ := exists_t1_layer hp2 hf hK σ hσ hg₀R
  have hmap : (fixedSubgroup (MulAut.conj t)).map Φ = ⁅R, R⁆ ⊓ Subgroup.centralizer {d} := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : t * s * t⁻¹ = s := hs
      have hst : t * s = s * t := by
        calc t * s = t * s * t⁻¹ * t := by group
          _ = s * t := by rw [hs']
      refine Subgroup.mem_inf.2 ⟨(t1_preimage hp2 hf hK σ hσ hg₀R).2 ⟨s, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hΦt, ← map_mul, ← map_mul, hst]
    · intro hv
      obtain ⟨hvH, hvd⟩ := Subgroup.mem_inf.1 hv
      obtain ⟨s, rfl⟩ := (t1_preimage hp2 hf hK σ hσ hg₀R).1 hvH
      refine ⟨s, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hΦapp s, ← hΦt, ← map_mul, ← map_mul] at hvd
      have hst := hΦinj hvd
      change t * s * t⁻¹ = s
      rw [← hst]
      group
  have hNle : ⁅R, R⁆ ⊓ Subgroup.centralizer {d} ≤ R ⊓ Subgroup.centralizer {d} :=
    inf_le_inf_right _ (Subgroup.commutator_le_of_le le_rfl le_rfl)
  have hCAnorm : (CA.subgroupOf (⁅R, R⁆ ⊓ Subgroup.centralizer {d})).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCAH).2 fun y hy => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hCAn y (hNle hy) v
    · intro hv
      have h := hCAn y⁻¹ (inv_mem (hNle hy)) _ hv
      rwa [show y⁻¹ * (y * v * y⁻¹) * y⁻¹⁻¹ = v by group] at h
  obtain ⟨hX, -⟩ := HarrisLit.L33.SR.E1.isComponentOf_oddFixed_of_map (MulAut.conj t) Φ hΦinj
    hmap hCAH hCAnorm.isSubnormal (HarrisLit.L33.SR.E1.gw_isQuasisimple_of_isQuasisimple hqCA)
  refine outerCoreAt_of_component_induced (exceptional_fixed_center_trivial TwistTag.E6 K σ) hX
    hΦinj (Set.range (rootDiagUnit TwistTag.E6.tag)) ?_ ?_
  · intro r hr _ hfix
    obtain ⟨c, -, -, -, -, -, -, hc⟩ := hCAind r hr fun s hs => hfix s hs
    exact ⟨rootDiagUnit TwistTag.E6.tag c, ⟨c, rfl⟩, fun s => hc s⟩
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRTwE6
