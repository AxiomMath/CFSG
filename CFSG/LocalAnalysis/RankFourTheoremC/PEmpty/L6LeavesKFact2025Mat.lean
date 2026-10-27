module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Abs
public import CFSG.Open.StatedDefs
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SeitzGeneration.Dispatch
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open Matrix Subgroup CFSG.Open

section ToEnd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

noncomputable abbrev toEnd : GL ι K ≃* (Module.End K (ι → K))ˣ :=
  Matrix.GeneralLinearGroup.toLin

theorem toEnd_neg_one : toEnd (-1 : GL ι K) = -1 := by
  apply Units.ext
  show Matrix.toLin' ((-1 : GL ι K) : Matrix ι ι K) = _
  rw [Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, map_neg, Matrix.toLin'_one]
  rfl

theorem toEnd_symm_val (g : (Module.End K (ι → K))ˣ) :
    ((toEnd.symm g : GL ι K) : Matrix ι ι K) =
      Matrix.toLinAlgEquiv'.symm (g : Module.End K (ι → K)) := rfl

end ToEnd

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem kxSection_of_stated_proj (h2 : (2 : K) ≠ 0) (hι : Fintype.card ι = 4)
    (H₀ : Subgroup (GL ι K))
    (hZ : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ H₀ → c ^ 4 = 1)
    (hW : ∀ x u w : GL ι K, x ∈ H₀ → u ∈ H₀ → x * x = -1 →
      (w : Matrix ι ι K) = (2⁻¹ : K) • ((1 + (x : Matrix ι ι K)) *
        (1 + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K))) → w ∈ H₀)
    {A : Type} [Group A] {L S : Subgroup A} (e : ↥L ≃* StatedProj H₀) {z : A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hzp : orderOf z = p) (hzL : z ∈ L) (hSL : S ≤ L)
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hzS : z ∈ normalizer (S : Set A))
    (hcomm : ⁅S, zpowers z⁆ = S) : KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  obtain ⟨F, hF⟩ : ∃ F : H₀ →* A, ∀ y : H₀,
      F y = (e.symm (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H₀) y) : A) :=
    ⟨L.subtype.comp (e.symm.toMonoidHom.comp
      (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H₀))), fun _ => rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : H₀ →* (Module.End K (ι → K))ˣ, ∀ y : H₀, ρ y = toEnd (y : GL ι K) :=
    ⟨toEnd.toMonoidHom.comp H₀.subtype, fun _ => rfl⟩
  have hρinj : Function.Injective ρ := by
    intro a b hab
    rw [hρ, hρ] at hab
    exact Subtype.ext (toEnd.injective hab)
  have hFker : ∀ y : H₀, F y = 1 → y ∈ (StatedScalars ι K).subgroupOf H₀ := by
    intro y hy
    rw [hF] at hy
    have h1 : e.symm (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H₀) y) = 1 :=
      Subtype.ext hy
    have h2' := e.symm.injective (h1.trans (map_one e.symm).symm)
    exact (QuotientGroup.eq_one_iff y).mp h2'
  have hFrange : F.range = L := by
    ext l
    constructor
    · rintro ⟨y, rfl⟩
      rw [hF]
      exact (e.symm _).2
    · intro hl
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e ⟨l, hl⟩)
      refine ⟨y, ?_⟩
      rw [hF]
      show ((e.symm (QuotientGroup.mk y)) : A) = l
      rw [hy]
      simp
  have hy4 : ∀ y : H₀, y ∈ (StatedScalars ι K).subgroupOf H₀ → y ^ 4 = 1 := by
    intro y hy
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hy : (y : GL ι K) ∈ StatedScalars ι K)
    have hcH : Matrix.GeneralLinearGroup.scalar ι c ∈ H₀ := by rw [hc]; exact y.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hZ c hcH, map_one]
    rfl
  have hker2 : IsPGroup 2 F.ker := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    have := hy4 g.1 (hFker g.1 (MonoidHom.mem_ker.mp g.2))
    simpa using this
  have hkerc : ∀ y ∈ F.ker, ∀ g : (Module.End K (ι → K))ˣ, ρ y * g = g * ρ y := by
    intro y hy g
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp (hFker y (MonoidHom.mem_ker.mp hy)) :
      (y : GL ι K) ∈ StatedScalars ι K)
    obtain ⟨g', rfl⟩ := toEnd.surjective g
    rw [hρ, ← hc, ← map_mul, ← map_mul, Matrix.GeneralLinearGroup.scalar_commute]
  have hdim : Module.finrank K (ι → K) ≤ 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  have hW' : ∀ (x₀ u₀ : H₀) (x' : (Module.End K (ι → K))ˣ) (hx : ρ x₀ * ρ x₀ = -1)
      (hx' : x' * x' = -1), x' = ρ u₀ * ρ x₀ * (ρ u₀)⁻¹ →
      half h2 * gam h2 (ρ x₀) hx * gam h2 x' hx' ∈ ρ.range := by
    intro x₀ u₀ x' hx hx' hxu
    have hxu' : x' = toEnd ((u₀ : GL ι K) * (x₀ : GL ι K) * (u₀ : GL ι K)⁻¹) := by
      rw [hxu, hρ, hρ, map_mul, map_mul, map_inv]
    have hXX : (x₀ : GL ι K) * x₀ = -1 := by
      apply toEnd.injective
      rw [map_mul, toEnd_neg_one]
      rw [hρ] at hx
      exact hx
    subst hxu'
    obtain ⟨w, hw⟩ : ∃ w : GL ι K, w = toEnd.symm (half h2 * gam h2 (ρ x₀) hx *
        gam h2 (toEnd ((u₀ : GL ι K) * (x₀ : GL ι K) * (u₀ : GL ι K)⁻¹)) hx') := ⟨_, rfl⟩
    have hwv : (w : Matrix ι ι K) = (2⁻¹ : K) • ((1 + ((x₀ : GL ι K) : Matrix ι ι K)) *
        (1 + (((u₀ : GL ι K) * (x₀ : GL ι K) * (u₀ : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K))) := by
      rw [hw, toEnd_symm_val, Units.val_mul, Units.val_mul, gam_val, gam_val]
      have e1 : ((half h2 : (Module.End K (ι → K))ˣ) : Module.End K (ι → K)) =
          Matrix.toLinAlgEquiv' (algebraMap K (Matrix ι ι K) 2⁻¹) :=
        (AlgEquiv.commutes Matrix.toLinAlgEquiv' (2⁻¹ : K)).symm
      have e2 : ((ρ x₀ : (Module.End K (ι → K))ˣ) : Module.End K (ι → K)) =
          Matrix.toLinAlgEquiv' ((x₀ : GL ι K) : Matrix ι ι K) := by
        rw [hρ]
        rfl
      have e3 : ((toEnd ((u₀ : GL ι K) * (x₀ : GL ι K) * (u₀ : GL ι K)⁻¹) :
          (Module.End K (ι → K))ˣ) : Module.End K (ι → K)) =
          Matrix.toLinAlgEquiv' (((u₀ : GL ι K) * (x₀ : GL ι K) * (u₀ : GL ι K)⁻¹ : GL ι K) :
            Matrix ι ι K) := rfl
      rw [e1, e2, e3, ← map_one Matrix.toLinAlgEquiv', ← map_add, ← map_add, ← map_mul,
        ← map_mul, AlgEquiv.symm_apply_apply, Algebra.smul_def, mul_assoc]
    have hwH : w ∈ H₀ := hW x₀ u₀ w x₀.2 u₀.2 hXX hwv
    refine ⟨⟨w, hwH⟩, ?_⟩
    rw [hρ]
    show toEnd w = _
    rw [hw, MulEquiv.apply_symm_apply]
  exact kxSection_of_model h2 hdim ρ hρinj F hker2 hkerc hW' hFrange hp hp5 hzp hzL hSL hS2 hS1
    hzS hcomm

end Transport

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
