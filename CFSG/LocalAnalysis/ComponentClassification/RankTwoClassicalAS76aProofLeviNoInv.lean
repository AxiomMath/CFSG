module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviLayer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.RankTwoStandard

section Induced

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] {θ : ↥A →* P}

theorem eq_of_inv_mul_mem_center {H M : Type*} [Group H] [Group M] [Group.IsPerfect H]
    (f g : H →* M) (h : ∀ x, (f x)⁻¹ * g x ∈ center M) : f = g := by
  let d : H →* center M :=
    { toFun := fun x => ⟨(f x)⁻¹ * g x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change (f (x * y))⁻¹ * g (x * y) = (f x)⁻¹ * g x * ((f y)⁻¹ * g y)
        have hc := mem_center_iff.mp (h x) ((f y)⁻¹)
        calc (f (x * y))⁻¹ * g (x * y) = (f y)⁻¹ * ((f x)⁻¹ * g x) * g y := by
              rw [map_mul, map_mul]
              group
          _ = (f x)⁻¹ * g x * ((f y)⁻¹ * g y) := by
              rw [hc]
              group }
  ext x
  have hx : x ∈ d.ker :=
    Abelianization.commutator_subset_ker d (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  have h1 : (f x)⁻¹ * g x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact inv_mul_eq_one.mp h1

variable (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
include hker hθ

theorem exists_inducedAut (σ : MulAut ↥A) : ∃ α : MulAut P, ∀ a, α (θ a) = θ (σ a) := by
  set e₀ := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  have he : ∀ a, e₀ (QuotientGroup.mk a) = θ a := fun _ => rfl
  refine ⟨(e₀.symm.trans (QuotientGroup.congr θ.ker θ.ker σ ?_)).trans e₀, fun a => ?_⟩
  · rw [hker]
    exact map_center_eq σ
  · have h1 : e₀.symm (θ a) = QuotientGroup.mk a := by
      rw [MulEquiv.symm_apply_eq, he]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk, he]

omit hθ in
theorem eq_one_of_theta_eq (hA : commutator ↥A = ⊤) (σ : MulAut ↥A)
    (h : ∀ a, θ (σ a) = θ a) : σ = 1 := by
  have : Group.IsPerfect ↥A := ⟨hA⟩
  have h1 := eq_of_inv_mul_mem_center (MonoidHom.id ↥A) σ.toMonoidHom fun a => by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    change (θ a)⁻¹ * θ (σ a) = 1
    rw [h, inv_mul_cancel]
  ext a
  exact (congrArg (fun f : ↥A →* ↥A => (f a : G)) h1).symm

omit hker in
theorem inducedAut_sq {σ : MulAut ↥A} (hσ : σ * σ = 1) {α : MulAut P}
    (hα : ∀ a, α (θ a) = θ (σ a)) : α * α = 1 := by
  ext p
  obtain ⟨a, rfl⟩ := hθ p
  rw [MulAut.mul_apply, hα, hα, ← MulAut.mul_apply, hσ]
  rfl

omit hker in
theorem inducedAut_fix_of_levLift {S : Subgroup P} (hperf : ⁅S, S⁆ = S) {X : Subgroup G}
    (hX : levLift θ S ≤ X) {σ : MulAut ↥A} (hσ : ∀ x : ↥A, (x : G) ∈ X → σ x = x)
    {α : MulAut P} (hα : ∀ a, α (θ a) = θ (σ a)) : ∀ s ∈ S, α s = s := by
  intro s hs
  obtain ⟨x, hx, rfl⟩ := exists_mem_levLift hθ hperf hs
  rw [hα, hσ _ (hX hx)]

omit hker in
theorem inducedAut_fix_of_liftSub {S : Subgroup P} {X : Subgroup G} (hX : liftSub θ S ≤ X)
    {σ : MulAut ↥A} (hσ : ∀ x : ↥A, (x : G) ∈ X → σ x = x) {α : MulAut P}
    (hα : ∀ a, α (θ a) = θ (σ a)) : ∀ s ∈ S, α s = s := by
  intro s hs
  obtain ⟨a, rfl⟩ := hθ s
  rw [hα, hσ _ (hX (mem_liftSub.mpr ⟨a.2, hs⟩))]

end Induced

section NoInv

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {A : Subgroup G}

theorem noInv_of_three_le {k : ℕ} {θ : ↥A →* projectiveSL (2 + k) K} (hA : commutator ↥A = ⊤)
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4)
    (hk : 3 ≤ k) : NoInvolutoryCentralizing A (leviW θ ⊔ leviL θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have h1 := eq_one_of_fixes_of_three_le hk α (inducedAut_sq hθ hσ hα)
    (inducedAut_fix_of_levLift hθ (commutator_barW h4) le_sup_left hfix hα)
    (inducedAut_fix_of_levLift hθ (commutator_barL (by omega) h4) le_sup_right hfix hα)
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

theorem noInv_two {θ : ↥A →* projectiveSL (2 + 2) K} (hA : commutator ↥A = ⊤)
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4)
    {c : Kˣ} (hc : c ≠ 1) :
    NoInvolutoryCentralizing A (liftSub θ (barT K) ⊔ leviW θ ⊔ leviL θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hT := inducedAut_fix_of_liftSub hθ (le_sup_left.trans le_sup_left) hfix hα
    _ ⟨c, rfl⟩
  have h1 := eq_one_of_fixes_two α (inducedAut_sq hθ hσ hα)
    (inducedAut_fix_of_levLift hθ (commutator_barW h4) (le_sup_right.trans le_sup_left)
      hfix hα)
    (inducedAut_fix_of_levLift hθ (commutator_barL le_rfl h4) le_sup_right hfix hα) hc hT
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

theorem outerFree_two {θ : ↥A →* projectiveSL (2 + 2) K} (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4) {c : Kˣ} (hc : c ≠ 1)
    (σ : MulAut ↥A) (hfix : ∀ y : ↥A, (y : G) ∈ liftSub θ (barT K) ⊔ leviW θ → σ y = y) :
    ∃ l ∈ leviL θ, ∀ z : ↥A, (z : G) ∈ leviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹ := by
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hT := inducedAut_fix_of_liftSub hθ le_sup_left hfix hα _ ⟨c, rfl⟩
  obtain ⟨lb, hlb, hinner⟩ := exists_inner_of_fixes_two α
    (inducedAut_fix_of_levLift hθ (commutator_barW h4) le_sup_right hfix hα) hc hT
  obtain ⟨l, hl, hlθ⟩ := exists_mem_levLift hθ (commutator_barL le_rfl h4) hlb
  refine ⟨l, hl, ?_⟩
  have hlA : l ∈ A := levLift_le hl
  have hperf : Group.IsPerfect ↥(leviL θ) :=
    (Subgroup.isPerfect_iff).mpr (commutator_levLift hker hθ (commutator_barL le_rfl h4))
  let f : ↥(leviL θ) →* ↥A := (MulAut.conj (⟨l, hlA⟩ : ↥A)).toMonoidHom.comp
    (Subgroup.inclusion (levLift_le (θ := θ) (S := barL K 2)))
  let g : ↥(leviL θ) →* ↥A := σ.toMonoidHom.comp
    (Subgroup.inclusion (levLift_le (θ := θ) (S := barL K 2)))
  have hfg := eq_of_inv_mul_mem_center f g fun z => by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    change (θ (⟨l, hlA⟩ * ⟨z, levLift_le z.2⟩ * (⟨l, hlA⟩ : ↥A)⁻¹))⁻¹ *
      θ (σ ⟨z, levLift_le z.2⟩) = 1
    rw [← hα, hinner _ (theta_mem_of_mem_levLift z.2), map_mul, map_mul, map_inv, hlθ,
      inv_mul_cancel]
  intro z hz
  have := congrArg (fun F : ↥(leviL θ) →* ↥A => ((F ⟨z, hz⟩ : ↥A) : G)) hfg
  exact this.symm

end NoInv

end CFSG.ComponentClassification.RankTwoClassical
