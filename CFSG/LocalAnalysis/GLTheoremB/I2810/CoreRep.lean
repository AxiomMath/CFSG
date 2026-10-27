module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV
import CFSG.HardMathSupport.Solomon.Coordinator.I28_5
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement IsMulCommutative

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

section Rep
variable {X : Type} [Group X] [Finite X]

theorem secRep_exists_proof (K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X)
    (hel : IsElemAbelian 2 U₁) (hle : U₂ ≤ U₁)
    (hK₁ : ∀ k ∈ K, ∀ x ∈ U₁, k * x * k⁻¹ ∈ U₁) (hK₂ : ∀ k ∈ K, ∀ x ∈ U₂, k * x * k⁻¹ ∈ U₂)
    (ha₁ : ∀ x ∈ U₁, a * x * a⁻¹ ∈ U₁) (ha₂ : ∀ x ∈ U₂, a * x * a⁻¹ ∈ U₂) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module (ZMod 2) P) (_ : Finite P)
      (ρ : ↥(K ⊔ Subgroup.zpowers a) →* LinearMap.GeneralLinearGroup (ZMod 2) P)
      (φ : ↥U₁ →* Multiplicative P), SecRepData (K ⊔ Subgroup.zpowers a) U₁ U₂ ρ φ := by
  haveI := hel.1
  set M := K ⊔ Subgroup.zpowers a with hM
  have hnorm : ∀ V : Subgroup X, (∀ k ∈ K, ∀ x ∈ V, k * x * k⁻¹ ∈ V) →
      (∀ x ∈ V, a * x * a⁻¹ ∈ V) → M ≤ Subgroup.normalizer (V : Set X) := by
    intro V hK ha
    refine sup_le (fun k hk => Subgroup.mem_normalizer_fintype fun n hn => hK k hk n hn) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype fun n hn => ha n hn
  have hn1 := hnorm U₁ hK₁ ha₁
  have hn2 := hnorm U₂ hK₂ ha₂
  have hc1 : ∀ g : ↥M, ∀ v ∈ U₁, M.subtype g * v * (M.subtype g)⁻¹ ∈ U₁ := fun g v hv =>
    (Subgroup.mem_normalizer_iff.1 (hn1 g.2) v).1 hv
  have hc2 : ∀ g : ↥M, ∀ v ∈ U₂, M.subtype g * v * (M.subtype g)⁻¹ ∈ U₂ := fun g v hv =>
    (Subgroup.mem_normalizer_iff.1 (hn2 g.2) v).1 hv
  let c : ↥M →* MulAut ↥U₁ := CFSG.SignalizerFunctorTheorem.NonLocal.conjHom M.subtype U₁ hc1
  have hc_apply : ∀ (g : ↥M) (v : ↥U₁), ((c g v : ↥U₁) : X) = (g : X) * v * (g : X)⁻¹ := fun g v =>
    CFSG.SignalizerFunctorTheorem.NonLocal.conjHom_apply M.subtype U₁ hc1 g v
  let N : Subgroup ↥U₁ := U₂.subgroupOf U₁
  have hN : ∀ v : ↥U₁, v ∈ N ↔ (v : X) ∈ U₂ := fun v => Subgroup.mem_subgroupOf
  have hcN : ∀ g : ↥M, N.map (c g).toMonoidHom = N := by
    intro g
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hy' := (hN y).1 hy
      refine (hN _).2 ?_
      show ((c g y : ↥U₁) : X) ∈ U₂
      rw [hc_apply]
      exact hc2 g _ hy'
    · intro x hx
      refine ⟨c g⁻¹ x, ?_, ?_⟩
      · have hx' := (hN x).1 hx
        refine (hN _).2 ?_
        show ((c g⁻¹ x : ↥U₁) : X) ∈ U₂
        rw [hc_apply]
        have := hc2 g⁻¹ _ hx'
        simpa using this
      · show c g (c g⁻¹ x) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  let Q := ↥U₁ ⧸ N
  haveI : N.Normal := Subgroup.normal_of_comm N
  let qc : ↥M →* MulAut Q :=
    { toFun := fun g => QuotientGroup.congr N N (c g) (hcN g)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x => simp
      map_mul' := fun g h => by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x =>
          show (QuotientGroup.mk (c (g * h) x) : Q) = QuotientGroup.mk (c g (c h x))
          rw [map_mul]; rfl }
  have hqc : ∀ (g : ↥M) (v : ↥U₁), qc g (QuotientGroup.mk v) = QuotientGroup.mk (c g v) :=
    fun g v => rfl
  let P : Type := Additive Q
  have h2 : ∀ x : P, (2 : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hv, pow_two, ← QuotientGroup.mk_mul]
    have : (v * v : ↥U₁) = 1 := Subtype.ext (by simpa [pow_two] using hel.2 v v.2)
    rw [this]; rfl
  letI : Module (ZMod 2) P := AddCommGroup.zmodModule h2
  let ρ : ↥M →* LinearMap.GeneralLinearGroup (ZMod 2) P :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i285_Φ (V := Q)).toMonoidHom.comp qc
  let φ : ↥U₁ →* Multiplicative P :=
    { toFun := fun v => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk v : Q))
      map_one' := rfl
      map_mul' := fun x y => rfl }
  refine ⟨P, inferInstance, inferInstance, inferInstanceAs (Finite (Additive Q)), ρ, φ, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd y))
    exact ⟨v, by
      show Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk v : Q)) = y
      rw [hv]; rfl⟩
  · intro u
    show Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u : Q)) = 1 ↔ _
    rw [← hN u, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => h, fun h => h⟩
  · intro g u u' hu'
    have hcu : c g u = u' := Subtype.ext (by rw [hc_apply, hu'])
    show Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u' : Q)) = _
    rw [← hcu]
    rfl

end Rep

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
