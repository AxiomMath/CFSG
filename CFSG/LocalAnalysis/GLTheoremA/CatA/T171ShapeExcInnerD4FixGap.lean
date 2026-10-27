module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Center

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open scoped Pointwise commutatorElement

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem torus_fixed_mem_CQ_of_det_four (i : KernelComponent χ)
    (hdet : (Matrix.of fun β γ : simpleRoots (componentRoots χ i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4) (σ : L ≃+* L) {t : ModGL τ L}
    (ht : t ∈ rootSpan τ L (componentRoots χ i) ⊓ torusGroup τ L) (hfix : frobGL σ t = t) :
    t ∈ CQ σ i := by
  classical
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hΔroot : ∀ β ∈ simpleRoots (componentRoots χ i), IsRoot τ β :=
    fun _ hβ => simpleRoots_isRoot hβ
  have hΔsub : ∀ β ∈ simpleRoots (componentRoots χ i), β ∈ componentRoots χ i :=
    fun _ hβ => simpleRoots_subset hβ
  have hcenter := center_eq_bot_of_cartan_det_eq_four (L := L) i hdet
  obtain ⟨c, htc⟩ := exists_rootDiagUnit_coordTuple_of_mem_rootSpan_torus
    (S := componentRoots χ i) (Δ := simpleRoots (componentRoots χ i)) hΔroot hΔsub hdet
    (fun γ hγ => exists_coords hΨ hγ)
    (fun γ hγ => hΨ.isRoot γ hγ) (fun γ hγ => hΨ.neg_mem γ hγ) hcenter ht
  have ht' : t ∈ unionTorus L χ ({i} : Set (KernelComponent χ)) := by
    refine Subgroup.mem_inf.2 ⟨?_, ht.2⟩
    unfold unionRootSpan
    rw [unionRoots_singleton]
    exact ht.1
  have hchar := torus_fixed_char (σ := σ) (i := i)
    (l := coordTuple (simpleRoots (componentRoots χ i)) c) htc ht'
    (fun a _ => by rw [mul_one, one_mul]) (by rw [hfix, one_mul])
  have hfixc : ∀ β ∈ simpleRoots (componentRoots χ i),
      σ ((rootChar (coordTuple (simpleRoots (componentRoots χ i)) c) β : Lˣ) : L) =
        ((rootChar (coordTuple (simpleRoots (componentRoots χ i)) c) β : Lˣ) : L) :=
    fun β hβ => hchar β (by rw [unionRoots_singleton]; exact hΔsub β hβ)
  have hcoords : ∀ β ∈ simpleRoots (componentRoots χ i),
      σ ((c β : Lˣ) : L) = ((c β : Lˣ) : L) :=
    coordTuple_fixed_of_rootChar_fixed hΔroot hdet σ c hfixc
  have hCQ : rootDiagUnit τ (coordTuple (simpleRoots (componentRoots χ i)) c) ∈ CQ σ i :=
    rootDiagUnit_coordTuple_mem_CQ hΔsub σ c hcoords
  rw [htc]
  exact hCQ

theorem mem_CQ_of_frobGL_fixed_of_det_four (i : KernelComponent χ)
    (hdet : (Matrix.of fun β γ : simpleRoots (componentRoots χ i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (σ : L ≃+* L) {y : ModGL τ L} (hy : y ∈ rootSpan τ L (componentRoots χ i))
    (hfix : frobGL σ y = y) : y ∈ CQ σ i := by
  have hy' : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    unfold unionRootSpan
    rw [unionRoots_singleton]
    exact hy
  obtain ⟨t, ht, x, hx, hyt, hft⟩ := exists_decomp (σ := σ) (i := i) hy' (one_mem _)
    (by rw [hfix, one_mul])
  have htT : t ∈ torusGroup τ L := (Subgroup.mem_inf.1 ht).2
  have htS : t ∈ rootSpan τ L (componentRoots χ i) := by
    have h := (Subgroup.mem_inf.1 ht).1
    unfold unionRootSpan at h
    rwa [unionRoots_singleton] at h
  have htC : t ∈ CQ σ i :=
    torus_fixed_mem_CQ_of_det_four i hdet σ ⟨htS, htT⟩ (by rw [hft, one_mul])
  rw [hyt]
  exact mul_mem htC hx

theorem mem_CQ_of_frobGL_fixed_rank_four (i : KernelComponent χ)
    (hr : compRank (componentRoots χ i) = 4) (hc : (componentRoots χ i).ncard = 24)
    (σ : L ≃+* L) {y : ModGL τ L} (hy : y ∈ rootSpan τ L (componentRoots χ i))
    (hfix : frobGL σ y = y) : y ∈ CQ σ i :=
  mem_CQ_of_frobGL_fixed_of_det_four i
    (det_cartan_eq_four_of_compRank_four_ncard_24 (isRootComponent_componentRoots i) hr hc) σ hy
    hfix

theorem mem_CQ_of_commute_of_det_four (i : KernelComponent χ)
    (hdet : (Matrix.of fun β γ : simpleRoots (componentRoots χ i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (σ : L ≃+* L) {g : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots χ i))
    (hc : ∀ x ∈ rootSpan τ L (componentRoots χ i),
      x * (frobGL σ g * g⁻¹) = (frobGL σ g * g⁻¹) * x) :
    g ∈ CQ σ i := by
  have hd : frobGL σ g * g⁻¹ ∈ rootSpan τ L (componentRoots χ i) :=
    mul_mem (frobGL_mem_rootSpan σ hg) (inv_mem hg)
  have hdc : (⟨_, hd⟩ : componentRootSpan L χ i) ∈
      Subgroup.center (componentRootSpan L χ i) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2)
  rw [center_eq_bot_of_cartan_det_eq_four (L := L) i hdet, Subgroup.mem_bot] at hdc
  have h1 : frobGL σ g * g⁻¹ = 1 := congrArg Subtype.val hdc
  exact mem_CQ_of_frobGL_fixed_of_det_four i hdet σ hg (mul_inv_eq_one.mp h1)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
