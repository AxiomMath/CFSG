module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinCoords
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem rootChar_coordTuple
    {τ : Tag} {L : Type} [Field L] {Δ : Finset (Fin τ.rank → ℤ)}
    (hΔ : ∀ β ∈ Δ, IsRoot τ β) (c : (Fin τ.rank → ℤ) → Lˣ) (γ : Fin τ.rank → ℤ) :
    rootChar (coordTuple Δ c) γ = ∏ β ∈ Δ, c β ^ corootPair β γ := by
  unfold rootChar
  rw [coordTuple_eq_prod]
  simp only [Finset.prod_apply]
  rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.prod_zpow_prod_comm
    Δ Finset.univ c (fun β i => corootPair β (Pi.single i 1)) γ]
  refine Finset.prod_congr rfl fun β hβ => ?_
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum (hΔ β hβ) γ]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem rootChar_eq_of_conj_pinnedX
    {τ : Tag} {L : Type} [Field L] {g : ModGL τ L}
    {π : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hπΦ : ∀ α, IsRoot τ α → IsRoot τ (π α))
    (hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ x : L,
      g * pinnedX τ L α x * g⁻¹ = pinnedX τ L (π α) (ε * x))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {a a' : Fin τ.rank → Lˣ}
    (ha' : g * rootDiagUnit τ a * g⁻¹ = rootDiagUnit τ a') :
    rootChar a' (π α) = rootChar a α := by
  obtain ⟨ε, hε⟩ := hgX α hα
  have hroot : ∀ x : L,
      pinnedX τ L (π α) (((rootChar a' (π α) : L) * ε) * x) =
        pinnedX τ L (π α) ((ε : L) * ((rootChar a α : L) * x)) := by
    intro x
    have h1 : rootDiagUnit τ a' * pinnedX τ L (π α) ((ε : L) * x) *
        (rootDiagUnit τ a')⁻¹ =
        pinnedX τ L (π α) (((rootChar a' (π α) : L) * ε) * x) := by
      rw [rootDiagUnit_conj_pinnedX a' (hπΦ α hα) ((ε : L) * x)]
      congr 1
      ring
    have h2 : rootDiagUnit τ a' * pinnedX τ L (π α) ((ε : L) * x) *
        (rootDiagUnit τ a')⁻¹ =
        pinnedX τ L (π α) ((ε : L) * ((rootChar a α : L) * x)) := by
      rw [← ha', ← hε x]
      rw [show g * rootDiagUnit τ a * g⁻¹ * (g * pinnedX τ L α x * g⁻¹) *
            (g * rootDiagUnit τ a * g⁻¹)⁻¹ =
            g * (rootDiagUnit τ a * pinnedX τ L α x * (rootDiagUnit τ a)⁻¹) * g⁻¹ by
          group]
      rw [rootDiagUnit_conj_pinnedX a hα x]
      exact hε _
    exact h1.symm.trans h2
  have harg := pinnedX_injective τ L (π α) (hroot 1)
  simp only [mul_one] at harg
  refine Units.ext ?_
  have hval : (rootChar a' (π α) : L) * (ε : L) = (rootChar a α : L) * (ε : L) :=
    harg.trans (mul_comm _ _)
  exact mul_right_cancel₀ (Units.ne_zero ε) hval

private theorem exists_isRoot_eq_pi_single {τ : Tag}
    {π : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hπΦ : ∀ α, IsRoot τ α → IsRoot τ (π α)) (i : Fin τ.rank) :
    ∃ α, IsRoot τ α ∧ π α = Pi.single i 1 := by
  let f : {v : Fin τ.rank → ℤ // IsRoot τ v} → {v : Fin τ.rank → ℤ // IsRoot τ v} :=
    fun v => ⟨π v.1, hπΦ v.1 v.2⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (π.injective (congrArg Subtype.val h))
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hf ⟨Pi.single i 1, IsRoot.basis i⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

theorem rootDiagUnit_coordTuple_mem_unionTorus
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {Δ : Finset (Fin τ.rank → ℤ)} (hΔ : ∀ β ∈ Δ, β ∈ unionRoots χ J)
    (c : (Fin τ.rank → ℤ) → Lˣ) :
    rootDiagUnit τ (coordTuple Δ c) ∈ unionTorus L χ J := by
  classical
  revert hΔ
  refine Finset.induction_on Δ ?h0 ?h1
  · intro hΔ
    have h1 : coordTuple (∅ : Finset (Fin τ.rank → ℤ)) c = 1 := by
      funext i
      simp [coordTuple]
    rw [h1, rootDiagUnit_one]
    exact Subgroup.one_mem _
  · intro a s ha ih hΔ
    have hcoord : coordTuple (insert a s) c =
        (fun i => c a ^ corootPair a (Pi.single i 1)) * coordTuple s c := by
      funext i
      simp only [coordTuple_eq_prod, Pi.mul_apply, Finset.prod_apply, Finset.prod_insert ha]
    have hfactor : rootDiagUnit τ (fun i => c a ^ corootPair a (Pi.single i 1)) ∈
        unionTorus L χ J := by
      have haroot : IsRoot τ a := isRoot_of_mem_unionRoots (hΔ a (Finset.mem_insert_self a s))
      rw [unionTorus, Subgroup.mem_inf]
      constructor
      · have hsub : ({a, -a} : Set (Fin τ.rank → ℤ)) ⊆ unionRoots χ J := by
          intro x hx
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with hx | hx
          · rw [hx]
            exact hΔ a (Finset.mem_insert_self a s)
          · rw [hx]
            exact neg_mem_unionRoots (hΔ a (Finset.mem_insert_self a s))
        have hmem : rootSL2 τ L a (HSL (c a)) ∈ rootSpan τ L (unionRoots χ J) :=
          rootSpan_mono hsub (rootSL2_mem_rootSpan_pair haroot (HSL (c a)))
        rwa [rootSL2_HSL_eq haroot (c a)] at hmem
      · rw [← rootSL2_HSL_eq haroot (c a)]
        exact rootSL2_HSL_mem_torusGroup haroot (c a)
    rw [hcoord, rootDiagUnit_mul]
    exact mul_mem hfactor (ih fun β hβ => hΔ β (Finset.mem_insert_of_mem hβ))

theorem conj_rootDiagUnit_coordTuple
    {τ : Tag} {L : Type} [Field L] {g : ModGL τ L}
    {π : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} (hπ : ∀ x y, iform (π x) (π y) = iform x y)
    (hπΦ : ∀ α, IsRoot τ α → IsRoot τ (π α))
    (hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ x : L,
      g * pinnedX τ L α x * g⁻¹ = pinnedX τ L (π α) (ε * x))
    (hgT : ∀ t, ∃ t', g * rootDiagUnit τ t * g⁻¹ = rootDiagUnit τ t')
    {Δ : Finset (Fin τ.rank → ℤ)} (hΔ : ∀ β ∈ Δ, IsRoot τ β) (c : (Fin τ.rank → ℤ) → Lˣ) :
    g * rootDiagUnit τ (coordTuple Δ c) * g⁻¹ =
      rootDiagUnit τ (coordTuple (Δ.image π) fun γ => c (π.symm γ)) := by
  classical
  obtain ⟨a', ha'⟩ := hgT (coordTuple Δ c)
  have hchar : ∀ α, IsRoot τ α → rootChar a' (π α) = rootChar (coordTuple Δ c) α :=
    fun α hα => rootChar_eq_of_conj_pinnedX hπΦ hgX hα ha'
  have hΔπ : ∀ γ ∈ Δ.image π, IsRoot τ γ := by
    intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
    exact hπΦ β (hΔ β hβ)
  have hb : a' = coordTuple (Δ.image π) fun γ => c (π.symm γ) := by
    funext i
    obtain ⟨α, hα, hπα⟩ := exists_isRoot_eq_pi_single hπΦ i
    have hL : a' i = rootChar a' (π α) := by
      rw [hπα]
      exact (by simpa using (rootChar_nsmul_single a' i 1).symm)
    have hR : (coordTuple (Δ.image π) fun γ => c (π.symm γ)) i =
        rootChar (coordTuple (Δ.image π) fun γ => c (π.symm γ)) (π α) := by
      rw [hπα]
      exact (by simpa using (rootChar_nsmul_single _ i 1).symm)
    have hprod : (∏ β ∈ Δ, c β ^ corootPair β α) =
        ∏ γ ∈ Δ.image π, (c (π.symm γ)) ^ corootPair γ (π α) := by
      rw [Finset.prod_image
        (f := fun γ => (c (π.symm γ)) ^ corootPair γ (π α))
        (g := π) (fun x _ y _ hxy => π.injective hxy)]
      refine Finset.prod_congr rfl fun β hβ => ?_
      rw [AddEquiv.symm_apply_apply]
      congr 1
      rw [corootPair, corootPair, hπ β α, hπ β β]
    rw [hL, hR, hchar α hα, rootChar_coordTuple hΔ c α, hprod]
    exact (rootChar_coordTuple hΔπ (fun γ => c (π.symm γ)) (π α)).symm
  rw [ha', hb]

end CFSG.HardMathSupport.C14Idx
