module

public import CFSG.HardMathSupport.C14IdxCorootTorus
public import CFSG.HardMathSupport.C14IdxPLift
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple coordHom)

theorem exists_coordTuple_of_frobTwist_fixed
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {e p : ℕ} {Q : ModGL τ L}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hΔ : Set.BijOn θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    (hp : p.Prime) (hsat : CorootPSaturated p (kernelRoots χ))
    {t : ModGL τ L} (ht : t ∈ unionTorus L χ Set.univ) (hσ : frobTwistGL τ L 2 e Q t = t)
    {n : ℕ} (hn : t ^ p ^ n = 1) :
    ∃ c : (Fin τ.rank → ℤ) → Lˣ,
      t = rootDiagUnit τ (coordTuple (simpleRoots (kernelRoots χ)) c) ∧
        ∀ β ∈ simpleRoots (kernelRoots χ), c (θ β) = c β ^ 2 ^ e := by
  classical
  set Δ : Finset (Fin τ.rank → ℤ) := simpleRoots (kernelRoots χ) with hΔdef
  have hΔunion : (Δ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots χ Set.univ := by
    rw [hΔdef]
    exact (unionSimpleRoots_univ_eq (χ := χ)).symm
  obtain ⟨c₀, hc₀⟩ :=
    exists_coordTuple_of_mem_unionTorus (χ := χ) (J := Set.univ) Δ hΔunion ht
  have hinj : Function.Injective (rootDiagUnit τ : (Fin τ.rank → Lˣ) → ModGL τ L) :=
    rootDiagUnit_injective
  have hx : ∃ m : ℕ, coordTuple Δ c₀ ^ p ^ m = 1 := by
    refine ⟨n, hinj ?_⟩
    change (rootDiagUnitHom τ L) (coordTuple Δ c₀ ^ p ^ n) = (rootDiagUnitHom τ L) 1
    rw [map_pow, map_one]
    change (rootDiagUnit τ (coordTuple Δ c₀)) ^ p ^ n = 1
    rwa [← hc₀]
  obtain ⟨c, hc, hceq⟩ :=
    exists_coordTuple_eq_of_pow_eq_one (k := L) hp
      (linearIndependent_corootVec_unionSimpleRoots (χ := χ) (J := Set.univ) Δ hΔunion) hx
  have ht_eq : t = rootDiagUnit τ (coordTuple Δ c) := by
    rw [hc₀, hceq]
  let c' : (Fin τ.rank → ℤ) → Lˣ := fun γ => c (θ.symm γ) ^ 2 ^ e
  have himageθ : Δ.image θ = Δ := by
    apply Finset.coe_injective
    rw [Finset.coe_image, hΔdef, hΔ.image_eq]
  have hsymm : θ.symm '' (Δ : Set (Fin τ.rank → ℤ)) = Δ := by
    have h := congrArg (fun s : Set (Fin τ.rank → ℤ) => θ.symm '' s) hΔ.image_eq
    have hleft : θ.symm '' (θ '' (simpleRoots (kernelRoots χ) :
        Set (Fin τ.rank → ℤ))) = (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)) := by
      rw [Set.image_image]
      ext x
      simp
    rw [hleft] at h
    rw [hΔdef]
    exact h.symm
  have hθsymm : ∀ β ∈ Δ, θ.symm β ∈ Δ := by
    intro β hβ
    have hmem : θ.symm β ∈ θ.symm '' (Δ : Set (Fin τ.rank → ℤ)) :=
      Set.mem_image_of_mem θ.symm (by simpa using hβ)
    rw [hsymm] at hmem
    exact hmem
  have hΔroot : ∀ β ∈ Δ, IsRoot τ β :=
    fun β hβ => simpleRoots_isRoot (hΔdef ▸ hβ)
  have hFr : entrywiseFrobGL τ L 2 e (rootDiagUnit τ (coordTuple Δ c)) =
      rootDiagUnit τ (coordTuple Δ (c ^ 2 ^ e)) := by
    rw [entrywiseFrobGL_rootDiagUnit_eq_map]
    have hpow : coordTuple Δ (c ^ 2 ^ e) = (coordTuple Δ c) ^ 2 ^ e :=
      map_pow (coordHom Δ) c (2 ^ e)
    rw [hpow]
    congr 1
  have hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ x : L,
      Q * pinnedX τ L α x * Q⁻¹ = pinnedX τ L (θ α) (ε * x) :=
    fun α hα => ⟨1, fun x => by simpa using hQX α hα x⟩
  have hQd : Q * rootDiagUnit τ (coordTuple Δ (c ^ 2 ^ e)) * Q⁻¹ =
      rootDiagUnit τ (coordTuple (Δ.image θ) fun γ => (c ^ 2 ^ e) (θ.symm γ)) :=
    conj_rootDiagUnit_coordTuple (g := Q) (π := θ) hθ hθΦ hgX hQT hΔroot (c ^ 2 ^ e)
  have hσd : frobTwistGL τ L 2 e Q (rootDiagUnit τ (coordTuple Δ c)) =
      rootDiagUnit τ (coordTuple Δ c') := by
    rw [frobTwistGL_apply, hFr, hQd, himageθ]
    rfl
  have hfix : coordTuple Δ c' = coordTuple Δ c := by
    apply hinj
    rw [← hσd, ← ht_eq]
    exact hσ
  have hc' : ∀ β ∈ Δ, ∃ m : ℕ, c' β ^ p ^ m = 1 := by
    intro β hβ
    obtain ⟨m, hm⟩ := hc (θ.symm β) (hθsymm β hβ)
    refine ⟨m, ?_⟩
    change (c (θ.symm β) ^ 2 ^ e) ^ p ^ m = 1
    calc (c (θ.symm β) ^ 2 ^ e) ^ p ^ m
        = (c (θ.symm β) ^ p ^ m) ^ 2 ^ e := pow_right_comm _ _ _
      _ = 1 := by simp [hm]
  have hclosure : AddSubgroup.closure (corootVec '' kernelRoots χ) =
      AddSubgroup.closure (corootVec '' (Δ : Set (Fin τ.rank → ℤ))) := by
    rw [← unionRoots_univ_eq_kernelRoots (χ := χ), hΔunion]
    exact closure_corootVec_unionRoots_eq (χ := χ) (J := Set.univ)
  have hsat' : CorootPSaturated p (Δ : Set (Fin τ.rank → ℤ)) := by
    intro y hy
    rw [← hclosure] at hy ⊢
    exact hsat y hy
  have hfinal :=
    eqOn_of_coordTuple_eq (k := L) hp
      (linearIndependent_corootVec_unionSimpleRoots (χ := χ) (J := Set.univ) Δ hΔunion)
      hsat' hc hc' hfix.symm
  refine ⟨c, ht_eq, ?_⟩
  intro β hβ
  have hβθ : θ β ∈ Δ := by
    rw [← himageθ]
    exact Finset.mem_image_of_mem θ hβ
  have h2 := hfinal (θ β) hβθ
  change c (θ β) = c (θ.symm (θ β)) ^ 2 ^ e at h2
  rwa [AddEquiv.symm_apply_apply] at h2

end CFSG.HardMathSupport.C14Idx
