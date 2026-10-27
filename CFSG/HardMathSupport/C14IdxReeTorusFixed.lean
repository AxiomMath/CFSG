module

public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.HardMathSupport.C14IdxCorootTorus
public import CFSG.HardMathSupport.C14IdxPLift
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


private lemma reeRelationExponent_eq_two_pow_mul (a : ℕ) (j : Fin ReeTag.F4.tag.rank) :
    (ReeTag.F4.relationExponent a j : ℤ) =
      2 ^ a * (ReeTag.F4.relationExponent 0 j : ℤ) := by
  by_cases hj : j ∈ ReeTag.F4.longSet
  · rw [relExp_long a j hj, relExp_long 0 j hj]
    push_cast
    ring
  · rw [relExp_short a j hj, relExp_short 0 j hj]
    push_cast
    rw [pow_succ]

private lemma reeRootExp_eq_two_pow_mul (a : ℕ) (β : Fin ReeTag.F4.tag.rank → ℤ) :
    (rootExp a β : ℤ) = 2 ^ a * (rootExp 0 β : ℤ) := by
  unfold rootExp
  split_ifs with h
  · push_cast
    rw [pow_succ]
  · push_cast
    ring

private lemma reeCorootPair_dualRoot_zero :
    ∀ k : Fin ReeTag.F4.tag.rank, ∀ β ∈ rootFinset ReeTag.F4.tag,
      corootPair β (Pi.single (ReeTag.F4.perm k) 1) *
        (ReeTag.F4.relationExponent 0 (ReeTag.F4.perm k) : ℤ) =
      (rootExp 0 β : ℤ) * corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1) := by
  decide +kernel

private lemma reeCorootPair_dualRoot
    {β : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : IsRoot ReeTag.F4.tag β) (a : ℕ) (k : Fin ReeTag.F4.tag.rank) :
    corootPair β (Pi.single (ReeTag.F4.perm k) 1) *
        (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) =
      (rootExp a β : ℤ) * corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1) := by
  have hz := reeCorootPair_dualRoot_zero k β (mem_rootFinset.mpr hβ)
  rw [reeRelationExponent_eq_two_pow_mul, reeRootExp_eq_two_pow_mul]
  calc corootPair β (Pi.single (ReeTag.F4.perm k) 1) *
        (2 ^ a * (ReeTag.F4.relationExponent 0 (ReeTag.F4.perm k) : ℤ))
      = 2 ^ a * (corootPair β (Pi.single (ReeTag.F4.perm k) 1) *
          (ReeTag.F4.relationExponent 0 (ReeTag.F4.perm k) : ℤ)) := by ring
    _ = 2 ^ a * ((rootExp 0 β : ℤ) *
          corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1)) := by rw [hz]
    _ = (2 ^ a * (rootExp 0 β : ℤ)) *
          corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1) := by ring

private lemma reeTuple_coordTuple
    {L : Type} [Field L] (a : ℕ) (Δ : Finset (Fin ReeTag.F4.tag.rank → ℤ))
    (hΔ : ∀ β ∈ Δ, IsRoot ReeTag.F4.tag β)
    (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ) :
    reeTuple a (coordTuple Δ c) =
      coordTuple (Δ.image ReeTag.F4.dualRoot)
        (fun γ => c (ReeTag.F4.dualRoot γ) ^ rootExp a (ReeTag.F4.dualRoot γ)) := by
  classical
  funext k
  simp only [reeTuple, coordTuple]
  rw [← Finset.prod_pow]
  have hinj : Set.InjOn ReeTag.F4.dualRoot (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
    intro x hx y hy hxy
    calc x = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot x) :=
          (ReeTag.dualRoot_dualRoot (hΔ x hx)).symm
      _ = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot y) := by rw [hxy]
      _ = y := ReeTag.dualRoot_dualRoot (hΔ y hy)
  rw [Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun β hβ => ?_
  rw [ReeTag.dualRoot_dualRoot (hΔ β hβ)]
  have hlhs : (c β ^ corootPair β (Pi.single (ReeTag.F4.perm k) 1)) ^
        ReeTag.F4.relationExponent a (ReeTag.F4.perm k) =
      c β ^ (corootPair β (Pi.single (ReeTag.F4.perm k) 1) *
        (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
  have hrhs : (c β ^ rootExp a β) ^ corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1) =
      c β ^ ((rootExp a β : ℤ) * corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1)) := by
    rw [← zpow_natCast, ← zpow_mul]
  rw [hlhs, hrhs, reeCorootPair_dualRoot (hΔ β hβ) a k]

private lemma dualRoot_inv_smul_mem
    {w : WeylGroup ReeTag.F4.tag}
    {Δ : Finset (Fin ReeTag.F4.tag.rank → ℤ)}
    (hΔroot : ∀ β ∈ Δ, IsRoot ReeTag.F4.tag β)
    (hΔ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)))
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ Δ) :
    ReeTag.F4.dualRoot (w⁻¹ • β) ∈ Δ := by
  have hβroot : IsRoot ReeTag.F4.tag β := hΔroot β hβ
  have hwβroot : IsRoot ReeTag.F4.tag (w⁻¹ • β) := IsRoot.smul hβroot w⁻¹
  set β' : Fin ReeTag.F4.tag.rank → ℤ := ReeTag.F4.dualRoot (w⁻¹ • β) with hβ'def
  have hβ'root : IsRoot ReeTag.F4.tag β' := ReeTag.isRoot_dualRoot hwβroot
  have hθβ' : w • ReeTag.F4.dualRoot β' = β := by
    rw [hβ'def, ReeTag.dualRoot_dualRoot hwβroot, smul_inv_smul]
  have hθinj : Set.InjOn (fun α => w • ReeTag.F4.dualRoot α)
      {α | IsRoot ReeTag.F4.tag α} := by
    intro x hx y hy hxy
    have h1 : ReeTag.F4.dualRoot x = ReeTag.F4.dualRoot y := smul_left_cancel w hxy
    calc x = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot x) :=
          (ReeTag.dualRoot_dualRoot hx).symm
      _ = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot y) := by rw [h1]
      _ = y := ReeTag.dualRoot_dualRoot hy
  have hmem : w • ReeTag.F4.dualRoot β' ∈
      (fun α => w • ReeTag.F4.dualRoot α) '' (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
    rw [hΔ.image_eq, hθβ']
    exact hβ
  obtain ⟨α, hαΔ, hαeq⟩ := hmem
  have heq : α = β' := hθinj (hΔroot α hαΔ) hβ'root hαeq
  rw [← heq]
  exact hαΔ

theorem exists_coordTuple_of_reeTwist_fixed {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ p : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    (hΔ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)))
    (hp : p.Prime) (hsat : CorootPSaturated p (kernelRoots χ))
    {t : ModGL ReeTag.F4.tag L} (ht : t ∈ unionTorus L χ Set.univ)
    (hσ : t ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    {n : ℕ} (hn : t ^ p ^ n = 1) :
    ∃ c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ,
      t = rootDiagUnit ReeTag.F4.tag (coordTuple (simpleRoots (kernelRoots χ)) c) ∧
        ∀ β ∈ simpleRoots (kernelRoots χ),
          c (w • ReeTag.F4.dualRoot β) = c β ^ rootExp a₀ β := by
  classical
  set Δ : Finset (Fin ReeTag.F4.tag.rank → ℤ) := simpleRoots (kernelRoots χ) with hΔdef
  have hΔunion : (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) = unionSimpleRoots χ Set.univ := by
    rw [hΔdef]
    exact (unionSimpleRoots_univ_eq (χ := χ)).symm
  obtain ⟨c₀, hc₀⟩ :=
    exists_coordTuple_of_mem_unionTorus (χ := χ) (J := Set.univ) Δ hΔunion ht
  have hinj : Function.Injective (rootDiagUnit ReeTag.F4.tag :
      (Fin ReeTag.F4.tag.rank → Lˣ) → ModGL ReeTag.F4.tag L) := rootDiagUnit_injective
  have hx : ∃ m : ℕ, coordTuple Δ c₀ ^ p ^ m = 1 := by
    refine ⟨n, hinj ?_⟩
    change (rootDiagUnitHom ReeTag.F4.tag L) (coordTuple Δ c₀ ^ p ^ n) =
      (rootDiagUnitHom ReeTag.F4.tag L) 1
    rw [map_pow, map_one]
    change (rootDiagUnit ReeTag.F4.tag (coordTuple Δ c₀)) ^ p ^ n = 1
    rwa [← hc₀]
  obtain ⟨c, hc, hceq⟩ :=
    exists_coordTuple_eq_of_pow_eq_one (k := L) hp
      (linearIndependent_corootVec_unionSimpleRoots (χ := χ) (J := Set.univ) Δ hΔunion) hx
  have ht_eq : t = rootDiagUnit ReeTag.F4.tag (coordTuple Δ c) := by
    rw [hc₀, hceq]
  have hΔroot : ∀ β ∈ Δ, IsRoot ReeTag.F4.tag β :=
    fun β hβ => simpleRoots_isRoot (hΔdef ▸ hβ)
  have hΔ' : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
    rw [hΔdef]
    exact hΔ
  let b : Fin ReeTag.F4.tag.rank → Lˣ := coordTuple Δ c
  let cD : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ :=
    fun γ => c (ReeTag.F4.dualRoot γ) ^ rootExp a₀ (ReeTag.F4.dualRoot γ)
  let π : (Fin ReeTag.F4.tag.rank → ℤ) ≃+ (Fin ReeTag.F4.tag.rank → ℤ) :=
    DistribMulAction.toAddEquiv (Fin ReeTag.F4.tag.rank → ℤ) w
  let c' : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ := fun γ => cD (w⁻¹ • γ)
  have himage : (Δ.image ReeTag.F4.dualRoot).image π = Δ := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_image, Set.image_image]
    change (fun α => w • ReeTag.F4.dualRoot α) '' (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) =
      (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ))
    rw [hΔ'.image_eq]
  have hσ' : canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      Fext F (rootDiagUnit ReeTag.F4.tag b) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ = rootDiagUnit ReeTag.F4.tag b := by
    have h := hσ.2
    rw [ht_eq] at h
    exact h
  have hσd : canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      Fext F (rootDiagUnit ReeTag.F4.tag b) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
      rootDiagUnit ReeTag.F4.tag (coordTuple Δ c') := by
    rw [hF.fext_rootDiagUnit b]
    have hree : reeTuple a₀ b = coordTuple (Δ.image ReeTag.F4.dualRoot) cD :=
      reeTuple_coordTuple (L := L) a₀ Δ hΔroot c
    rw [hree]
    have hπ : ∀ x y, iform (π x) (π y) = iform x y := fun x y => iform_smul w x y
    have hπΦ : ∀ α, IsRoot ReeTag.F4.tag α → IsRoot ReeTag.F4.tag (π α) :=
      fun α hα => IsRoot.smul hα w
    have hgX : ∀ α, IsRoot ReeTag.F4.tag α → ∃ ε : Lˣ, ∀ x : L,
        canonicalRep (coxeterSystem ReeTag.F4.tag) L w * pinnedX ReeTag.F4.tag L α x *
            (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
          pinnedX ReeTag.F4.tag L (π α) (ε * x) := by
      intro α hα
      refine ⟨1, fun x => ?_⟩
      simpa [π] using canonicalRep_conj_pinnedX (L := L) w hα x
    have hgT : ∀ s : Fin ReeTag.F4.tag.rank → Lˣ,
        ∃ s', canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
            rootDiagUnit ReeTag.F4.tag s *
              (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
          rootDiagUnit ReeTag.F4.tag s' := by
      intro s
      have hnorm : canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈
          Subgroup.normalizer (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) :=
        (canonical_weyl_root_transport ReeTag.F4.tag L).2.2 w
      exact exists_rootDiagUnit_eq_of_mem_torusGroup
        ((Subgroup.mem_normalizer_iff.1 hnorm (rootDiagUnit ReeTag.F4.tag s)).1
          (rootDiagUnit_mem_torusGroup s))
    have hΔ'root : ∀ γ ∈ Δ.image ReeTag.F4.dualRoot, IsRoot ReeTag.F4.tag γ := by
      intro γ hγ
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
      exact ReeTag.isRoot_dualRoot (hΔroot β hβ)
    have hQd := conj_rootDiagUnit_coordTuple (g := canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
      (π := π) hπ hπΦ hgX hgT hΔ'root cD
    rw [hQd, himage]
    rfl
  have hfix : coordTuple Δ c' = coordTuple Δ c := by
    apply hinj
    calc rootDiagUnit ReeTag.F4.tag (coordTuple Δ c')
        = canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
            Fext F (rootDiagUnit ReeTag.F4.tag b) *
              (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ := hσd.symm
      _ = rootDiagUnit ReeTag.F4.tag b := hσ'
      _ = rootDiagUnit ReeTag.F4.tag (coordTuple Δ c) := rfl
  have hc' : ∀ β ∈ Δ, ∃ m : ℕ, c' β ^ p ^ m = 1 := by
    intro β hβ
    obtain ⟨m, hm⟩ := hc (ReeTag.F4.dualRoot (w⁻¹ • β)) (dualRoot_inv_smul_mem hΔroot hΔ' hβ)
    refine ⟨m, ?_⟩
    change (c (ReeTag.F4.dualRoot (w⁻¹ • β)) ^
      rootExp a₀ (ReeTag.F4.dualRoot (w⁻¹ • β))) ^ p ^ m = 1
    rw [pow_right_comm, hm, one_pow]
  have hclosure : AddSubgroup.closure (corootVec '' kernelRoots χ) =
      AddSubgroup.closure (corootVec '' (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ))) := by
    rw [← unionRoots_univ_eq_kernelRoots (χ := χ), hΔunion]
    exact closure_corootVec_unionRoots_eq (χ := χ) (J := Set.univ)
  have hsat' : CorootPSaturated p (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
    intro y hy
    rw [← hclosure] at hy ⊢
    exact hsat y hy
  have hfinal :=
    eqOn_of_coordTuple_eq (k := L) hp
      (linearIndependent_corootVec_unionSimpleRoots (χ := χ) (J := Set.univ) Δ hΔunion)
      hsat' hc hc' hfix.symm
  refine ⟨c, ht_eq, ?_⟩
  intro β hβ
  have hβθ : w • ReeTag.F4.dualRoot β ∈ Δ := hΔ'.mapsTo hβ
  have h2 := hfinal (w • ReeTag.F4.dualRoot β) hβθ
  rw [h2]
  simp only [c', cD, inv_smul_smul, ReeTag.dualRoot_dualRoot (hΔroot β hβ)]

end CFSG.HardMathSupport.C14Idx
