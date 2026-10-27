module

public import CFSG.HardMathSupport.C14IdxReeBruhat
public import CFSG.LieType.Chevalley.FoldedWeylOrbits
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


private lemma weylPerm_rootReflection_dualRoot
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) :
    ReeTag.F4.weylPerm (rootReflection γ) = rootReflection (ReeTag.F4.dualRoot γ) := by
  obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 hγ
  have hdual : ReeTag.F4.weylPerm u • (Pi.single (ReeTag.F4.perm j) 1) =
      ReeTag.F4.dualRoot γ := by
    rw [← huj, ReeTag.F4.dualRoot_smul u (isRoot_single ReeTag.F4.tag j),
      ReeTag.F4.dualRoot_single]
  have hweyl : ReeTag.F4.weylPerm (rootReflection γ) =
      ReeTag.F4.weylPerm u * simple ReeTag.F4.tag (ReeTag.F4.perm j) *
        (ReeTag.F4.weylPerm u)⁻¹ := by
    rw [rootReflection_eq_conj huj, map_mul, map_mul, ReeTag.weylPerm_simple,
      MulEquiv.map_inv]
  rw [hweyl]
  exact (rootReflection_eq_conj hdual).symm

private lemma weylPerm_conj_eq_of_commute {M : Type*}
    [CommGroup M] {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M}
    {w : WeylGroup ReeTag.F4.tag}
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΨp : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (posRoots (kernelRoots χ))
      (posRoots (kernelRoots χ)))
    {v : WeylGroup ReeTag.F4.tag} (hv : v ∈ unionWeylGroup χ Set.univ)
    (hvθ : ∀ α ∈ unionRoots χ Set.univ,
      w • ReeTag.F4.dualRoot (v • α) = v • (w • ReeTag.F4.dualRoot α)) :
    w * ReeTag.F4.weylPerm v * w⁻¹ = v := by
  classical
  let θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ :=
    fun α => w • ReeTag.F4.dualRoot α
  have hπ : Set.BijOn θ (unionRoots χ Set.univ) (unionRoots χ Set.univ) := by
    rw [unionRoots_univ_eq_kernelRoots]
    simpa [θ] using hΨ
  have hπΔ : Set.MapsTo θ (unionSimpleRoots χ Set.univ) (unionSimpleRoots χ Set.univ) := by
    have h := (bijOn_simpleRoots_of_reeTwist hΨ hΨp).mapsTo
    have hset : (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)) =
        unionSimpleRoots χ Set.univ := by
      rw [← unionRoots_univ_eq_kernelRoots]
      exact Set.ext fun β => mem_simpleRoots_unionRoots_iff
    rw [hset] at h
    simpa [θ] using h
  have hmem : w * ReeTag.F4.weylPerm v * w⁻¹ ∈ unionWeylGroup χ Set.univ := by
    refine Subgroup.closure_induction (p := fun u _ =>
      w * ReeTag.F4.weylPerm u * w⁻¹ ∈ unionWeylGroup χ Set.univ) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨β, hβ, rfl⟩
      have hβr : IsRoot ReeTag.F4.tag β := isRoot_of_mem_unionSimpleRoots hβ
      have hθβ : θ β ∈ unionSimpleRoots χ Set.univ := hπΔ hβ
      rw [weylPerm_rootReflection_dualRoot hβr,
        ← rootReflection_smul_root w (ReeTag.isRoot_dualRoot hβr)]
      exact rootReflection_mem_unionWeylGroup hθβ
    · have h1 : w * ReeTag.F4.weylPerm (1 : WeylGroup ReeTag.F4.tag) * w⁻¹ = 1 := by
        rw [map_one]
        group
      rw [h1]
      exact one_mem _
    · intro x y _ _ hx hy
      have h1 : w * ReeTag.F4.weylPerm (x * y) * w⁻¹ =
          (w * ReeTag.F4.weylPerm x * w⁻¹) * (w * ReeTag.F4.weylPerm y * w⁻¹) := by
        rw [map_mul]
        group
      rw [h1]
      exact mul_mem hx hy
    · intro x _ hx
      have h1 : w * ReeTag.F4.weylPerm x⁻¹ * w⁻¹ = (w * ReeTag.F4.weylPerm x * w⁻¹)⁻¹ := by
        rw [map_inv]
        group
      rw [h1]
      exact inv_mem hx
  have hagree : ∀ α ∈ unionRoots χ Set.univ,
      (w * ReeTag.F4.weylPerm v * w⁻¹) • α = v • α := by
    intro α hα
    obtain ⟨β, hβ, hβeq⟩ := hπ.surjOn hα
    rw [← hβeq]
    simp only [θ]
    have hβr : IsRoot ReeTag.F4.tag β := isRoot_of_mem_unionRoots hβ
    have hkey : w • ReeTag.F4.dualRoot (v • β) = v • (w • ReeTag.F4.dualRoot β) := hvθ β hβ
    rw [mul_smul, mul_smul, inv_smul_smul,
      ReeTag.F4.weylPerm_smul_eq_dualRoot v (ReeTag.isRoot_dualRoot hβr),
      ReeTag.F4.dualRoot_dualRoot hβr]
    exact hkey
  have hratio : (w * ReeTag.F4.weylPerm v * w⁻¹)⁻¹ * v ∈ unionWeylGroup χ Set.univ :=
    mul_mem (inv_mem hmem) hv
  have hratio1 : (w * ReeTag.F4.weylPerm v * w⁻¹)⁻¹ * v = 1 := by
    refine eq_one_of_forall_smul_eq hratio fun α hα => ?_
    rw [mul_smul, ← hagree α hα, inv_smul_smul]
  have hfinal := congrArg (fun z => (w * ReeTag.F4.weylPerm v * w⁻¹) * z) hratio1
  rw [mul_one, mul_inv_cancel_left] at hfinal
  exact hfinal.symm

private lemma mem_closure_of_unipotent_fixed {L : Type}
    [Field L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} {w : WeylGroup ReeTag.F4.tag}
    {u : ModGL ReeTag.F4.tag L} (hu : u ∈ unionUnipotent L χ Set.univ)
    (hfix : u ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    u ∈ Subgroup.closure {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
      x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  have hU2 : IsPGroup 2 (posUnipotent ReeTag.F4.tag L) :=
    isPGroup_of_le_posFiltration (K := L) 2 Label.position_lt_card
      (posUnipotent_le_posFiltration ReeTag.F4.tag L)
  obtain ⟨k, hk⟩ := hU2 ⟨u, unionUnipotent_le_posUnipotent hu⟩
  exact Subgroup.subset_closure
    ⟨unionUnipotent_le_unionRootSpan hu, hfix, k, by simpa using congrArg Subtype.val hk⟩

theorem exists_reeTwistFixed_torus_mul_mem_closure {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΨp : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (posRoots (kernelRoots χ))
      (posRoots (kernelRoots χ)))
    {s : ModGL ReeTag.F4.tag L} (hs : s ∈ unionRootSpan L χ Set.univ)
    (hσ : s ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ t ∈ unionTorus L χ Set.univ,
      t ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      t⁻¹ * s ∈ Subgroup.closure {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
        x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
          ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  let D : Subgroup (ModGL ReeTag.F4.tag L) := Subgroup.closure {x : ModGL ReeTag.F4.tag L |
    x ∈ unionRootSpan L χ Set.univ ∧
      x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1}
  obtain ⟨x, hxW, hxθ, t, ht, htfix, u, hu, hufix, v, hv, hvfix, hst⟩ :=
    exists_reeTwistFixed_bruhat_factor hF hΨ hΨp hs hσ
  have huD : u ∈ D := mem_closure_of_unipotent_fixed hu hufix
  have hvD : v ∈ D := mem_closure_of_unipotent_fixed hv hvfix
  let θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ :=
    fun α => w • ReeTag.F4.dualRoot α
  have hπ : Set.BijOn θ (unionRoots χ Set.univ) (unionRoots χ Set.univ) := by
    rw [unionRoots_univ_eq_kernelRoots]
    simpa [θ] using hΨ
  have hπΔ : Set.MapsTo θ (unionSimpleRoots χ Set.univ) (unionSimpleRoots χ Set.univ) := by
    have h := (bijOn_simpleRoots_of_reeTwist hΨ hΨp).mapsTo
    have hset : (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)) =
        unionSimpleRoots χ Set.univ := by
      rw [← unionRoots_univ_eq_kernelRoots]
      exact Set.ext fun β => mem_simpleRoots_unionRoots_iff
    rw [hset] at h
    simpa [θ] using h
  have hπpos : ∀ α ∈ unionRoots χ Set.univ, 0 < height α → 0 < height (θ α) := by
    intro α hα hpos
    rw [unionRoots_univ_eq_kernelRoots] at hα
    simpa [θ] using (hΨp.mapsTo ⟨hα, hpos⟩).2
  have hπref : ∀ γ ∈ unionRoots χ Set.univ, ∀ α ∈ unionRoots χ Set.univ,
      θ (rootReflection γ • α) = rootReflection (θ γ) • θ α := by
    intro γ hγ α hα
    rw [unionRoots_univ_eq_kernelRoots] at hγ hα
    have hγr : IsRoot ReeTag.F4.tag γ := hγ.1
    have hαr : IsRoot ReeTag.F4.tag α := hα.1
    simp only [θ]
    rw [ReeTag.F4.dualRoot_smul (rootReflection γ) hαr,
      weylPerm_rootReflection_dualRoot hγr]
    have hmul : w * rootReflection (ReeTag.F4.dualRoot γ) =
        rootReflection (w • ReeTag.F4.dualRoot γ) * w := by
      rw [rootReflection_smul_root w (ReeTag.isRoot_dualRoot hγr)]
      group
    calc w • (rootReflection (ReeTag.F4.dualRoot γ) • ReeTag.F4.dualRoot α)
        = (w * rootReflection (ReeTag.F4.dualRoot γ)) • ReeTag.F4.dualRoot α := by
          rw [mul_smul]
      _ = (rootReflection (w • ReeTag.F4.dualRoot γ) * w) • ReeTag.F4.dualRoot α := by
          rw [hmul]
      _ = rootReflection (w • ReeTag.F4.dualRoot γ) • (w • ReeTag.F4.dualRoot α) := by
          rw [mul_smul]
  have hxθ' : ∀ α ∈ unionRoots χ Set.univ, θ (x • α) = x • θ α := by
    intro α hα
    rw [unionRoots_univ_eq_kernelRoots] at hα
    simpa [θ] using hxθ α hα
  have hxC : x ∈ Subgroup.closure {y : WeylGroup ReeTag.F4.tag |
      y ∈ unionWeylGroup χ Set.univ ∧
        (∀ α ∈ unionRoots χ Set.univ, θ (y • α) = y • θ α) ∧ y * y = 1} :=
    mem_closure_fixed_involutions θ hπ hπΔ hπpos hπref hxW hxθ'
  have hnwD : canonicalRep (coxeterSystem ReeTag.F4.tag) L x ∈ D := by
    let φ : WeylGroup ReeTag.F4.tag →* ModGL ReeTag.F4.tag L :=
      { toFun := canonicalRep (coxeterSystem ReeTag.F4.tag) L
        map_one' := canonicalRep_one _ _
        map_mul' := CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo }
    have hinv : ∀ y : WeylGroup ReeTag.F4.tag,
        canonicalRep (coxeterSystem ReeTag.F4.tag) L y⁻¹ =
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L y)⁻¹ := by
      intro y
      rw [eq_inv_iff_mul_eq_one, ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo,
        inv_mul_cancel, canonicalRep_one]
    have hXsub : φ '' {y : WeylGroup ReeTag.F4.tag | y ∈ unionWeylGroup χ Set.univ ∧
        (∀ α ∈ unionRoots χ Set.univ, θ (y • α) = y • θ α) ∧ y * y = 1} ⊆
        {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
          x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
            ∃ k : ℕ, x ^ 2 ^ k = 1} := by
      rintro _ ⟨y, ⟨hyW, hyθ, hy2⟩, rfl⟩
      refine ⟨canonicalRep_mem_rootSpan_unionRoots hyW, ?_, ?_⟩
      · refine mem_twistedFixed.2
          ⟨canonicalRep_mem_adjointGroup (coxeterSystem ReeTag.F4.tag) L y, ?_⟩
        change canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
            Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L y) *
            (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
          canonicalRep (coxeterSystem ReeTag.F4.tag) L y
        have hconj := weylPerm_conj_eq_of_commute hΨ hΨp hyW hyθ
        have hkey : canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
              canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm y) *
              (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
            canonicalRep (coxeterSystem ReeTag.F4.tag) L (w * ReeTag.F4.weylPerm y * w⁻¹) := by
          rw [← hinv w,
            ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo w (ReeTag.F4.weylPerm y),
            ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo
              (w * ReeTag.F4.weylPerm y) w⁻¹]
        rw [hF.fext_canonicalRep, hkey, hconj]
      · refine ⟨1, ?_⟩
        change φ y * φ y = 1
        rw [show φ y = canonicalRep (coxeterSystem ReeTag.F4.tag) L y from rfl]
        simpa [pow_two] using
          CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_self_charTwo hy2
    have h1 : φ x ∈ (Subgroup.closure {y : WeylGroup ReeTag.F4.tag |
        y ∈ unionWeylGroup χ Set.univ ∧
          (∀ α ∈ unionRoots χ Set.univ, θ (y • α) = y • θ α) ∧ y * y = 1}).map φ :=
      Subgroup.mem_map_of_mem φ hxC
    rw [MonoidHom.map_closure] at h1
    exact Subgroup.closure_mono hXsub h1
  refine ⟨t, ht, htfix, ?_⟩
  have hcalc : t⁻¹ * s = u * canonicalRep (coxeterSystem ReeTag.F4.tag) L x * v := by
    rw [hst]
    group
  rw [hcalc]
  exact mul_mem (mul_mem huD hnwD) hvD

end CFSG.HardMathSupport.C14Idx
