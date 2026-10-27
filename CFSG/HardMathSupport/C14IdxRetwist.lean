module

public import CFSG.HardMathSupport.C14IdxFrobAction
public import CFSG.LieType.Chevalley.UnionPositiveSystems
public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.HardMathSupport.C14IdxBorelHolds
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.Chevalley.E6EvenRootTorus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.HardMathSupport.C14Idx

open scoped CFSG.ConvolutionPoints

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem idxConclusion_of_conj
    {τ : Tag} {L : Type} [Field L] {ι : Type} {p : ℕ} {a : ι → Fin τ.rank → Lˣ}
    {F σ : adjointGroup τ L →* adjointGroup τ L} {m : adjointGroup τ L} (hm : m ∈ famM a)
    (hσ : ∀ g, σ g = m⁻¹ * F (m * g * m⁻¹) * m) (h : IdxConclusion p a σ) :
    IdxConclusion p a F := by
  let Hσ : Subgroup (adjointGroup τ L) := famS a ⊓ σ.eqLocus (MonoidHom.id _)
  let HF : Subgroup (adjointGroup τ L) := famS a ⊓ F.eqLocus (MonoidHom.id _)
  let Eσ : Set (adjointGroup τ L) := {x | x ∈ Hσ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  let EF : Set (adjointGroup τ L) := {x | x ∈ HF ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  have hfamM : (famM a).map (MulAut.conj m).toMonoidHom = famM a := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer hm :
        m ∈ Subgroup.normalizer (famM a : Set (adjointGroup τ L)))
    simpa using h
  have hfamS : (famS a).map (MulAut.conj m).toMonoidHom = famS a := by
    rw [famS, Subgroup.map_commutator, hfamM]
  have hfix : (σ.eqLocus (MonoidHom.id _)).map (MulAut.conj m).toMonoidHom =
      F.eqLocus (MonoidHom.id _) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F (m * x * m⁻¹) = m * x * m⁻¹
      have hx1 : x = m⁻¹ * F (m * x * m⁻¹) * m := by
        rw [← hσ x]
        simpa using hx.symm
      calc F (m * x * m⁻¹) = m * (m⁻¹ * F (m * x * m⁻¹) * m) * m⁻¹ := by group
        _ = m * x * m⁻¹ := by rw [← hx1]
    · rintro hy
      have hy' : F y = y := by simpa using hy
      refine ⟨m⁻¹ * y * m, ?_, ?_⟩
      · change σ (m⁻¹ * y * m) = m⁻¹ * y * m
        rw [hσ]
        have h1 : m * (m⁻¹ * y * m) * m⁻¹ = y := by group
        rw [h1, hy']
      · show m * (m⁻¹ * y * m) * m⁻¹ = y
        group
  have hmapH : Hσ.map (MulAut.conj m).toMonoidHom = HF := by
    dsimp only [Hσ, HF]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj m).injective, hfamS, hfix]
  have hmapE : (Subgroup.closure Eσ).map (MulAut.conj m).toMonoidHom =
      Subgroup.closure EF := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨hmapH ▸ Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hx.1, ⟨k, ?_⟩⟩
      rw [← map_pow, hk, map_one]
    · rintro ⟨hyH, k, hk⟩
      rw [← hmapH] at hyH
      obtain ⟨x, hxH, hxy⟩ := hyH
      have hxy' : (MulAut.conj m) x = y := hxy
      have hxk : x ^ 2 ^ k = 1 := by
        apply (MulAut.conj m).injective
        rw [map_pow, hxy', hk, map_one]
      exact ⟨x, ⟨hxH, ⟨k, hxk⟩⟩, hxy⟩
  have hindex : ((Subgroup.closure EF).subgroupOf HF).index =
      ((Subgroup.closure Eσ).subgroupOf Hσ).index := by
    change (Subgroup.closure EF).relIndex HF = (Subgroup.closure Eσ).relIndex Hσ
    rw [← hmapE, ← hmapH]
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj m).injective
  change ¬ p ∣ ((Subgroup.closure EF).subgroupOf HF).index
  rw [hindex]
  exact h

theorem exists_pinned_retwist
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {e : ℕ} (he : 1 ≤ e)
    {Q' : ModGL τ L} (hQT : ∀ t, ∃ t', Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t')
    (hQ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n)
    {F₀ : adjointGroup τ L →* adjointGroup τ L}
    (hF₀ : ∀ g, (F₀ g : ModGL τ L) = frobTwistGL τ L 2 e Q' g)
    (hM : ∀ g ∈ famM a, F₀ g ∈ famM a) :
    ∃ m ∈ famM a, ∃ Q'' : ModGL τ L, ∃ θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ),
      (∀ g, ((m⁻¹ * F₀ (m * g * m⁻¹) * m : adjointGroup τ L) : ModGL τ L) =
        frobTwistGL τ L 2 e Q'' g) ∧
      (∀ x y, iform (θ x) (θ y) = iform x y) ∧ (∀ α, IsRoot τ α → IsRoot τ (θ α)) ∧
      (∀ α, IsRoot τ α → ∀ c : L, Q'' * pinnedX τ L α c * Q''⁻¹ = pinnedX τ L (θ α) c) ∧
      (∀ t, ∃ t', Q'' * rootDiagUnit τ t * Q''⁻¹ = rootDiagUnit τ t') ∧
      (adjointGroup τ L).map (MulAut.conj Q'').toMonoidHom = adjointGroup τ L ∧
      Set.BijOn θ (familyKernel a) (familyKernel a) ∧
      Set.BijOn θ (posRoots (familyKernel a)) (posRoots (familyKernel a)) := by
  obtain ⟨h, hhT, Q₀, θ₀, hQ'eq, hiform₀, hroot₀, hX₀, hQT₀, hadj₀⟩ :=
    exists_eq_torus_mul_pinned hQT hQ
  have hF₀Q : ∀ g, (F₀ g : ModGL τ L) = frobTwistGL τ L 2 e (h * Q₀) g := by
    intro g
    rw [← hQ'eq]
    exact hF₀ g
  have hbij₀ : Set.BijOn θ₀ (familyKernel a) (familyKernel a) :=
    bijOn_familyKernel_of_mapsTo_famM hhT hroot₀ hX₀ hF₀Q hM
  have hTconn : IsConnectedAlgebraicSubgroup L ((torusGroup τ L).map
      (modGLPoint τ L).toMonoidHom) := by
    have hgen : Set.range (fun p : Fin τ.rank × Lˣ => torusElt τ L p.1 p.2) ⊆
        {g : ModGL τ L | ∃ lam ∈ (Set.univ : Set (Fin τ.rank → ℤ)), ∃ c : Lˣ,
          g = rootDiagUnit τ fun i => c ^ lam i} := by
      rintro g ⟨⟨i, c⟩, rfl⟩
      exact ⟨τ.cartan i, Set.mem_univ _, c, torusElt_eq_rootDiagUnit i c⟩
    have hsub : {g : ModGL τ L | ∃ lam ∈ (Set.univ : Set (Fin τ.rank → ℤ)), ∃ c : Lˣ,
          g = rootDiagUnit τ fun i => c ^ lam i} ⊆ (torusGroup τ L : Set (ModGL τ L)) := by
      rintro g ⟨lam, -, c, rfl⟩
      exact rootDiagUnit_mem_torusGroup _
    have hTeq : torusGroup τ L = Subgroup.closure {g : ModGL τ L |
        ∃ lam ∈ (Set.univ : Set (Fin τ.rank → ℤ)), ∃ c : Lˣ,
          g = rootDiagUnit τ fun i => c ^ lam i} := by
      refine le_antisymm (Subgroup.closure_mono hgen) ?_
      exact (Subgroup.closure_le (torusGroup τ L)).2 hsub
    rw [hTeq]
    exact isConnectedAlgebraicSubgroup_closure_cocharCurve (Set.univ)
  have hQ₀T : ∀ g ∈ torusGroup τ L, frobTwistGL τ L 2 e Q₀ g ∈ torusGroup τ L := by
    intro g hg
    obtain ⟨t, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
    rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map]
    obtain ⟨t', ht'⟩ := hQT₀ (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom (t i))
    rw [ht']
    exact rootDiagUnit_mem_torusGroup t'
  obtain ⟨-, -, -, hlangT⟩ :=
    exists_frobTwist_restriction (p := 2) hTconn he Q₀ hQ₀T
  obtain ⟨z, hzT, hz⟩ := hlangT h⁻¹ (inv_mem hhT)
  let zA : adjointGroup τ L :=
    ⟨z, CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' hzT⟩
  have hcommT : ∀ u ∈ torusGroup τ L, ∀ v ∈ torusGroup τ L, u * v = v * u :=
    fun u hu v hv => CFSG.StandardType.LayerExc.commute_of_mem_torusGroup hu hv
  have hF₀_eval : ∀ y : adjointGroup τ L,
      (F₀ y : ModGL τ L) = h * frobTwistGL τ L 2 e Q₀ (y : ModGL τ L) * h⁻¹ := by
    intro y
    rw [hF₀, hQ'eq, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hconjz : ∀ x : adjointGroup τ L,
      ((zA⁻¹ * F₀ (zA * x * zA⁻¹) * zA : adjointGroup τ L) : ModGL τ L) =
        frobTwistGL τ L 2 e Q₀ (x : ModGL τ L) := by
    intro x
    set c := frobTwistGL τ L 2 e Q₀ z with hc
    have hzc : z⁻¹ * c = h⁻¹ := hz
    have hcz : c⁻¹ * z = h := by
      calc c⁻¹ * z = (z⁻¹ * c)⁻¹ := by group
        _ = h := by rw [hzc, inv_inv]
    have h1 : z⁻¹ * h * c = 1 := by
      rw [mul_assoc, hcommT h hhT c (hQ₀T z hzT), ← mul_assoc, hzc, inv_mul_cancel]
    have h2 : c⁻¹ * h⁻¹ * z = 1 := by
      rw [hcommT c⁻¹ (inv_mem (hQ₀T z hzT)) h⁻¹ (inv_mem hhT), mul_assoc, hcz,
        inv_mul_cancel]
    have hcancel : ∀ X : ModGL τ L, z⁻¹ * (h * (c * X * c⁻¹) * h⁻¹) * z = X := by
      intro X
      calc z⁻¹ * (h * (c * X * c⁻¹) * h⁻¹) * z
          = (z⁻¹ * h * c) * X * (c⁻¹ * h⁻¹ * z) := by group
        _ = 1 * X * 1 := by rw [h1, h2]
        _ = X := by simp
    have hstep : ((zA⁻¹ * F₀ (zA * x * zA⁻¹) * zA : adjointGroup τ L) : ModGL τ L) =
        z⁻¹ * (h * (c * frobTwistGL τ L 2 e Q₀ (x : ModGL τ L) * c⁻¹) * h⁻¹) * z := by
      rw [show ((zA⁻¹ * F₀ (zA * x * zA⁻¹) * zA : adjointGroup τ L) : ModGL τ L) =
          z⁻¹ * (F₀ (zA * x * zA⁻¹) : ModGL τ L) * z by
        dsimp only [zA]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]]
      rw [hF₀_eval]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rfl
    calc ((zA⁻¹ * F₀ (zA * x * zA⁻¹) * zA : adjointGroup τ L) : ModGL τ L)
        = z⁻¹ * (h * (c * frobTwistGL τ L 2 e Q₀ (x : ModGL τ L) * c⁻¹) * h⁻¹) * z := hstep
      _ = frobTwistGL τ L 2 e Q₀ (x : ModGL τ L) := hcancel _
  let F₁ : adjointGroup τ L →* adjointGroup τ L :=
    (MulAut.conj zA⁻¹).toMonoidHom.comp (F₀.comp (MulAut.conj zA).toMonoidHom)
  have hF₁_conj : ∀ x : adjointGroup τ L, (F₁ x : ModGL τ L) =
      frobTwistGL τ L 2 e Q₀ (x : ModGL τ L) := fun x => hconjz x
  have hzA_famM : zA ∈ famM a := by
    change (zA : ModGL τ L) ∈ familyGroup a
    exact Subgroup.mem_sup_left hzT
  have hF1M : ∀ x ∈ famM a, F₁ x ∈ famM a := by
    intro x hx
    exact mul_mem (mul_mem (inv_mem hzA_famM)
      (hM _ (mul_mem (mul_mem hzA_famM hx) (inv_mem hzA_famM)))) hzA_famM
  have hF1S : ∀ x ∈ famS a, F₁ x ∈ famS a := by
    have hle : (famM a).map F₁ ≤ famM a := by
      rintro _ ⟨x, hx, rfl⟩
      exact hF1M x hx
    have hmap : (famS a).map F₁ ≤ famS a := by
      rw [famS, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hle hle
    intro x hx
    exact hmap (Subgroup.mem_map_of_mem F₁ hx)
  have hZSconn : IsConnectedAlgebraicSubgroup L
      (((famS a).map (adjointGroup τ L).subtype).map (modGLPoint τ L).toMonoidHom) :=
    isConnectedAlgebraicSubgroup_famS a
  have hQ₀Z : ∀ g ∈ (famS a).map (adjointGroup τ L).subtype,
      frobTwistGL τ L 2 e Q₀ g ∈ (famS a).map (adjointGroup τ L).subtype := by
    rintro g ⟨sA, hsA, rfl⟩
    exact ⟨F₁ sA, hF1S sA hsA, hF₁_conj sA⟩
  obtain ⟨-, -, -, hlangZ⟩ :=
    exists_frobTwist_restriction (p := 2) hZSconn he Q₀ hQ₀Z
  obtain ⟨u, huW, hposBij⟩ :=
    exists_smul_bijOn_posRoots (χ := familyChar a) (J := Set.univ) θ₀ (by
      rw [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar]
      exact hbij₀)
  have hposBij' : Set.BijOn (fun α => u • θ₀ α) (posRoots (familyKernel a))
      (posRoots (familyKernel a)) := by
    rwa [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar] at hposBij
  have hn_root : canonicalRep (coxeterSystem τ) L u ∈ rootSpan τ L (familyKernel a) := by
    have h := canonicalRep_mem_rootSpan_unionRoots (K := L) (χ := familyChar a) (J := Set.univ) huW
    rwa [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar] at h
  have hn_adj : canonicalRep (coxeterSystem τ) L u ∈ adjointGroup τ L :=
    rootSpan_le_adjointGroup L (familyKernel a) hn_root
  have hn_uZ : canonicalRep (coxeterSystem τ) L u ∈
      (famS a).map (adjointGroup τ L).subtype := by
    rwa [map_famS_subtype_eq_rootSpan a]
  obtain ⟨s, hsZ, hs⟩ := hlangZ (canonicalRep (coxeterSystem τ) L u) hn_uZ
  obtain ⟨sA, hsA, hsAeq⟩ := hsZ
  have hsAval : (sA : ModGL τ L) = s := hsAeq
  have hfamS_le_famM : famS a ≤ famM a := Subgroup.commutator_le_of_le le_rfl le_rfl
  let m : adjointGroup τ L := zA * sA
  have hm : m ∈ famM a := mul_mem hzA_famM (hfamS_le_famM hsA)
  have hmconj : ∀ g : adjointGroup τ L,
      ((m⁻¹ * F₀ (m * g * m⁻¹) * m : adjointGroup τ L) : ModGL τ L) =
        frobTwistGL τ L 2 e (canonicalRep (coxeterSystem τ) L u * Q₀) g := by
    intro g
    have hx : m * g * m⁻¹ = zA * (sA * g * sA⁻¹) * zA⁻¹ := by
      dsimp only [m]
      group
    have hL : ((m⁻¹ * F₀ (m * g * m⁻¹) * m : adjointGroup τ L) : ModGL τ L) =
        (sA : ModGL τ L)⁻¹ *
          ((zA⁻¹ * F₀ (zA * (sA * g * sA⁻¹) * zA⁻¹) * zA : adjointGroup τ L) : ModGL τ L) *
          (sA : ModGL τ L) := by
      rw [hx]
      dsimp only [m]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      group
    have harg : ((sA * g * sA⁻¹ : adjointGroup τ L) : ModGL τ L) =
        s * (g : ModGL τ L) * s⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsAval]
    have hs' : s⁻¹ * frobTwistGL τ L 2 e Q₀ s =
        canonicalRep (coxeterSystem τ) L u := hs
    have hs'' : (frobTwistGL τ L 2 e Q₀ s)⁻¹ * s =
        (canonicalRep (coxeterSystem τ) L u)⁻¹ := by
      rw [← hs']
      group
    calc ((m⁻¹ * F₀ (m * g * m⁻¹) * m : adjointGroup τ L) : ModGL τ L)
        = (sA : ModGL τ L)⁻¹ *
          ((zA⁻¹ * F₀ (zA * (sA * g * sA⁻¹) * zA⁻¹) * zA : adjointGroup τ L) : ModGL τ L) *
          (sA : ModGL τ L) := hL
      _ = s⁻¹ * frobTwistGL τ L 2 e Q₀ (sA * g * sA⁻¹ : adjointGroup τ L) * s := by
        rw [hconjz (sA * g * sA⁻¹), hsAval]
      _ = s⁻¹ * (frobTwistGL τ L 2 e Q₀ s *
            frobTwistGL τ L 2 e Q₀ (g : ModGL τ L) *
            (frobTwistGL τ L 2 e Q₀ s)⁻¹) * s := by
        rw [harg]
        simp only [map_mul, map_inv]
      _ = (s⁻¹ * frobTwistGL τ L 2 e Q₀ s) *
            frobTwistGL τ L 2 e Q₀ (g : ModGL τ L) *
            ((frobTwistGL τ L 2 e Q₀ s)⁻¹ * s) := by simp only [mul_assoc]
      _ = frobTwistGL τ L 2 e (canonicalRep (coxeterSystem τ) L u * Q₀) g := by
        rw [hs', hs'', frobTwistGL_apply, frobTwistGL_apply]
        group
  refine ⟨m, hm, canonicalRep (coxeterSystem τ) L u * Q₀,
    θ₀.trans (DistribMulAction.toAddEquiv (Fin τ.rank → ℤ) u), hmconj, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x y
    change iform (u • θ₀ x) (u • θ₀ y) = iform x y
    rw [iform_smul, hiform₀]
  · intro α hα
    exact IsRoot.smul (hroot₀ α hα) u
  · intro α hα c
    change (canonicalRep (coxeterSystem τ) L u * Q₀) * pinnedX τ L α c *
        (canonicalRep (coxeterSystem τ) L u * Q₀)⁻¹ = pinnedX τ L (u • θ₀ α) c
    rw [show (canonicalRep (coxeterSystem τ) L u * Q₀) * pinnedX τ L α c *
        (canonicalRep (coxeterSystem τ) L u * Q₀)⁻¹ =
        canonicalRep (coxeterSystem τ) L u * (Q₀ * pinnedX τ L α c * Q₀⁻¹) *
          (canonicalRep (coxeterSystem τ) L u)⁻¹ by group]
    rw [hX₀ α hα]
    obtain ⟨ε, hε, hεc⟩ :=
      exists_canonicalRep_mul_pinnedX_mul_inv L u (hroot₀ α hα)
    rw [hεc]
    have hε1 : ε = 1 := by
      have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
      have h : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
    rw [hε1, one_mul]
  · intro t
    have hn_norm : canonicalRep (coxeterSystem τ) L u ∈
        Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
      canonicalRep_mem_normalizer u
    obtain ⟨t', ht'⟩ := hQT₀ t
    have hmem : canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ t' *
        (canonicalRep (coxeterSystem τ) L u)⁻¹ ∈ torusGroup τ L :=
      (Subgroup.mem_normalizer_iff.mp hn_norm (rootDiagUnit τ t')).1
        (rootDiagUnit_mem_torusGroup t')
    obtain ⟨t'', ht''⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmem
    exact ⟨t'', by
      rw [show (canonicalRep (coxeterSystem τ) L u * Q₀) * rootDiagUnit τ t *
          (canonicalRep (coxeterSystem τ) L u * Q₀)⁻¹ =
          canonicalRep (coxeterSystem τ) L u * (Q₀ * rootDiagUnit τ t * Q₀⁻¹) *
            (canonicalRep (coxeterSystem τ) L u)⁻¹ by group]
      rw [ht', ht'']⟩
  · have hn_norm_adj : (adjointGroup τ L).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) L u)).toMonoidHom = adjointGroup τ L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hn_adj)
    have hcomp : (MulAut.conj (canonicalRep (coxeterSystem τ) L u * Q₀)).toMonoidHom =
        ((MulAut.conj (canonicalRep (coxeterSystem τ) L u)).toMonoidHom).comp
          (MulAut.conj Q₀).toMonoidHom := by
      rw [map_mul]
      rfl
    rw [hcomp, ← Subgroup.map_map, hadj₀, hn_norm_adj]
  · have hu : Set.BijOn (fun α : Fin τ.rank → ℤ => u • α)
        (familyKernel a) (familyKernel a) := by
      refine Set.BijOn.mk ?_ ?_ ?_
      · intro α hα
        have hα' : α ∈ unionRoots (familyChar a) Set.univ := by
          rwa [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar]
        simpa [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar] using
          smul_mem_unionRoots huW hα'
      · intro α hα β hβ h
        exact smul_left_cancel u h
      · intro β hβ
        refine ⟨u⁻¹ • β, ?_, ?_⟩
        · have hβ' : β ∈ unionRoots (familyChar a) Set.univ := by
            rwa [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar]
          simpa [unionRoots_univ_eq_kernelRoots, kernelRoots_familyChar] using
            smul_mem_unionRoots (inv_mem huW) hβ'
        · simp
    change Set.BijOn (fun α => u • θ₀ α) (familyKernel a) (familyKernel a)
    exact hu.comp hbij₀
  · change Set.BijOn (fun α => u • θ₀ α) (posRoots (familyKernel a))
      (posRoots (familyKernel a))
    exact hposBij'

end CFSG.HardMathSupport.C14Idx
