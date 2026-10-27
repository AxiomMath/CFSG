module

public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieCore
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6NegDatumPlane
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6NegDatumCoroot
public import CFSG.LieType.Chevalley.RootHyperplaneGenerationR

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

section NegDatum

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint


local notation "θ₀" => CFSG.LieType.Chevalley.e6HighestRoot

theorem exists_radical_of_negDatum_r (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (hreg : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      ¬ TwKills K σ E₀ g0 α) :
    ∃ θ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag θ ∧
      (∀ x ∈ E₀, ∀ c : (AlgebraicClosure K)ˣ,
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
            g0 * rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform θ (Pi.single i 1)) * g0⁻¹ →
          x = 1) ∧
      ∃ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm ∧
        (∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
            (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ, -θ}).map
              (MulAut.conj g0).toMonoidHom) ∧
        ∃ R : Subgroup (twistedE6RootGroup K σ), R ≤ twE6LongRootRadical X ∧
          R ≤ Subgroup.closure (hyperRSet ⊤ E₀ (ringChar K) 3) ∧ ¬ R ≤ X := by
  classical
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hTt : ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hT x hx)
    rw [← hyx]
    simpa [MulAut.conj_apply, mul_assoc] using ((mem_twistedTorusOf).1 hy).1
  obtain ⟨β₁, β₂, δ, hβ₁, hβ₂, hβ₁₂, h3, hδ, hδθ, P, hPE, hPidx, hPchar⟩ :=
    exists_a2Plane_of_regular K σ hr E₀ hE₀.2 hcard g0 hTt hreg
  refine ⟨β₁ + β₂, hβ₁₂, twE6_corootLine_trivial K σ E₀ g0 hβ₁ hβ₂ hβ₁₂ h3 hδ hδθ, ?_⟩
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hSL2 : ∀ u : twistedE6RootGroup K σ,
      u ∈ twE6LongRootSL2 (TwE6LongRoot.stdX σ) (TwE6LongRoot.stdXm σ) ↔
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
          rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ₀, -θ₀} :=
    fun u => mem_twE6LongRootSL2_std_iff hpr hf1 hr K hK' σ hσ' u
  have hRad : ∀ u : twistedE6RootGroup K σ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        rootSpan TwistTag.E6.tag (AlgebraicClosure K)
          (parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion TwE6LongRoot.J0)) →
        u ∈ twE6LongRootRadical (TwE6LongRoot.stdX σ) :=
    fun u hu => (mem_twE6LongRootRadical_std_iff K σ u).2 hu
  have hrad : TwistTag.E6.orbitUnion TwE6LongRoot.J0 = e6LeviNodes := by
    rw [orbitUnion_J0_eq]
    rfl
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  have hFrc : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [hFr, hqf]
  have hFrEq : iterateFrobenius L (ringChar K) f = Fr :=
    RingHom.ext fun c => by rw [iterateFrobenius_def, hFrc]
  have hg0' : twistHom TwistTag.E6 L (iterateFrobenius L (ringChar K) f) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v := by
    rw [hFrEq]
    exact hg0
  obtain ⟨w, uJ, κ, z, hw, hκ, hz, hhA, hhF, hFz, hu1, hu2, hu3, hconj⟩ :=
    exists_lie_frame (L := L) (ringChar K) f hf1 hr hg0C hg0' hβ₁ hβ₂ hβ₁₂ (hv β₁) (hv β₂)
  rw [hFrEq] at hhF hFz
  obtain ⟨u₃, hu₃, t₃, ht₃, hdec⟩ := twE6_fixed_decomp hpr hf1 K hK' σ hσ' Fr hFrc hhA hhF
  obtain ⟨h, hh⟩ : ∃ h : ModGL TwistTag.E6.tag L,
      h = g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w * κ * z := ⟨_, rfl⟩
  rw [← hh] at hhA hhF hdec hconj
  have hrootsθ : ∀ α ∈ ({θ₀, -θ₀} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    · exact isRoot_e6HighestRoot
    · exact IsRoot.neg isRoot_e6HighestRoot
  obtain ⟨U₃, hU₃⟩ : ∃ U₃ : twistedE6RootGroup K σ, U₃ = ⟨u₃, hu₃⟩ := ⟨_, rfl⟩
  have hU₃c : ((U₃ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = u₃ := by rw [hU₃]
  have hSeq : twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)
      ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom) =
      (twE6LongRootSL2 (TwE6LongRoot.stdX σ) (TwE6LongRoot.stdXm σ)).map
        (MulAut.conj U₃).toMonoidHom :=
    TwE6LongRoot.twE6LongRootSL2_map (MulAut.conj U₃) _ _
  have hSbar : (rootSpan TwistTag.E6.tag L {θ₀, -θ₀}).map
      (MulAut.conj (baseChangeGL ι u₃)).toMonoidHom =
      (rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)}).map (MulAut.conj g0).toMonoidHom := by
    rw [← hconj, hdec, map_conj_mul,
      map_conj_eq_of_mem_normalizer (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
        hrootsθ ht₃)]
  have hSchar : ∀ u : twistedE6RootGroup K σ,
      u ∈ twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)
        ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom) ↔
      baseChangeGL ι (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)}).map (MulAut.conj g0).toMonoidHom := by
    intro u
    rw [hSeq, mem_map_conj_iff, hSL2, ← hSbar, mem_map_conj_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hU₃c]
    exact Iff.rfl
  refine ⟨(TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom,
    (TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom, ⟨U₃, rfl, rfl⟩, hSchar, ?_⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ModGL TwistTag.E6.tag L,
      n₁ = canonicalRep (coxeterSystem TwistTag.E6.tag) L uJ := ⟨_, rfl⟩
  rw [← hn₁] at hFz
  obtain ⟨nw, hnw⟩ : ∃ nw : ModGL TwistTag.E6.tag L,
      nw = canonicalRep (coxeterSystem TwistTag.E6.tag) L w := ⟨_, rfl⟩
  rw [← hnw] at hh
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁, δ₁ = w⁻¹ • β₁ := ⟨_, rfl⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, δ₂ = w⁻¹ • β₂ := ⟨_, rfl⟩
  obtain ⟨hpair₁, hpair₂, hsum⟩ := iform_theta_delta hβ₁ hβ₂ hβ₁₂ hw
  rw [← hδ₁] at hpair₁
  rw [← hδ₂] at hpair₂
  rw [← hδ₁, ← hδ₂] at hsum
  have hδ₁r : IsRoot TwistTag.E6.tag δ₁ := hδ₁ ▸ IsRoot.smul hβ₁ w⁻¹
  have hδ₂r : IsRoot TwistTag.E6.tag δ₂ := hδ₂ ▸ IsRoot.smul hβ₂ w⁻¹
  have hδ₁₂r : IsRoot TwistTag.E6.tag (δ₁ + δ₂) := by
    rw [hsum]
    exact isRoot_e6HighestRoot
  rw [← hδ₁, ← hδ₂] at hu1 hu2
  obtain ⟨a₁, ha₁, hψ₁⟩ := psi_pinnedX Fr uJ hδ₁r hu1
  obtain ⟨a₂, ha₂, hψ₂⟩ := psi_pinnedX Fr uJ hδ₂r hu2
  obtain ⟨a₃, ha₃, hψ₃⟩ := psi_pinnedX Fr uJ isRoot_e6HighestRoot hu3
  rw [← hn₁] at hψ₁ hψ₂ hψ₃
  let ψ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj n₁).toMonoidHom.comp (twistHom TwistTag.E6 L Fr)
  have hψ : ∀ y, ψ y = n₁ * twistHom TwistTag.E6 L Fr y * n₁⁻¹ := fun y => by
    simp [ψ, MulAut.conj_apply]
  obtain ⟨y₀, hy₀S, hy₀F, hy₀p, hy₀U⟩ := exists_fixed_rootSpan_heis (L := L) (ringChar K) f
    hf1 hδ₁r hδ₂r hδ₁₂r ψ a₁ a₂ a₃ ha₁ ha₂ ha₃
    (fun c => by rw [hψ, hψ₁, hFrc])
    (fun c => by rw [hψ, hψ₂, hFrc])
    (fun c => by rw [hsum, hψ, hψ₃, hFrc])
  have hFy : twistHom TwistTag.E6 L Fr y₀ = n₁⁻¹ * y₀ * n₁ := by
    have := hy₀F
    rw [hψ] at this
    calc twistHom TwistTag.E6 L Fr y₀ =
        n₁⁻¹ * (n₁ * twistHom TwistTag.E6 L Fr y₀ * n₁⁻¹) * n₁ := by group
      _ = n₁⁻¹ * y₀ * n₁ := by rw [this]
  have hFz' : twistHom TwistTag.E6 L Fr z = n₁⁻¹ * z := hFz
  obtain ⟨xhat, hxhat⟩ : ∃ xhat : ModGL TwistTag.E6.tag L, xhat = z⁻¹ * y₀ * z := ⟨_, rfl⟩
  have hxhatF : twistHom TwistTag.E6 L Fr xhat = xhat := by
    rw [hxhat, map_mul, map_mul, map_inv, hFz', hFy]
    group
  obtain ⟨shat, hshat⟩ : ∃ shat : ModGL TwistTag.E6.tag L, shat = h * xhat * h⁻¹ := ⟨_, rfl⟩
  have hshatF : twistHom TwistTag.E6 L Fr shat = shat := by
    rw [hshat, map_mul, map_mul, map_inv, hhF, hxhatF]
  have hzA : z ∈ adjointGroup TwistTag.E6.tag L :=
    (sup_le torusGroup_le_adjoint_E6 (rootSpan_le_adjoint_E6 _)) hz
  have hy₀A : y₀ ∈ adjointGroup TwistTag.E6.tag L := rootSpan_le_adjoint_E6 _ hy₀S
  have hshatA : shat ∈ adjointGroup TwistTag.E6.tag L := by
    rw [hshat, hxhat]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhA (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzA) hy₀A) hzA)) (Subgroup.inv_mem _ hhA)
  have hshatp : shat ^ (ringChar K ^ 2) = 1 := by
    have : shat = (MulAut.conj (h * z⁻¹)).toMonoidHom y₀ := by
      rw [hshat, hxhat]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this, ← map_pow, hy₀p, map_one]
  obtain ⟨x, hxG, hxι⟩ :=
    twE6_descent_of_pow hpr hf1 K hK' σ hσ' Fr hFrc hpr hr hshatA hshatF ⟨2, hshatp⟩
  obtain ⟨xG, hxGdef⟩ : ∃ xG : twistedE6RootGroup K σ, xG = ⟨x, hxG⟩ := ⟨_, rfl⟩
  have hxGc : ((xG : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = x := by
    rw [hxGdef]
  have hdec' : h = baseChangeGL ι u₃ * t₃ := hdec
  have hxι' : baseChangeGL ι x = shat := hxι
  have hconjι : baseChangeGL ι ((U₃⁻¹ * xG * U₃ : twistedE6RootGroup K σ) :
      ModGL TwistTag.E6.tag K) = t₃ * xhat * t₃⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hU₃c, hxGc, map_mul, map_inv]
    have hι₃ : baseChangeGL ι u₃ = h * t₃⁻¹ := by rw [hdec']; group
    rw [hι₃, hxι', hshat]
    group
  have hcoord₁ : δ₁ 1 = 1 := by
    have h := iform_e6HighestRoot δ₁
    rw [hpair₁] at h
    exact h.symm
  have hcoord₂ : δ₂ 1 = 1 := by
    have h := iform_e6HighestRoot δ₂
    rw [hpair₂] at h
    exact h.symm
  have hcoordθ : (δ₁ + δ₂) 1 = 2 := by
    rw [hsum]
    decide
  have hΦsub : ({δ₁, δ₂, δ₁ + δ₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆
      parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion TwE6LongRoot.J0) := by
    intro α hα
    rw [mem_radicalRoots_std_iff]
    rcases hα with h | h | h
    · rw [h]
      exact ⟨hδ₁r, by omega⟩
    · rw [h]
      exact ⟨hδ₂r, by omega⟩
    · rw [h]
      exact ⟨hδ₁₂r, by omega⟩
  have hQroots : ∀ α ∈ parabolicRadicalRoots TwistTag.E6.tag e6LeviNodes,
      IsRoot TwistTag.E6.tag α := fun _ hα => hα.1.1
  have hrootsδ : ∀ α ∈ ({δ₁, δ₂, δ₁ + δ₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with h | h | h
    · rw [h]; exact hδ₁r
    · rw [h]; exact hδ₂r
    · rw [h]; exact hδ₁₂r
  have hxQ : xG ∈
      twE6LongRootRadical ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom) := by
    rw [TwE6LongRoot.twE6LongRootRadical_map (MulAut.conj U₃) (TwE6LongRoot.stdX σ),
      mem_map_conj_iff]
    apply hRad
    rw [hconjι, hrad]
    have hy₀Q : y₀ ∈ rootSpan TwistTag.E6.tag L
        (parabolicRadicalRoots TwistTag.E6.tag e6LeviNodes) := by
      rw [← hrad]
      exact rootSpan_mono hΦsub hy₀S
    have hzN := torus_sup_rootSpan_parabolicRoots_le_normalizer_radical (L := L) e6LeviNodes hz
    have hxhatQ : xhat ∈ rootSpan TwistTag.E6.tag L
        (parabolicRadicalRoots TwistTag.E6.tag e6LeviNodes) := by
      rw [hxhat]
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hzN) y₀).1 hy₀Q
      rw [inv_inv] at this
      exact this
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hQroots ht₃) xhat).1 hxhatQ
  have htransport : ∀ S : Set (Fin TwistTag.E6.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwistTag.E6.tag α) →
      (rootSpan TwistTag.E6.tag L S).map (MulAut.conj nw).toMonoidHom =
        rootSpan TwistTag.E6.tag L ((fun α => w • α) '' S) := by
    intro S hS
    rw [hnw]
    exact (canonical_weyl_root_transport TwistTag.E6.tag L).1 w S hS
  have hnwN : nw ∈ Subgroup.normalizer
      (torusGroup TwistTag.E6.tag L : Set (ModGL TwistTag.E6.tag L)) :=
    hnw ▸ canonicalRep_mem_normalizer w
  have himg1 : (fun α => w • α) '' ({θ₀, -θ₀} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
      {β₁ + β₂, -(β₁ + β₂)} := by
    ext α
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_neg, hw]
  have himg2 : (fun α => w • α) '' ({δ₁, δ₂, δ₁ + δ₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
      {β₁, β₂, β₁ + β₂} := by
    ext α
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_add, hδ₁, hδ₂, smul_inv_smul]
  have hk : nw * κ * nw⁻¹ ∈ torusGroup TwistTag.E6.tag L ⊔
      rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)} := by
    have hmem : nw * κ * nw⁻¹ ∈ (torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L {θ₀, -θ₀}).map (MulAut.conj nw).toMonoidHom :=
      Subgroup.mem_map.2 ⟨κ, hκ, by simp [MulAut.conj_apply]⟩
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hnwN, htransport _ hrootsθ,
      himg1] at hmem
    exact hmem
  have hy₁ : nw * y₀ * nw⁻¹ ∈ rootSpan TwistTag.E6.tag L {β₁, β₂, β₁ + β₂} := by
    have hmem : nw * y₀ * nw⁻¹ ∈ (rootSpan TwistTag.E6.tag L {δ₁, δ₂, δ₁ + δ₂}).map
        (MulAut.conj nw).toMonoidHom := Subgroup.mem_map.2 ⟨y₀, hy₀S, by simp [MulAut.conj_apply]⟩
    rw [htransport _ hrootsδ, himg2] at hmem
    exact hmem
  have hcommY : ∀ a : Fin TwistTag.E6.tag.rank → Lˣ, rootChar a β₁ = 1 → rootChar a β₂ = 1 →
      rootDiagUnit TwistTag.E6.tag a * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) =
        (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a := by
    intro a hχ₁ hχ₂
    have hχγ : rootChar a (β₁ + β₂) = 1 := by rw [rootChar_add, hχ₁, hχ₂, mul_one]
    have hχγ' : rootChar a (-(β₁ + β₂)) = 1 := by
      have := rootChar_sub a 0 (β₁ + β₂)
      rw [zero_sub, rootChar_zero, hχγ] at this
      simpa using this
    have hSγ : ∀ α ∈ ({β₁ + β₂, -(β₁ + β₂)} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1 := by
      intro α hα
      rcases hα with h | h
      · rw [h]; exact ⟨hβ₁₂, hχγ⟩
      · rw [h]; exact ⟨IsRoot.neg hβ₁₂, hχγ'⟩
    have hS3 : ∀ α ∈ ({β₁, β₂, β₁ + β₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1 := by
      intro α hα
      rcases hα with h | h | h
      · rw [h]; exact ⟨hβ₁, hχ₁⟩
      · rw [h]; exact ⟨hβ₂, hχ₂⟩
      · rw [h]; exact ⟨hβ₁₂, hχγ⟩
    have hck : Commute (rootDiagUnit TwistTag.E6.tag a) (nw * κ * nw⁻¹) :=
      (Subgroup.mem_centralizer_iff.1 ((torus_sup_rootSpan_le_centralizer_rootDiagUnit (L := L) a
        (S := {β₁ + β₂, -(β₁ + β₂)}) hSγ) hk)) _ rfl
    have hcy : Commute (rootDiagUnit TwistTag.E6.tag a) (nw * y₀ * nw⁻¹) :=
      (Subgroup.mem_centralizer_iff.1 ((rootSpan_le_centralizer_rootDiagUnit (L := L) a
        (S := {β₁, β₂, β₁ + β₂}) hS3) hy₁)) _ rfl
    have := ((hck.mul_right hcy).mul_right hck.inv_right).eq
    calc rootDiagUnit TwistTag.E6.tag a * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) =
        rootDiagUnit TwistTag.E6.tag a * (nw * κ * nw⁻¹ * (nw * y₀ * nw⁻¹) *
          (nw * κ * nw⁻¹)⁻¹) := by group
      _ = (nw * κ * nw⁻¹ * (nw * y₀ * nw⁻¹) * (nw * κ * nw⁻¹)⁻¹) *
          rootDiagUnit TwistTag.E6.tag a := this
      _ = (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a := by group
  have hshat' : shat = g0 * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * g0⁻¹ := by
    rw [hshat, hxhat, hh]
    group
  have hxcomm : ∀ e ∈ P, e * xG = xG * e := by
    intro e he
    obtain ⟨a, ha, hχ₁, hχ₂⟩ := hPchar e he
    have ha' : rootDiagUnit TwistTag.E6.tag a =
        g0⁻¹ * baseChangeGL ι (e : ModGL TwistTag.E6.tag K) * g0 := ha
    have hed : baseChangeGL ι (e : ModGL TwistTag.E6.tag K) =
        g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ := by
      rw [ha']
      group
    have hc := hcommY a hχ₁ hχ₂
    apply Subtype.ext
    apply baseChangeGL_injective ι
    simp only [Subgroup.coe_mul, map_mul, hxGc]
    rw [hed, hxι', hshat']
    calc g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ * (g0 * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * g0⁻¹) =
        g0 * (rootDiagUnit TwistTag.E6.tag a * (nw * κ * y₀ * κ⁻¹ * nw⁻¹)) * g0⁻¹ := by group
      _ = g0 * ((nw * κ * y₀ * κ⁻¹ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a) * g0⁻¹ := by
        rw [hc]
      _ = g0 * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * g0⁻¹ *
          (g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹) := by group
  have hxX : xG ∉ (TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom := by
    intro hxmem
    rw [mem_map_conj_iff] at hxmem
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (show ((U₃⁻¹ * xG * U₃ : twistedE6RootGroup K σ) :
      ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot from hxmem)
    have h1 : baseChangeGL ι ((U₃⁻¹ * xG * U₃ : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag L e6HighestRoot := by
      rw [← hc, baseChangeGL_pinnedX]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
    rw [hconjι] at h1
    have h2 : xhat ∈ rootSubgroup TwistTag.E6.tag L e6HighestRoot :=
      (Subgroup.mem_normalizer_iff.1
        (torusGroup_le_normalizer_rootSubgroup isRoot_e6HighestRoot ht₃) xhat).2 h1
    have hzNU := torus_sup_rootSpan_levi_le_normalizer_rootSubgroup (L := L) hz
    have h3 : z * xhat * z⁻¹ ∈ rootSubgroup TwistTag.E6.tag L e6HighestRoot :=
      (Subgroup.mem_normalizer_iff.1 hzNU xhat).1 h2
    have h4 : z * xhat * z⁻¹ = y₀ := by rw [hxhat]; group
    rw [h4] at h3
    apply hy₀U
    rw [hsum]
    exact h3
  have hrxG : ∃ n : ℕ, xG ^ (ringChar K) ^ n = 1 := by
    have hQp : IsPGroup (ringChar K)
        (twE6LongRootRadical ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)) :=
      (CFSG.pCore_isPGroup (p := ringChar K) (G := twE6LongRootParabolic
        ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom))).map
        (twE6LongRootParabolic _).subtype
    obtain ⟨n, hn⟩ := hQp ⟨xG, hxQ⟩
    exact ⟨n, by
      have h1 : ((⟨xG, hxQ⟩ : twE6LongRootRadical
          ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)) ^ (ringChar K ^ n) :
          twistedE6RootGroup K σ) = 1 := congrArg Subtype.val hn
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1⟩
  refine ⟨Subgroup.zpowers xG, (Subgroup.zpowers_le).2 hxQ, (Subgroup.zpowers_le).2 ?_, ?_⟩
  · exact Subgroup.subset_closure ⟨Subgroup.mem_top _, hrxG, P, hPE, hPidx, hxcomm⟩
  · intro hle
    exact hxX (hle (Subgroup.mem_zpowers xG))

theorem exists_radical_of_negDatum (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (hreg : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      ¬ TwKills K σ E₀ g0 α) :
    ∃ θ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag θ ∧
      (∀ x ∈ E₀, ∀ c : (AlgebraicClosure K)ˣ,
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
            g0 * rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform θ (Pi.single i 1)) * g0⁻¹ →
          x = 1) ∧
      ∃ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm ∧
        (∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
            (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ, -θ}).map
              (MulAut.conj g0).toMonoidHom) ∧
        ∃ R : Subgroup (twistedE6RootGroup K σ), R ≤ twE6LongRootRadical X ∧
          R ≤ hyperClosure 3 ⊤ E₀ ∧ ¬ R ≤ X := by
  obtain ⟨θ, hθ, hcoroot, X, Xm, hpair, hS, R, hRQ, hRH, hRX⟩ :=
    exists_radical_of_negDatum_r q K σ hK hσ hr E₀ hE₀ hcard Fr hFr v g0 hg0C hg0 hT hv hreg
  have hle : Subgroup.closure (hyperRSet ⊤ E₀ (ringChar K) 3) ≤ hyperClosure 3 ⊤ E₀ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨-, -, B, hBE, hBi, hxB⟩
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, B, hBE, hBi,
      fun b hb => Subgroup.mem_centralizer_iff.1 hxB b hb⟩
  exact ⟨θ, hθ, hcoroot, X, Xm, hpair, hS, R, hRQ, hRH.trans hle, hRX⟩

end NegDatum

end CFSG.LieType.SeitzGeneration.ExcWideThree
