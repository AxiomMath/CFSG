module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Layers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CompsPD4Layers

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPD4Class

section Transport

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootSpan_inf_model_rationalLieType_d4_of_layer (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      RationalLieType ℓ (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    RationalLieType (ringChar L)
      (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (d4Nodes τ), IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ, hFr']
      exact hxF
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots, hring]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hP := hlayer ℓ f hf hq (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact rationalLieType_map_conj (MulAut.conj nv) hP

variable {Fr : L →+* L}

theorem rootSpan_inf_model_rationalLieType_d4_swap (hL : D4SwapLayerRL τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α)
    (hq : ringChar L = 2 ∨ 5 ≤ S.D.q) :
    RationalLieType (ringChar L)
      (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_rationalLieType_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf hqf n hn hC hex => hL L ℓ f hf (by
      have hring : ringChar L = ℓ := ringChar.eq L ℓ
      rw [← hqf, ← hring]
      exact hq) i j hij hi hj n hn hC hex _ rfl) hact

theorem rootSpan_inf_model_rationalLieType_d4 (hL : D4TrialityLayerRL τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {a b c : Fin τ.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    RationalLieType (ringChar L)
      (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_rationalLieType_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC hex _ rfl)
    hact

end Transport

section Component

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rationalLieType_rationalComponent_of_d4_outer [E6Sub τ] (hsearch : D4BaseSearch τ)
    (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ) (hR3 : D4TrialityLayerRL τ)
    (hR2 : D4SwapLayerRL τ) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hq : ringChar L = 2 ∨ 5 ≤ S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
      RationalLieType (ringChar L) (rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        CompsPD4Class.rootSpan_inf_model_rationalLieType_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2
          hact hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        CompsPD4Class.rootSpan_inf_model_rationalLieType_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4
          hact hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        CompsPD4Class.rootSpan_inf_model_rationalLieType_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4
          hact hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2, CompsPD4Class.rootSpan_inf_model_rationalLieType_d4 hR3 S hFr hΦ hn v hu h12 h24
          h14 hv1 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2, CompsPD4Class.rootSpan_inf_model_rationalLieType_d4 hR3 S hFr hΦ hn v hu h14
          h24.symm h12 hv1 hv4 hv2 hact⟩
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end Component

end CompsPD4Class

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
