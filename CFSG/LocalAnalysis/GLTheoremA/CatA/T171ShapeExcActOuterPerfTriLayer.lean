module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KD4L
open CFSG.RankThree.PartOne.KE (twistedFixedPoints d4Nodes D4TrialityLayer)


variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem excTri_layer_untw (hsearch : D4BaseSearch τ) (hL : D4TrialityLayer τ)
    (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  rw [componentOrbitLength_eq_one hfin hρ, mul_one] at h2
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
  have hπ2 : π * π ≠ 1 := by
    intro hππ
    apply h2
    have hu' : w₀ * u * w₀⁻¹ ∈ parabolicWeylGroup τ (d4Nodes τ) := by
      have hle : (parabolicWeylGroup τ (d4Nodes τ)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup τ (d4Nodes τ) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π j, hπ.mem_d4Set hj, ?_⟩
        change simple τ (π j) = w₀ * simple τ j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨u, hu, rfl⟩
    refine ⟨v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹,
      hΨ ▸ conj_mem_closure_rootReflection v (mul_mem hu hu'), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    have hγr : IsRoot τ (v • α) := hγ.1.1
    have hw2 : w₀ • w₀ • α = α := by
      have hα' : w₀ • α ∈ parabolicRoots τ (d4Nodes τ) := by
        rw [hlin0 α hα]
        refine ⟨?_, fun k hk => ?_⟩
        · rw [← hlin0 α hα]
          exact IsRoot.smul hα.1 w₀
        · have hk' : π.symm k ∉ d4Nodes τ := fun h => hk (by
            have h' := hπ.mem_d4Set (show π.symm k ∈ d4Set τ from h)
            rw [Equiv.apply_symm_apply] at h'
            exact h')
          exact hα.2 _ hk'
      rw [hlin0 _ hα', hlin0 α hα, ← permLattice_mul, hππ]
      rfl
    rw [Function.iterate_succ_apply, Function.iterate_one, hρw _ hγr,
      hρw _ ((isRoot_smul_iff w).2 hγr)]
    calc w • w • v • α = v • ((v⁻¹ * w * v) • (v⁻¹ * w * v) • α) := by
          simp only [mul_smul, smul_inv_smul]
      _ = v • (u • w₀ • u • w₀ • α) := by rw [hw₀]; simp only [mul_smul]
      _ = v • (u • (w₀ * u * w₀⁻¹) • w₀ • w₀ • α) := by simp only [mul_smul, inv_smul_smul]
      _ = (v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹) • v • α := by
          rw [hw2]
          simp only [mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ.eq_cycle hπ1 hπ2 with rfl | rfl
    · exact (rootSpan_inf_model_quasisimple_d4 hL S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2
  exact hlayer

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
