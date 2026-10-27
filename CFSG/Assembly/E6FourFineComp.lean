module

public import CFSG.Assembly.E6FourFineLayer
import CFSG.Assembly.E6FourFineTriality
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix MatrixGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CompsPD4Layers

set_option maxRecDepth 100000

namespace E6FourFine

section Transport

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {Fr : L →+* L}

theorem fine_rootSpan_inf_model_d4_of_layer
    (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f)
    (hlayer : ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      OmegaMinus8Fine ℓ f (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    OmegaMinus8Fine ℓ f
      (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
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
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots]
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
  have hP := hlayer (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact OmegaMinus8Fine.map_conj (MulAut.conj nv) hP

theorem fine_rootSpan_inf_model_d4_swap
    (hL : D4SwapLayerFine τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α)
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f) :
    OmegaMinus8Fine ℓ f
      (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  fine_rootSpan_inf_model_d4_of_layer S hFr hΦ hn v hu hf hq
    (fun n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact

end Transport

section Component

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem fine_rationalComponent_of_d4_outer
    (hsearch : D4BaseSearch Tag.E6)
    (hL2 : D4SwapLayer Tag.E6) (hR2 : D4SwapLayerFine Tag.E6) (S : LangSetup Tag.E6 L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ)
    (hρ2 : ∀ γ, IsRoot Tag.E6 γ → S.ρ (S.ρ γ) = γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f) :
    OmegaMinus8Fine ℓ f (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • α = permLattice π α :=
    fun α hα => by
      have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set Tag.E6)
        (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
      rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hsq : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • (v⁻¹ * w * v) • α = α := by
    intro α hα
    have hvα : v • α ∈ Ψ := hΨ ▸ ⟨α, hα, rfl⟩
    have hwvα : w • v • α = S.ρ (v • α) := (hρw (v • α) hvα.1.1).symm
    have hww : w • w • v • α = v • α := by
      rw [hwvα, ← hρw (S.ρ (v • α)) (hρ (v • α) hvα).1.1, hρ2 (v • α) hvα.1.1]
    calc (v⁻¹ * w * v) • (v⁻¹ * w * v) • α
        = v⁻¹ • w • (v • (v⁻¹ • (w • v • α))) := by simp only [mul_smul]
      _ = v⁻¹ • w • w • v • α := by rw [smul_inv_smul]
      _ = α := by rw [hww, inv_smul_smul]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ :
      γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) ∧
      OmegaMinus8Fine ℓ f (rootSpan Tag.E6 L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        fine_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact hf hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        fine_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact hf hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        fine_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact hf hq⟩
    · exact absurd (not_involution_of_leaf_threeCycle h12 h24 h14 hv1 hv2 hv4 hu hact hsq) id
    · exact absurd (not_involution_of_leaf_threeCycle h14 h24.symm h12 hv1 hv4 hv2 hu hact hsq) id
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end Component

end E6FourFine

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
