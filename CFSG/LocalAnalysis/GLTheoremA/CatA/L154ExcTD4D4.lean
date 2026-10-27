module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Exact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Par
public import CFSG.Assembly.E6FourFineComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4C

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix MatrixGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)


set_option maxRecDepth 100000

section Square


theorem l154td4_theta_mem {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ (d4Nodes τ)) :
    v⁻¹ • S.ρ (v • α) ∈ parabolicRoots τ (d4Nodes τ) := by
  have hmem : v • α ∈ componentRoots (rootCharHom a) i := by
    rw [hΨ]
    exact ⟨α, hα, rfl⟩
  have h2 := hρ _ hmem
  rw [hΨ] at h2
  obtain ⟨β, hβ, hβe⟩ := h2
  rw [← hβe, inv_smul_smul]
  exact hβ

end Square

section Untwisted

variable
  {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem l154td4_d4_untw
    (hsearch : D4BaseSearch Tag.E6) (hL2 : D4SwapLayer Tag.E6) (hR2 : D4SwapLayerFine Tag.E6)
    (S : LangSetup Tag.E6 L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup Tag.E6}
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (h2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f) :
    OmegaMinus8Fine ℓ f (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin hρ
  rw [hs, Function.iterate_one] at h1
  rw [hs] at h2
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
  obtain ⟨u'', hu'', hu''act⟩ := l154td4_exists_inner_sq hΨ
    (σ := (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) (by simpa using h2)
  have hsq : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • (v⁻¹ * w * v) • α = u'' • α := by
    intro α hα
    have hvα : v • α ∈ Ψ := hΨ ▸ ⟨α, hα, rfl⟩
    have hwvα : w • v • α = S.ρ (v • α) := (hρw (v • α) hvα.1.1).symm
    have hww : w • w • v • α = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) := by
      rw [hwvα]
      exact (hρw (S.ρ (v • α)) (hρ (v • α) hvα).1.1).symm
    rw [← hu''act α hα, ← hww]
    calc (v⁻¹ * w * v) • (v⁻¹ * w * v) • α
        = v⁻¹ • w • (v • (v⁻¹ • (w • v • α))) := by simp only [mul_smul]
      _ = v⁻¹ • w • w • v • α := by rw [smul_inv_smul]
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
  let fw : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := fun x => (v⁻¹ * w * v) • x
      map_zero' := smul_zero _
      map_add' := fun x y => smul_add _ x y }
  have hu' := l154td4_parabolic_le hu
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
    · exact (l154td4_not_inner_sq_leafThreeCycle h12 h24 h14 hv1 hv2 hv4 hu' hu'' fw hact
        hsq).elim
    · exact (l154td4_not_inner_sq_leafThreeCycle h14 h24.symm h12 hv1 hv4 hv2 hu' hu'' fw hact
        hsq).elim
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end Untwisted

section TwSwap

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem l154td4_twisted_swap_layer (hf : 1 ≤ f)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    OmegaMinus8Fine ℓ f
      (rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' : ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun k hk => by
    have := hact _ (single_mem_parabolicRoots hk)
    rw [permLattice_single (Equiv.swap i j)] at this
    exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap13_fine (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    exact fine_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap03_fine (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    exact fine_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap01_fine (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    exact fine_layer_swap hstd h₂ hRL hh hlang rfl

end TwSwap

section TwLayer

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem l154td4_twE6_layer (hf : 1 ≤ f) {n : ModGL Tag.E6 L}
    (hn : n ∈ monomialSubgroup Tag.E6 L) {u : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {π : Equiv.Perm (Fin Tag.E6.rank)} (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1)
    (hn3 : π ≠ List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∧
      π ≠ List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2])
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      OmegaMinus8Fine ℓ f (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hE6 := e6FixDNAll_proved
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  rcases hleaf with hc | hc | hc | hc | hc | hc
  · exact absurd hc hπ1
  · rw [hc] at hact
    exact ⟨(twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2,
      l154td4_twisted_swap_layer hf h12 hv1 hv2 hn hu hact⟩
  · rw [hc] at hact
    exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
      l154td4_twisted_swap_layer hf h14 hv1 hv4 hn hu hact⟩
  · rw [hc] at hact
    exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
      l154td4_twisted_swap_layer hf h24 hv2 hv4 hn hu hact⟩
  · exact absurd hc hn3.1
  · exact absurd hc hn3.2

end TwLayer

section TwMain

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem l154td4_tw_not_threeCycle (S : LangSetup .E6 L p) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]))
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α) :
    πJ ≠ List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∧
      πJ ≠ List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2] := by
  obtain ⟨u'', hu'', hu''act⟩ := l154td4_exists_inner_sq hΨ
    (σ := (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) h2
  let ft : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := fun x => u • permLattice πJ x
      map_zero' := by simp [permLattice]
      map_add' := fun x y => by
        rw [← smul_add]
        rfl }
  have hft : ∀ α, ft α = u • permLattice πJ α := fun α => rfl
  have hsq : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), ft (ft α) = u'' • α := by
    intro α hα
    have hmem : ft α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
      rw [hft, ← hθ' α hα]
      exact l154td4_theta_mem S i v hΨ hρ hα
    calc ft (ft α) = v⁻¹ • S.ρ (v • ft α) := (hθ' _ hmem).symm
      _ = v⁻¹ • S.ρ (v • (v⁻¹ • S.ρ (v • α))) := by rw [hft α, hθ' α hα]
      _ = v⁻¹ • (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) := by rw [smul_inv_smul]; rfl
      _ = u'' • α := hu''act α hα
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hu' := l154td4_parabolic_le hu
  exact ⟨fun hc => l154td4_not_inner_sq_leafThreeCycle h12 h24 h14 hv1 hv2 hv4 hu' hu'' ft
      (fun α _ => by rw [hft, hc]) hsq,
    fun hc => l154td4_not_inner_sq_leafThreeCycle h14 h24.symm h12 hv1 hv4 hv2 hu' hu'' ft
      (fun α _ => by rw [hft, hc]) hsq⟩

end TwMain

section TwComponent


theorem l154td4_d4_tw {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (h2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      OmegaMinus8Fine (ringChar L) f (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨w, hn, hρw⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq S hS
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  obtain ⟨u, hu, w₀, hw₀, πJ, hleaf, hlin, hθ'⟩ := l154r4_tw_action S hρw i v hΨ hρ
  have hπ1 := l154r4_tw_pi_ne_one S i v hΨ hnin hu hθ'
  have hn3 := l154td4_tw_not_threeCycle S i v hΨ hρ h2 hu hθ'
  obtain ⟨n', hn', hact, g, heq⟩ := l154r4_tw_layer_eq S hFr' hΦ' hn i v hΨ hw₀ hlin
  have hlayer := l154td4_twE6_layer (ℓ := ℓ) hf hn' hu hleaf hπ1 hn3 hact
  set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
    twistedFixedPoints (n' * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
  have e : Q ≃* Q.map (MulAut.conj g).toMonoidHom :=
    Q.equivMapOfInjective _ (MulAut.conj g).injective
  have hqs : CFSG.IsQuasisimple
      ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [heq]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1
  refine ⟨f, by rw [ringChar.eq L ℓ, hq], ?_⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs, heq, ringChar.eq L ℓ]
  exact OmegaMinus8Fine.map_conj (MulAut.conj g) hlayer.2

end TwComponent

section Final

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_d4_E6 (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (h2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  have hL2 : ringChar L = 2 := ringChar.eq L 2
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
    (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin hρ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have h := l154td4_d4_untw d4Base_E6 (d4SwapLayer_E6 e6FixDNAll_proved) d4SwapLayerFine_E6 S
      hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin h2 hf hq
    exact l154td4_exact_of_lieModel ((ringChar.eq L ℓ).symm.trans hL2) (by decide) h
  · rw [hs, Function.iterate_one] at hnin
    rw [hs] at h2
    obtain ⟨f, -, h⟩ := l154td4_d4_tw S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin (by simpa using h2)
    rw [hL2] at h
    exact l154td4_exact_of_lieModel rfl (by decide) h

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
