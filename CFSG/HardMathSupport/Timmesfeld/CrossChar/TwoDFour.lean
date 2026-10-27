module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFourLayer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)


set_option linter.unusedSectionVars false

theorem twoD_kind_unpack {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i : KernelComponent χ}
    (hk : twistKind ρ χ i = .twoD) :
    ¬ twistInner (componentRoots χ i)
        ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) ∧
      4 ≤ compRank (componentRoots χ i) ∧ (componentRoots χ i).ncard =
        2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1) := by
  unfold twistKind at hk
  split_ifs at hk with h1 h2 h3
  exact ⟨h1, h3⟩

section Layer


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootSpan_inf_model_quasisimple_d4_swap (hL : D4SwapLayer τ) (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α) :
    Finite ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple
        ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  LangTorus.rootSpan_inf_model_quasisimple_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact


theorem isQuasisimple_rationalComponent_of_d4_outer [E6Sub τ] (hsearch : D4BaseSearch τ)
    (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
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
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2
  exact isQuasisimple_rationalComponent_of_layer S i hρ hlayer

end Layer

section Twisted


theorem isQuasisimple_rationalComponent_of_d4_twE6 (hE6 : E6FixDNAll) {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  isQuasisimple_rationalComponent_of_d4_twE6_of_layer S hS i v hΨ hρ hnin
    fun ℓ f _ _ hf n hn u hu π hleaf hπ1 _ hact => by
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
        exact (twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2

theorem isQuasisimple_rationalComponent_rank_four_T_of_prime (hE6 : E6FixDNAll) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
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
      exact isQuasisimple_rationalComponent_of_d4_outer d4Base_E6 d4TrialityLayer_E6
        (d4SwapLayer_E6 hE6) S hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v
        hv hρ hnin
    · rw [hs, Function.iterate_one] at hnin
      exact isQuasisimple_rationalComponent_of_d4_twE6 hE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact isQuasisimple_rationalComponent_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact isQuasisimple_rationalComponent_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin

theorem isQuasisimple_rationalComponent_rank_four_T (hE6 : E6FixDNAll) {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  isQuasisimple_rationalComponent_rank_four_T_of_prime hE6 S S.hp S.natCast_ne_zero hT hTp ha1 i
    hr hc hnin

theorem isQuasisimple_rationalComponent_rank_four (hE6 : E6FixDNAll) {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (ha : rootDiagUnit τ a ∈ S.E) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  isQuasisimple_rationalComponent_rank_four_T hE6 S (S.E_le ha).1 (S.E_exp _ ha) ha1 i hr hc hnin

theorem langComponentsQuasisimple_twoD_of_high (hE6 : E6FixDNAll) (h : TwoDHighComponents) :
    LangComponentsQuasisimple .twoD := by
  intro τ L _ _ p S a ha ha1 i hk hbig
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact h τ L p S a ha ha1 i hk h5 hbig
  · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hcard, hr]
    exact isQuasisimple_rationalComponent_rank_four hE6 S ha ha1 i hr hc hnin

theorem langComponentsQuasisimpleT_twoD_of_high (hE6 : E6FixDNAll) (h : TwoDHighComponentsT) :
    LangComponentsQuasisimpleT .twoD := by
  intro τ L _ _ p S a hT hTp ha1 i hk hbig
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact h τ L p S a hT hTp ha1 i hk h5 hbig
  · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hcard, hr]
    exact isQuasisimple_rationalComponent_rank_four_T hE6 S hT hTp ha1 i hr hc hnin

end Twisted

end CFSG.HardMathSupport.Timmesfeld.CrossChar
