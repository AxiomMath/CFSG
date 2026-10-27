module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4A
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

section TwSwap

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem l154r4_twisted_swap_layer (hf : 1 ≤ f)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    L154R4Model ℓ f
      ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
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
  · obtain ⟨n₂, h₂, -, hRL⟩ := l154r4_exists_fix_swap13_all (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    exact l154r4_model_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := l154r4_exists_fix_swap03_all (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    exact l154r4_model_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := l154r4_exists_fix_swap01_all (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    exact l154r4_model_layer_swap hstd h₂ hRL hh hlang rfl

end TwSwap

section TwTriality

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem l154r4_twisted_triality_layer (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    L154R4Model ℓ f
      ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact l154r4_model_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact l154r4_model_layer_triality hf hstd hh hlang rfl

end TwTriality

section TwLayer

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem l154r4_twE6_layer (hf : 1 ≤ f) {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {π : Equiv.Perm (Fin Tag.E6.rank)} (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1)
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      L154R4Model ℓ f ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
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
      l154r4_twisted_swap_layer hf h12 hv1 hv2 hn hu hact⟩
  · rw [hc] at hact
    exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
      l154r4_twisted_swap_layer hf h14 hv1 hv4 hn hu hact⟩
  · rw [hc] at hact
    exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
      l154r4_twisted_swap_layer hf h24 hv2 hv4 hn hu hact⟩
  · rw [hc] at hact
    exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2,
      l154r4_twisted_triality_layer hf h12 h24 h14 hv1 hv2 hv4 hn hu hact⟩
  · rw [hc] at hact
    exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2,
      l154r4_twisted_triality_layer hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact⟩

end TwLayer

section TwGeom

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem l154r4_tw_sigma_par : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
    permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
  intro α hα
  refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
  exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1


theorem l154r4_tw_theta (S : LangSetup .E6 L p) {w : WeylGroup .E6}
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ) (v : WeylGroup .E6) :
    ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = (v⁻¹ * w * e6WeylTwist v) • permLattice e6Graph α := by
  intro α hα
  rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, mul_smul, mul_smul]

theorem l154r4_tw_mapsJ (S : LangSetup .E6 L p) {w : WeylGroup .E6}
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * e6WeylTwist v) := by
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  intro α hα
  have h1 := l154r4_tw_theta S hρw v (permLattice e6Graph α) (l154r4_tw_sigma_par α hα)
  rw [hσσ] at h1
  rw [← h1]
  exact hθmem _ (l154r4_tw_sigma_par α hα)

theorem l154r4_tw_lin {w₀ : WeylGroup Tag.E6} {π' : Equiv.Perm (Fin Tag.E6.rank)}
    (hw₀π : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π' j) 1) :
    ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • permLattice e6Graph α =
      permLattice (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) α := by
  intro α hα
  have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
    (fun j hj => by rw [one_smul]; exact hw₀π j hj) (l154r4_tw_sigma_par α hα).2
  rw [one_smul] at h1
  rw [h1, permLattice_mul]
  congr 1
  funext k
  simp only [permLattice, Function.comp]
  by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
  · rw [((e6Graph_on_d4 k).1 hk).2.1]
  · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]

theorem l154r4_tw_pi_ne_one (S : LangSetup .E6 L p) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), v⁻¹ • S.ρ (v • α) = u • permLattice πJ α) :
    πJ ≠ 1 := by
  intro h1
  apply hnin
  refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
  rintro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  have h := hθ' α hα
  rw [h1] at h
  calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
    _ = v • (u • α) := by rw [h]; rfl
    _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]


theorem l154r4_tw_action (S : LangSetup .E6 L p) {w : WeylGroup .E6}
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    ∃ u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6), ∃ w₀ : WeylGroup Tag.E6,
      v⁻¹ * w * e6WeylTwist v = u * w₀ ∧ ∃ πJ : Equiv.Perm (Fin Tag.E6.rank), IsD4LeafPerm πJ ∧
        (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
          w₀ • permLattice e6Graph α = permLattice πJ α) ∧
        ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ :=
    exists_d4_action d4Base_E6 (l154r4_tw_mapsJ S hρw i v hΨ hρ)
  refine ⟨u, hu, w₀, hw₀, π' * Equiv.swap (e6Idx 2) (e6Idx 4), isD4LeafPerm_mul_swap hπ',
    l154r4_tw_lin hw₀π, fun α hα => ?_⟩
  rw [l154r4_tw_theta S hρw v α hα, hw₀, mul_smul, l154r4_tw_lin hw₀π α hα]

end TwGeom

section TwModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem l154r4_tw_model_eq (S : LangSetup .E6 L p) {Fr : L →+* L} {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hFr' : Fr = iterateFrobenius L ℓ f)
    (hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup .E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (Ψ : Set (Fin Tag.E6.rank → ℤ)) :
    rootSpan Tag.E6 L Ψ ⊓ S.D.model = rootSpan Tag.E6 L Ψ ⊓
      twistedFixedPoints (canonicalRep (coxeterSystem Tag.E6) L w * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, -, hxF⟩
    refine ⟨hx, ?_⟩
    have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
    rw [hn, hΦ', hFr'] at hxF'
    change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
      (nw * e6Diagram L)⁻¹ = x
    calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
            Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
          group
      _ = x := hxF'
  · rintro ⟨hx, hxF⟩
    refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
    have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x := hxF
    change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
    rw [hn, hΦ', hFr']
    calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
            Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
          group
      _ = x := hxF'

theorem l154r4_tw_layer_eq (S : LangSetup .E6 L p) {Fr : L →+* L} {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hFr' : Fr = iterateFrobenius L ℓ f)
    (hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup .E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    {u w₀ : WeylGroup Tag.E6} (hw₀ : v⁻¹ * w * e6WeylTwist v = u * w₀)
    {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    (hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α) :
    ∃ (n' : ModGL Tag.E6 L) (hn' : n' ∈ monomialSubgroup Tag.E6 L),
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n', hn'⟩ • permLattice e6Graph α = u • permLattice πJ α) ∧
      ∃ g : ModGL Tag.E6 L,
        rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
          (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
            twistedFixedPoints (n' * e6Diagram L)
              (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).map
            (MulAut.conj g).toMonoidHom := by
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = v⁻¹ * w * e6WeylTwist v := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  refine ⟨nv⁻¹ * nw * nδ, hn'M, fun α hα => ?_, nv, ?_⟩
  · rw [hπn', hw₀, mul_smul, hlin α hα]
  · rw [l154r4_tw_model_eq S hFr' hΦ' hn, hΨ,
      rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]

end TwModel

section TwComponent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers


theorem l154r4_rationalComponent_of_d4_twE6 {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      L154R4Model (ringChar L) f ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
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
  obtain ⟨n', hn', hact, g, heq⟩ := l154r4_tw_layer_eq S hFr' hΦ' hn i v hΨ hw₀ hlin
  have hlayer := l154r4_twE6_layer (ℓ := ℓ) hf hn' hu hleaf hπ1 hact
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
  exact l154r4_model_map_conj (MulAut.conj g) hlayer.2

end TwComponent

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
