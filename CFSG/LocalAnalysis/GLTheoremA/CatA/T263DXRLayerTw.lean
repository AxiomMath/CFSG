module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFourLayer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints d4Nodes)



section Layer

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

private theorem twE6_swap_hact {i j : Fin TwistTag.E6.tag.rank}
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag}
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
  intro k hk
  have := hact _ (single_mem_parabolicRoots hk)
  rw [permLattice_single (Equiv.swap i j)] at this
  exact this

theorem twisted_swap_layer_commutant (hE6 : E6FixDNAll) (hf : 1 ≤ f)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    Finite ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan TwistTag.E6.tag L
          (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ y ∈ torusGroup TwistTag.E6.tag L ⊔
          subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag),
        (∀ u ∈ rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
          twistedFixedPoints (n * diagramMap TwistTag.E6 L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), y * u = u * y) →
        y ∈ torusGroup TwistTag.E6.tag L ∧
          y ∈ Subgroup.centralizer
            (subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag) :
              Set (ModGL TwistTag.E6.tag L))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' := twE6_swap_hact hn hact
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, hfix⟩ := exists_fix_swap13 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    obtain ⟨hfin, hqs, hcl, -⟩ := layer_of_swap hstd h₂ (by decide) hfix hh hlang rfl
    exact ⟨hfin, hqs, hcl⟩
  · obtain ⟨n₂, h₂, hfix⟩ := exists_fix_swap03 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    obtain ⟨hfin, hqs, hcl, -⟩ := layer_of_swap hstd h₂ (by decide) hfix hh hlang rfl
    exact ⟨hfin, hqs, hcl⟩
  · obtain ⟨n₂, h₂, hfix⟩ := exists_fix_swap01 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    obtain ⟨hfin, hqs, hcl, -⟩ := layer_of_swap hstd h₂ (by decide) hfix hh hlang rfl
    exact ⟨hfin, hqs, hcl⟩

theorem twisted_swap_layer_E6_commutant (hE6 : E6FixDNAll) (hf : 1 ≤ f)
    {i j : Fin Tag.E6.rank} (hij : i ≠ j)
    (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes _),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α =
        u • permLattice (Equiv.swap i j) α) :
    Finite ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6),
        (∀ u ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
          twistedFixedPoints (n * e6Diagram L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), y * u = u * y) →
        y ∈ torusGroup Tag.E6 L ∧
          y ∈ Subgroup.centralizer
            (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L))) :=
  twisted_swap_layer_commutant hE6 hf hij hi hj hn hu hact

theorem twisted_triality_layer_commutant (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    Finite ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan TwistTag.E6.tag L
          (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ y ∈ torusGroup TwistTag.E6.tag L ⊔
          subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag),
        (∀ u ∈ rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
          twistedFixedPoints (n * diagramMap TwistTag.E6 L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), y * u = u * y) →
        y ∈ torusGroup TwistTag.E6.tag L ∧
          y ∈ Subgroup.centralizer
            (subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag) :
              Set (ModGL TwistTag.E6.tag L))) := by
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
    obtain ⟨hfin, hqs, hcl, -⟩ := layer_of_standard hf hstd hh hlang rfl
    exact ⟨hfin, hqs, hcl⟩
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    obtain ⟨hfin, hqs, hcl, -⟩ := layer_of_standard hf hstd hh hlang rfl
    exact ⟨hfin, hqs, hcl⟩

theorem twisted_triality_layer_E6_commutant (hf : 1 ≤ f) {a b c : Fin Tag.E6.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes _),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    Finite ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6),
        (∀ u ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
          twistedFixedPoints (n * e6Diagram L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), y * u = u * y) →
        y ∈ torusGroup Tag.E6 L ∧
          y ∈ Subgroup.centralizer
            (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L))) :=
  twisted_triality_layer_commutant hf hab hbc hac ha hb hc hn hu hact

end Layer

section Transport

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private theorem twE6_rho_eq_smul {S : LangSetup .E6 L p} {Fr : L →+* L}
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hFrs : Function.Surjective Fr) :
    ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
  intro γ hγ
  have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
      Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
      (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
    rw [hΦ, hn]
  have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
  have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
      rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
    rw [← S.frob.map_rootSubgroup γ hγ, hst]
    exact h2
  have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
    IsRoot.smul (hγ.permLattice e6Graph_cartan) w
  exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3

private theorem twE6_sigma :
    (∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x) ∧
      ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
  constructor
  · intro x
    rw [← permLattice_mul, e6Graph_mul_self]
    rfl
  · intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1

private theorem twE6_rootAction {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {v : WeylGroup .E6} {w w' : WeylGroup Tag.E6}
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hw' : w' = v⁻¹ * w * e6WeylTwist v)
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ)
    (hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x)
    (hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α) ∧
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ∧
      MapsJ Tag.E6 (d4Set Tag.E6) w' := by
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
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
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  exact ⟨hθ, hθmem, hmaps⟩

private theorem twE6_d4Action {S : LangSetup .E6 L p} {v : WeylGroup .E6} {w' : WeylGroup Tag.E6}
    (hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w')
    (hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α)
    (hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    ∃ (u : WeylGroup Tag.E6) (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
      (w₀ : WeylGroup Tag.E6) (hw₀ : w' = u * w₀)
      (π' : Equiv.Perm (Fin Tag.E6.rank)) (hπ' : IsD4LeafPerm π')
      (hw₀π : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π' j) 1)
      (πJ : Equiv.Perm (Fin Tag.E6.rank)) (hπJ : πJ = π' * Equiv.swap (e6Idx 2) (e6Idx 4))
      (hπJleaf : IsD4LeafPerm πJ)
      (hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        w₀ • permLattice e6Graph α = permLattice πJ α)
      (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        v⁻¹ • S.ρ (v • α) = u • permLattice πJ α)
      (huJ : MapsJ Tag.E6 (d4Set Tag.E6) u),
      ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) α ∈
        parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  exact ⟨u, hu, w₀, hw₀, π', hπ', hw₀π, π' * Equiv.swap (e6Idx 2) (e6Idx 4), rfl,
    isD4LeafPerm_mul_swap hπ', hlin, hθ', huJ, hπJpar⟩

private theorem twE6_pi_ne_one {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {v : WeylGroup .E6} {u : WeylGroup Tag.E6}
    {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α) :
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

private theorem twE6_twist_mem {u w₀ : WeylGroup Tag.E6} {π' : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ' : IsD4LeafPerm π') (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    (hw₀π : ∀ j ∈ d4Set Tag.E6,
      w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π' j) 1) :
    u * (w₀ * e6WeylTwist u * w₀⁻¹) ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
  have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
        parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2,
        (e6WeylTwist_simple j).symm⟩
    exact hle ⟨u, hu, rfl⟩
  have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
        parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
      change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
      rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
    exact hle ⟨e6WeylTwist u, hδu, rfl⟩
  exact mul_mem hu hconj

private theorem twE6_pi_sq_ne_one {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {v : WeylGroup .E6} {u w₀ : WeylGroup Tag.E6}
    {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hu₂ : u * (w₀ * e6WeylTwist u * w₀⁻¹) ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    (hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α)
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α)
    (hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (huJ : MapsJ Tag.E6 (d4Set Tag.E6) u)
    (hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
      πJ * πJ ≠ 1 := by
  intro hnin2 h2
  apply hnin2
  set u₂ := u * (w₀ * e6WeylTwist u * w₀⁻¹) with hu₂def
  have hu₂' : u₂ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by rwa [hu₂def]
  refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu₂', ?_⟩
  rintro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), permLattice πJ (u • x) =
      (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
    intro x hx
    rw [← hlin _ (huJ x hx), ← hlin x hx, ← e6WeylTwist_smul u x, mul_smul, mul_smul,
      inv_smul_smul]
  set β := u • permLattice πJ α with hβ
  have hβJ : β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    rw [hβ, ← hθ' α hα]
    exact hθmem α hα
  have e1 : S.ρ (v • α) = v • β := by rw [hβ, ← hθ' α hα, smul_inv_smul]
  have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by rw [← hθ' β hβJ, smul_inv_smul]
  have e3 : permLattice πJ (permLattice πJ α) = α := by
    rw [← permLattice_mul, h2]
    rfl
  calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
    _ = v • (u • permLattice πJ β) := by rw [e1, e2]
    _ = v • (u₂ • α) := by
        rw [hβ, hpx _ (hπJpar α hα), e3, hu₂def, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
    _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]

private theorem twE6_model_eq {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {v : WeylGroup .E6} {Fr : L →+* L}
    {w : WeylGroup Tag.E6}
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hFr : Fr = iterateFrobenius L ℓ f) :
    rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (canonicalRep (coxeterSystem Tag.E6) L w * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr] at hxF'
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
      rw [hn, hΦ, hFr]
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  simpa only [hnw] using hmodel

private abbrev TwE6LayerHyp (S : LangSetup .E6 L p) (a : Fin Tag.E6.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L) (u : WeylGroup Tag.E6),
    u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) → ∀ π : Equiv.Perm (Fin Tag.E6.rank),
    IsD4LeafPerm π → π ≠ 1 →
    (¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → π * π ≠ 1) →
    (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) →
    Finite ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6),
        (∀ u ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
          twistedFixedPoints (n * e6Diagram L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), y * u = u * y) →
        y ∈ torusGroup Tag.E6 L ∧
          y ∈ Subgroup.centralizer (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L)))

private theorem twE6_layerConj {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {v : WeylGroup .E6} {w w' : WeylGroup Tag.E6}
    {u w₀ : WeylGroup Tag.E6} {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hw' : w' = v⁻¹ * w * e6WeylTwist v) (hw₀ : w' = u * w₀)
    (hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α)
    (hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (canonicalRep (coxeterSystem Tag.E6) L w * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (nv : ModGL Tag.E6 L), nv = canonicalRep (coxeterSystem Tag.E6) L v ∧
      ∃ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L),
        (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
          weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice πJ α) ∧
        ∃ (Q : Subgroup (ModGL Tag.E6 L)),
          Q = rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
              twistedFixedPoints (n * e6Diagram L)
                (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
            Q.map (MulAut.conj nv).toMonoidHom =
              rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  set n := nv⁻¹ * nw * nδ with hn_def; have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn : n ∈ monomialSubgroup Tag.E6 L := by
    rw [hn_def]; exact mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨n, hn⟩ = w' := by
    have e : (⟨n, hn⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v)), ← hw']
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = n * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep (RingHom.id L) v; rw [hn_def]
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice πJ α := by
    intro α hα; rw [hπn', hw₀, mul_smul, hlin α hα]
  set Q : Subgroup (ModGL Tag.E6 L) := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints (n * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) with hQ
  have hQmap : Q.map (MulAut.conj nv).toMonoidHom =
      rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
  exact ⟨nv, hnv, n, hn, hact, Q, hQ, hQmap⟩

private theorem twE6_layerData {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {u : WeylGroup Tag.E6}
    {πJ : Equiv.Perm (Fin Tag.E6.rank)} {n : ModGL Tag.E6 L}
    {Q : Subgroup (ModGL Tag.E6 L)} {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hn : n ∈ monomialSubgroup Tag.E6 L)
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice πJ α)
    (hQdef : Q = rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints (n * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hlay : TwE6LayerHyp S a i) (hf : 1 ≤ f)
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) (hπJleaf : IsD4LeafPerm πJ)
    (hπ1 : πJ ≠ 1)
    (hπ2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → πJ * πJ ≠ 1) :
    Finite ↥Q ∧ CFSG.IsQuasisimple ↥Q ∧
      (∀ y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6),
        (∀ u ∈ Q, y * u = u * y) → y ∈ torusGroup Tag.E6 L ∧
          y ∈ Subgroup.centralizer
            (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L))) := by
  have hlayer := hlay ℓ f hf n hn u hu πJ hπJleaf hπ1 hπ2 hact
  rw [hQdef]
  exact hlayer

private theorem twE6_mem_of_mem_map {nv : ModGL Tag.E6 L} {S T : Subgroup (ModGL Tag.E6 L)}
    (h : S.map (MulAut.conj nv).toMonoidHom = T) {z : ModGL Tag.E6 L} (hz : z ∈ T) :
    nv⁻¹ * z * nv ∈ S := by
  have hz' : z ∈ S.map (MulAut.conj nv).toMonoidHom := by rw [h]; exact hz
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
  have hy' : nv⁻¹ * z * nv = y := by
    rw [← hyz]
    change nv⁻¹ * (nv * y * nv⁻¹) * nv = y
    group
  rwa [hy']

private theorem twE6_commute_transfer {S : LangSetup .E6 L p} {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {nv : ModGL Tag.E6 L} {Q : Subgroup (ModGL Tag.E6 L)}
    (hmap : (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6))).map
        (MulAut.conj nv).toMonoidHom =
        rootSpan Tag.E6 L (componentRoots (rootCharHom a) i))
    (hQmap : Q.map (MulAut.conj nv).toMonoidHom =
        rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model)
    (hcl : ∀ y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6),
      (∀ u ∈ Q, y * u = u * y) → y ∈ torusGroup Tag.E6 L ∧
        y ∈ Subgroup.centralizer (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L))) :
    ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
      (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model, z * u = u * z) →
      ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g := by
  intro z hz hc
  set y := nv⁻¹ * z * nv with hy
  have hyQ : y ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :=
    twE6_mem_of_mem_map hmap hz
  have hyc : ∀ u ∈ Q, y * u = u * y := by
    intro u hu
    have hu' : nv * u * nv⁻¹ ∈
        rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
      rw [← hQmap]
      exact Subgroup.mem_map_of_mem (MulAut.conj nv).toMonoidHom hu
    have h1 := hc (nv * u * nv⁻¹) hu'
    rw [hy]
    calc (nv⁻¹ * z * nv) * u = nv⁻¹ * (z * (nv * u * nv⁻¹)) * nv := by group
      _ = nv⁻¹ * ((nv * u * nv⁻¹) * z) * nv := by rw [h1]
      _ = u * (nv⁻¹ * z * nv) := by group
  have hySup : y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6) :=
    Subgroup.mem_sup_right (by rwa [subsystemGroup_eq_rootSpan])
  have hclY := hcl y hySup hyc
  intro g hg
  have hgQ : nv⁻¹ * g * nv ∈ subsystemGroup Tag.E6 L (d4Set Tag.E6) := by
    rw [subsystemGroup_eq_rootSpan]
    exact twE6_mem_of_mem_map hmap hg
  have h2 := (Subgroup.mem_centralizer_iff.1 hclY.2 (nv⁻¹ * g * nv) hgQ).symm
  rw [hy] at h2
  calc z * g = nv * ((nv⁻¹ * z * nv) * (nv⁻¹ * g * nv)) * nv⁻¹ := by group
    _ = nv * ((nv⁻¹ * g * nv) * (nv⁻¹ * z * nv)) * nv⁻¹ := by rw [h2]
    _ = g * z := by group

private theorem twE6_commutant_clause {S : LangSetup .E6 L p}
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g * (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)} {v : WeylGroup .E6}
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hlay : TwE6LayerHyp S a i) :
    ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
      (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model, z * u = u * z) →
      ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by ext x; rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by rw [hq]; exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0; exact ⟨x, by rw [hFr, hx]⟩
  have hρw := twE6_rho_eq_smul hΦ' hn hFrs
  obtain ⟨hσσ, hσpar⟩ := twE6_sigma
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  obtain ⟨hθ, hθmem, hmaps⟩ := twE6_rootAction hΨ hρ hw' hρw hσσ hσpar
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π, πJ, hπJ, hπJleaf, hlin, hθ', huJ, hπJpar⟩ :=
    twE6_d4Action hmaps hθ hθmem hσpar
  have hπ1 := twE6_pi_ne_one hΨ hnin hu hθ'
  have hu₂ := twE6_twist_mem hπ' hu hw₀π
  have hπ2 := twE6_pi_sq_ne_one hΨ hnin hu₂ hlin hθ' hθmem huJ hπJpar
  have hmodel := twE6_model_eq hΨ hn hΦ' hFr'
  obtain ⟨nv, hnv, n, hn, hact, Q, hQdef, hQmap⟩ := twE6_layerConj hw' hw₀ hlin hmodel
  have hlayer := twE6_layerData hn hact hQdef hlay hf hu hπJleaf hπ1 hπ2
  have hmap : (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6))).map
      (MulAut.conj nv).toMonoidHom =
      rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    rw [hnv, (canonical_weyl_root_transport Tag.E6 L).1 v _ (fun α hα => hα.1), ← hΨ]
  exact twE6_commute_transfer hmap hQmap hlayer.2.2


theorem shapeComm_of_d4_twE6_of_layer {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g * (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hlay : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L) (u : WeylGroup Tag.E6),
      u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) → ∀ π : Equiv.Perm (Fin Tag.E6.rank),
      IsD4LeafPerm π → π ≠ 1 →
      (¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → π * π ≠ 1) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α =
          u • permLattice π α) →
      Finite ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
          twistedFixedPoints (n * e6Diagram L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
        CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L
            (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
          twistedFixedPoints (n * e6Diagram L)
            (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
        (∀ y ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L (d4Set Tag.E6),
          (∀ u ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
            twistedFixedPoints (n * e6Diagram L)
              (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), y * u = u * y) →
          y ∈ torusGroup Tag.E6 L ∧
            y ∈ Subgroup.centralizer
              (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L)))) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
        (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model,
          z * u = u * z) →
        ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g := by
  refine ⟨?_, twE6_commutant_clause (S := S) hS hΨ hρ hnin hlay⟩
  exact isQuasisimple_rootSpan_inf_model_of_d4_twE6_of_layer S hS i v hΨ hρ hnin
    (fun ℓ f _ _ hf n hn u hu π hπ hπ1 hπ2 hact =>
      (hlay ℓ f hf n hn u hu π hπ hπ1 hπ2 hact).2.1)



end Transport


section Assembly

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem shapeComm_of_d4_twE6 {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
        (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model,
          z * u = u * z) →
        ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g := by
  refine shapeComm_of_d4_twE6_of_layer S hS i v hΨ hρ hnin ?_
  intro ℓ f _ _ hf n hn u hu π hleaf hπ1 _ hact
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
    exact twisted_swap_layer_E6_commutant e6FixDNAll_proved hf h12 hv1 hv2 hn hu hact
  · rw [hc] at hact
    exact twisted_swap_layer_E6_commutant e6FixDNAll_proved hf h14 hv1 hv4 hn hu hact
  · rw [hc] at hact
    exact twisted_swap_layer_E6_commutant e6FixDNAll_proved hf h24 hv2 hv4 hn hu hact
  · rw [hc] at hact
    exact twisted_triality_layer_E6_commutant hf h12 h24 h14 hv1 hv2 hv4 hn hu hact
  · rw [hc] at hact
    exact twisted_triality_layer_E6_commutant hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
