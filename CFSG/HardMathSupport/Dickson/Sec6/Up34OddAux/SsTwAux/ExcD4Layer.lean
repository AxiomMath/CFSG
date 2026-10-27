module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.NormGroup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcTwD4Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints d4Nodes)


section D4Layer

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem ssTw_cartan_e6Idx {k l : Fin Tag.E6.rank} (h : Tag.E6.cartan k l = 0) :
    τ.cartan (e6Idx k) (e6Idx l) = 0 :=
  (‹E6Sub τ›.cartan_eq k l).trans h

theorem ssTw_formPerm_three {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    List.formPerm [a, b, c] a = b ∧ List.formPerm [a, b, c] b = c ∧
      List.formPerm [a, b, c] c = a := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [List.formPerm_cons_cons, Equiv.swap_apply_def, hab, hbc, hac, hab.symm, hbc.symm,
      hac.symm]

theorem ssBig_d4_std (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {π : Equiv.Perm (Fin τ.rank)} (hleaf : IsD4LeafPerm π) {n n₁ h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹) :
    SsBig ℓ (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have m1 : e6Idx (τ := τ) 1 ∈ d4Set τ := e6Idx_mem_d4Set' 1 (by decide) (by decide)
  have m2 : e6Idx (τ := τ) 2 ∈ d4Set τ := e6Idx_mem_d4Set' 2 (by decide) (by decide)
  have m4 : e6Idx (τ := τ) 4 ∈ d4Set τ := e6Idx_mem_d4Set' 4 (by decide) (by decide)
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have c12 : τ.cartan (e6Idx 1) (e6Idx 2) = 0 := ssTw_cartan_e6Idx (by decide)
  have c14 : τ.cartan (e6Idx 1) (e6Idx 4) = 0 := ssTw_cartan_e6Idx (by decide)
  have c24 : τ.cartan (e6Idx 2) (e6Idx 4) = 0 := ssTw_cartan_e6Idx (by decide)
  have c42 : τ.cartan (e6Idx 4) (e6Idx 2) = 0 := ssTw_cartan_e6Idx (by decide)
  rcases hleaf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ssBig_of_std_fixed hτ' hℓ5 hf hh hlang m1 m2 h12 c12
      (fun c => by simpa using hgen _ m1 c) (fun c => by simpa using hgen _ m2 c)
  · exact ssBig_of_std_swap hτ' hℓ5 hf hh hlang m1 m2 h12 c12
      (fun c => by have := hgen _ m1 c; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := hgen _ m2 c; rwa [Equiv.swap_apply_right] at this)
  · exact ssBig_of_std_swap hτ' hℓ5 hf hh hlang m1 m4 h14 c14
      (fun c => by have := hgen _ m1 c; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := hgen _ m4 c; rwa [Equiv.swap_apply_right] at this)
  · exact ssBig_of_std_swap hτ' hℓ5 hf hh hlang m2 m4 h24 c24
      (fun c => by have := hgen _ m2 c; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := hgen _ m4 c; rwa [Equiv.swap_apply_right] at this)
  · obtain ⟨e1, e2, e3⟩ := ssTw_formPerm_three h12 h24 h14
    exact ssBig_of_std_cycle hτ' hℓ5 hf hh hlang m1 m2 m4 h12 h24 h14 c12 c24 c14
      (fun c => by have := hgen _ m1 c; rwa [e1] at this)
      (fun c => by have := hgen _ m2 c; rwa [e2] at this)
      (fun c => by have := hgen _ m4 c; rwa [e3] at this)
  · obtain ⟨e1, e2, e3⟩ := ssTw_formPerm_three h14 h24.symm h12
    exact ssBig_of_std_cycle hτ' hℓ5 hf hh hlang m1 m4 m2 h14 h24.symm h12 c14 c42 c12
      (fun c => by have := hgen _ m1 c; rwa [e1] at this)
      (fun c => by have := hgen _ m4 c; rwa [e2] at this)
      (fun c => by have := hgen _ m2 c; rwa [e3] at this)

theorem ssBig_d4_layer (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) {π : Equiv.Perm (Fin τ.rank)}
    (hleaf : IsD4LeafPerm π) {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) :
    SsBig ℓ (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ := fun i hi => hleaf.mem_d4Set hi
  have hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ := fun i hi => hleaf.inv.mem_d4Set hi
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ •
      (Pi.single j 1 : Fin τ.rank → ℤ) = u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hd4 : d4Nodes τ = d4Set τ := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  exact ssBig_d4_std hτ hℓ5 hf hleaf hh (fun j hj c => (hgen j hj c).1) hlang

end D4Layer

section D4LayerTw

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem ssBig_d4_layer_tw' (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {n : ModGL TwistTag.E6.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag L) {π : Equiv.Perm (Fin TwistTag.E6.tag.rank)}
    (hleaf : IsD4LeafPerm π) {u : WeylGroup TwistTag.E6.tag}
    (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice π α) :
    SsBig ℓ (rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
      twistedFixedPoints (n * diagramMap TwistTag.E6 L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hπ : ∀ i ∈ d4Set TwistTag.E6.tag, π i ∈ d4Set TwistTag.E6.tag :=
    fun i hi => hleaf.mem_d4Set hi
  have hπ' : ∀ i ∈ d4Set TwistTag.E6.tag, π.symm i ∈ d4Set TwistTag.E6.tag :=
    fun i hi => hleaf.inv.mem_d4Set hi
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (π j) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun j hj => by
    have := hact _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single π] at this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn hπ hπ' hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  exact ssBig_d4_std (τ := TwistTag.E6.tag) (Or.inl rfl) hℓ5 hf hleaf hh
    (fun j hj c => (hgen j hj c).1) hlang

theorem ssBig_d4_layer_tw (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {n : ModGL Tag.E6 L}
    (hn : n ∈ monomialSubgroup Tag.E6 L) {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hleaf : IsD4LeafPerm π) {u : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes _),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) :
    SsBig ℓ (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
      twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
  ssBig_d4_layer_tw' hℓ5 hf hn hleaf hu hact

end D4LayerTw

end CFSG.HardMathSupport.Dickson.Sec6
