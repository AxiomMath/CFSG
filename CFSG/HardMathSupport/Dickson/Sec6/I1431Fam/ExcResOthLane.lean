module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthStd
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcE6Lane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFourLayer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Dickson.Sec6 (ssTw_rationalComponent_eq_layer ssTw_exists_f
  ssTw_layer_untw_adj ssTw_layer_tw_adj ssTw_cartan_e6Idx ssTw_formPerm_three)


set_option linter.unusedSectionVars false

@[expose] def ExcOthQ {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  CFSG.IsQuasisimple ↥P ∧ ExcOthNoL2 P

theorem ExcOthQ.map_conj {G : Type*} [Group G] {P : Subgroup G} (h : ExcOthQ P) (g : G) :
    ExcOthQ (P.map (MulAut.conj g).toMonoidHom) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (P.equivMapOfInjective _ (MulAut.conj g).injective) h.1, h.2.map_conj g⟩

section Transport

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem ssOth_of_std {J : Set (Fin τ.rank)} {n n₁ h : ModGL τ L} (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    (hstd : ExcOthNoL2 (subsystemGroup τ L J ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    ExcOthNoL2 (subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have heq : subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (subsystemGroup τ L J ⊓
        twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).map
          (MulAut.conj h⁻¹).toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨h * x * h⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by simp [mul_assoc]⟩
      · exact mul_mem (mul_mem hh (Subgroup.mem_inf.1 hx).1) (inv_mem hh)
      · exact (hlang x).1 (mem_twistedFixedPoints.1 (Subgroup.mem_inf.1 hx).2)
    · rintro ⟨y, hy, rfl⟩
      have hyJ := (Subgroup.mem_inf.1 hy).1
      have hyF := mem_twistedFixedPoints.1 (Subgroup.mem_inf.1 hy).2
      have hx : (MulAut.conj h⁻¹).toMonoidHom y = h⁻¹ * y * h := by simp
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [hx]
        exact mul_mem (mul_mem (inv_mem hh) hyJ) hh
      · rw [hx, mem_twistedFixedPoints]
        refine (hlang _).2 ?_
        have e : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
        rw [e]
        exact hyF
  rw [heq]
  exact hstd.map_conj _

end Transport

section D4Std

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem ssOth_cartan_e6Idx {k l : Fin Tag.E6.rank} {v : ℤ} (h : Tag.E6.cartan k l = v) :
    τ.cartan (e6Idx k) (e6Idx l) = v :=
  (‹E6Sub τ›.cartan_eq k l).trans h

theorem ssOth_d4_std (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f)
    {π : Equiv.Perm (Fin τ.rank)} (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1) {n n₁ h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹) :
    ExcOthNoL2 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  refine ssOth_of_std hh hlang ?_
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have m1 : e6Idx (τ := τ) 1 ∈ d4Set τ := e6Idx_mem_d4Set' 1 (by decide) (by decide)
  have m2 : e6Idx (τ := τ) 2 ∈ d4Set τ := e6Idx_mem_d4Set' 2 (by decide) (by decide)
  have m3 : e6Idx (τ := τ) 3 ∈ d4Set τ := e6Idx_mem_d4Set' 3 (by decide) (by decide)
  have m4 : e6Idx (τ := τ) 4 ∈ d4Set τ := e6Idx_mem_d4Set' 4 (by decide) (by decide)
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h31 : e6Idx (τ := τ) 3 ≠ e6Idx 1 := e6Idx_ne (by decide)
  have h32 : e6Idx (τ := τ) 3 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h34 : e6Idx (τ := τ) 3 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have c12 : τ.cartan (e6Idx 1) (e6Idx 2) = 0 := ssOth_cartan_e6Idx (by decide)
  have c21 : τ.cartan (e6Idx 2) (e6Idx 1) = 0 := ssOth_cartan_e6Idx (by decide)
  have c14 : τ.cartan (e6Idx 1) (e6Idx 4) = 0 := ssOth_cartan_e6Idx (by decide)
  have c41 : τ.cartan (e6Idx 4) (e6Idx 1) = 0 := ssOth_cartan_e6Idx (by decide)
  have c24 : τ.cartan (e6Idx 2) (e6Idx 4) = 0 := ssOth_cartan_e6Idx (by decide)
  have c42 : τ.cartan (e6Idx 4) (e6Idx 2) = 0 := ssOth_cartan_e6Idx (by decide)
  have c13 : τ.cartan (e6Idx 1) (e6Idx 3) = -1 := ssOth_cartan_e6Idx (by decide)
  have c23 : τ.cartan (e6Idx 2) (e6Idx 3) = -1 := ssOth_cartan_e6Idx (by decide)
  have c43 : τ.cartan (e6Idx 4) (e6Idx 3) = -1 := ssOth_cartan_e6Idx (by decide)
  have hfix3 : π (e6Idx 3) = e6Idx 3 := hleaf.apply_of_ne h31 h32 h34
  have hx3 : ∀ c : L, n₁ * xUnit τ L (e6Idx 3) c * n₁⁻¹ = xUnit τ L (e6Idx 3) c := fun c => by
    have := (hgen _ m3 c).1
    rwa [hfix3] at this
  have hy3 : ∀ c : L, n₁ * yUnit τ L (e6Idx 3) c * n₁⁻¹ = yUnit τ L (e6Idx 3) c := fun c => by
    have := (hgen _ m3 c).2
    rwa [hfix3] at this
  rcases hleaf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hπ1
  ·
    refine excOth_noL2_std_swap hτ' hf m1 m2 m4 c12 c14 c24
      (fun c => by have := (hgen _ m1 c).1; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := (hgen _ m1 c).2; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := (hgen _ m2 c).1; rwa [Equiv.swap_apply_right] at this)
      (fun c => by have := (hgen _ m2 c).2; rwa [Equiv.swap_apply_right] at this)
      (fun c => by
        have := (hgen _ m4 c).1
        rwa [Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm] at this)
      (fun c => by
        have := (hgen _ m4 c).2
        rwa [Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm] at this)
  ·
    refine excOth_noL2_std_swap hτ' hf m1 m4 m2 c14 c12 c42
      (fun c => by have := (hgen _ m1 c).1; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := (hgen _ m1 c).2; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := (hgen _ m4 c).1; rwa [Equiv.swap_apply_right] at this)
      (fun c => by have := (hgen _ m4 c).2; rwa [Equiv.swap_apply_right] at this)
      (fun c => by
        have := (hgen _ m2 c).1
        rwa [Equiv.swap_apply_of_ne_of_ne h12.symm h24] at this)
      (fun c => by
        have := (hgen _ m2 c).2
        rwa [Equiv.swap_apply_of_ne_of_ne h12.symm h24] at this)
  ·
    refine excOth_noL2_std_swap hτ' hf m2 m4 m1 c24 c21 c41
      (fun c => by have := (hgen _ m2 c).1; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := (hgen _ m2 c).2; rwa [Equiv.swap_apply_left] at this)
      (fun c => by have := (hgen _ m4 c).1; rwa [Equiv.swap_apply_right] at this)
      (fun c => by have := (hgen _ m4 c).2; rwa [Equiv.swap_apply_right] at this)
      (fun c => by
        have := (hgen _ m1 c).1
        rwa [Equiv.swap_apply_of_ne_of_ne h12 h14] at this)
      (fun c => by
        have := (hgen _ m1 c).2
        rwa [Equiv.swap_apply_of_ne_of_ne h12 h14] at this)
  ·
    obtain ⟨e1, e2, e3⟩ := ssTw_formPerm_three h12 h24 h14
    refine excOth_noL2_std_triple hτ' hf m1 m2 m4 m3 c12 c14 c24 c13 c23 c43
      (fun c => by have := (hgen _ m1 c).1; rwa [e1] at this)
      (fun c => by have := (hgen _ m1 c).2; rwa [e1] at this)
      (fun c => by have := (hgen _ m2 c).1; rwa [e2] at this)
      (fun c => by have := (hgen _ m2 c).2; rwa [e2] at this)
      (fun c => by have := (hgen _ m4 c).1; rwa [e3] at this)
      (fun c => by have := (hgen _ m4 c).2; rwa [e3] at this) hx3 hy3
  ·
    obtain ⟨e1, e2, e3⟩ := ssTw_formPerm_three h14 h24.symm h12
    refine excOth_noL2_std_triple hτ' hf m1 m4 m2 m3 c14 c12 c42 c13 c43 c23
      (fun c => by have := (hgen _ m1 c).1; rwa [e1] at this)
      (fun c => by have := (hgen _ m1 c).2; rwa [e1] at this)
      (fun c => by have := (hgen _ m4 c).1; rwa [e2] at this)
      (fun c => by have := (hgen _ m4 c).2; rwa [e2] at this)
      (fun c => by have := (hgen _ m2 c).1; rwa [e3] at this)
      (fun c => by have := (hgen _ m2 c).2; rwa [e3] at this) hx3 hy3

end D4Std

section D4Layer

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem ssOth_d4_layer (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) {π : Equiv.Perm (Fin τ.rank)}
    (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1) {u : WeylGroup τ}
    (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) :
    ExcOthNoL2 (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
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
  exact ssOth_d4_std hτ hf hleaf hπ1 hh hgen hlang

end D4Layer

section D4LayerTw

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem ssOth_d4_layer_tw' (hf : 1 ≤ f) {n : ModGL TwistTag.E6.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag L) {π : Equiv.Perm (Fin TwistTag.E6.tag.rank)}
    (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1) {u : WeylGroup TwistTag.E6.tag}
    (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice π α) :
    ExcOthNoL2 (rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
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
  exact ssOth_d4_std (τ := TwistTag.E6.tag) (Or.inl rfl) hf hleaf hπ1 hh hgen hlang

theorem ssOth_d4_layer_tw (hf : 1 ≤ f) {n : ModGL Tag.E6 L}
    (hn : n ∈ monomialSubgroup Tag.E6 L) {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1) {u : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes _),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) :
    ExcOthNoL2 (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
      twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
  ssOth_d4_layer_tw' hf hn hleaf hπ1 hu hact

end D4LayerTw

section Lanes

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem ssOth_noL2_of_layer (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hP : ExcOthQ (rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  rw [ssTw_rationalComponent_eq_layer S i hρ hP.1]
  exact hP.2

end Lanes

section Outer

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem ssOth_d4_outer [E6Sub τ] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hsearch : D4BaseSearch τ) (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ)
    (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨f, hf, hq⟩ := ssTw_exists_f S (ℓ := ℓ)
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
  have hlayer : ExcOthQ (rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    refine ssTw_layer_untw_adj S hq hFr hΦ hn v (d4Nodes τ) ExcOthQ
      (fun P g h => h.map_conj g) ?_
    intro n hn' hC hw'
    have hact' : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn'⟩ • α = u • permLattice π α := fun α hα => by
      rw [hw']
      exact hact α hα
    refine ⟨?_, ssOth_d4_layer hτ hf hn' hπ hπ1 hu hact'⟩
    have hex : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn'⟩ • α = u • permLattice π α := ⟨u, hu, hact'⟩
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact (hL2 L ℓ f hf _ _ h12 hv1 hv2 n hn' hC hex _ rfl).2
    · exact (hL2 L ℓ f hf _ _ h14 hv1 hv4 n hn' hC hex _ rfl).2
    · exact (hL2 L ℓ f hf _ _ h24 hv2 hv4 n hn' hC hex _ rfl).2
    · exact (hL3 L ℓ f hf _ _ _ h12 h24 h14 hv1 hv2 hv4 n hn' hC hex _ rfl).2.1
    · exact (hL3 L ℓ f hf _ _ _ h14 h24.symm h12 hv1 hv4 hv2 n hn' hC hex _ rfl).2.1
  exact ssOth_noL2_of_layer S i hρ hlayer

end Outer

section Twisted

variable
  {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem ssOth_d4_twE6 (hE6 : E6FixDNAll) (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨f, hf, hq⟩ := ssTw_exists_f S (ℓ := ℓ)
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
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
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have hπ1 : πJ ≠ 1 := by
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
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  have hlayer : ExcOthQ (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hΨ]
    refine ssTw_layer_tw_adj S hq hFr hΦ' hn v (d4Nodes Tag.E6) ExcOthQ
      (fun P g h => h.map_conj g) ?_
    intro n hn' hC hwn
    have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn'⟩ • permLattice e6Graph α = u • permLattice πJ α := by
      intro α hα
      rw [hwn, ← hw', hw₀, mul_smul, hlin α hα]
    refine ⟨?_, ssOth_d4_layer_tw hf hn' hπJleaf hπ1 hu hact⟩
    rcases hπJleaf with hc | hc | hc | hc | hc | hc
    · exact absurd hc hπ1
    · rw [hc] at hact
      exact (twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn' hu hact).2
    · rw [hc] at hact
      exact (twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn' hu hact).2
    · rw [hc] at hact
      exact (twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn' hu hact).2
    · rw [hc] at hact
      exact (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact).2
    · rw [hc] at hact
      exact (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact).2
  exact ssOth_noL2_of_layer S i hρ hlayer

end Twisted

section D4Class


theorem ssOth_d4class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 : E6FixDNAll := e6FixDNAll_proved
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    exfalso
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
      exact ssOth_d4_outer (Or.inl rfl) d4Base_E6 d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) S
        hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hℓ
    · rw [hs, Function.iterate_one] at hnin
      exact ssOth_d4_twE6 hE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin hℓ
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ssOth_d4_outer (Or.inr (Or.inl rfl)) d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hℓ
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ssOth_d4_outer (Or.inr (Or.inr rfl)) d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hℓ

end D4Class


section E6Layer

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem ssOth_e6_layer (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (e6Set τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : π = 1 ∨ π = rhoτ τ) (hπ1 : π ≠ 1)
    (hact : ∀ j ∈ e6Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ExcOthNoL2 (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hπρ : π = rhoτ τ := hπ.resolve_left hπ1
  subst hπρ
  have hπJ : ∀ i ∈ e6Set τ, rhoτ τ i ∈ e6Set τ := fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, (rhoτ τ).symm i ∈ e6Set τ := fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    CFSG.RankThree.PartOne.KE6.exists_conj_twistedFixed hf hn hπJ hπJ' hu hact
  have hP' : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ L (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  rw [hP']
  refine ssOth_of_std hh hlang ?_
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    Or.inr (Or.inr (M27Ok.isE7E8 (τ := τ)))
  have m0 : e6Idx (τ := τ) 0 ∈ e6Set τ := e6Idx_mem_e6Set 0
  have m1 : e6Idx (τ := τ) 1 ∈ e6Set τ := e6Idx_mem_e6Set 1
  have m5 : e6Idx (τ := τ) 5 ∈ e6Set τ := e6Idx_mem_e6Set 5
  have c05 : τ.cartan (e6Idx 0) (e6Idx 5) = 0 := ssOth_cartan_e6Idx (by decide)
  have c01 : τ.cartan (e6Idx 0) (e6Idx 1) = 0 := ssOth_cartan_e6Idx (by decide)
  have c51 : τ.cartan (e6Idx 5) (e6Idx 1) = 0 := ssOth_cartan_e6Idx (by decide)
  refine excOth_noL2_std_swap hτ' hf m0 m5 m1 c05 c01 c51
    (fun c => by
      have := (hgen _ m0 c).1
      rwa [rhoτ_e6Idx, show rho6 0 = 5 by decide] at this)
    (fun c => by
      have := (hgen _ m0 c).2
      rwa [rhoτ_e6Idx, show rho6 0 = 5 by decide] at this)
    (fun c => by
      have := (hgen _ m5 c).1
      rwa [rhoτ_e6Idx, show rho6 5 = 0 by decide] at this)
    (fun c => by
      have := (hgen _ m5 c).2
      rwa [rhoτ_e6Idx, show rho6 5 = 0 by decide] at this)
    (fun c => by
      have := (hgen _ m1 c).1
      rwa [rhoτ_e6Idx, show rho6 1 = 1 by decide] at this)
    (fun c => by
      have := (hgen _ m1 c).2
      rwa [rhoτ_e6Idx, show rho6 1 = 1 by decide] at this)

end E6Layer

section E6Lane


theorem ssOth_e6 {tau : Tag} [M27Ok tau] [E6Sub tau] {L : Type} [Field L] [IsAlgClosed L]
    {p0 : ℕ} (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (haT : rootDiagUnit tau a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup tau)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots tau (e6Nodes tau))
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin tau.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {l : ℕ} (hl : l.Prime) [CharP L l] :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨f, hf, hq⟩ := ssTw_exists_f S (ℓ := l)
  have hτ' : ∀ t : TwistTag, t.tag ≠ tau := by
    rcases M27Ok.isE7E8 (τ := tau) with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρ := ssTw_rho_stable_e6 S haT i v hΨ
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at hnin
  have hΨ' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots tau (e6Set tau) := by
    rw [hΨ, e6Nodes_eq_e6Set]
  have hmapsJ : MapsJ tau (e6Set tau) (v⁻¹ * w * v) := by
    intro α hα
    have hmem : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ']
      exact ⟨α, hα, rfl⟩
    have h2 := hw (v • α) hmem
    rw [hΨ'] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hmapsJ
  have hlin : ∀ α ∈ parabolicRoots tau (e6Set tau), (v⁻¹ * w * v) • α = u • permLattice π α :=
    fun α hα => smul_eq_of_simple hact hα.2
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ' ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ' ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots tau (e6Set tau))
    rw [S.rho_eq_smul hτ' hn hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hlin α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hlayer : ExcOthQ (rootSpan tau L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hΨ]
    rw [hΨ] at hw
    refine ssTw_layer_untw S hq hFr hΦ hn v (e6Nodes tau) ExcOthQ
      (fun P g h => h.map_conj g) ?_
    intro n hn' hw'
    have hmaps : ∀ α ∈ parabolicRoots tau (e6Nodes tau),
        weylQuotientHom tau L ⟨n, hn'⟩ • α ∈ parabolicRoots tau (e6Nodes tau) := by
      intro α hα
      rw [hw']
      obtain ⟨β, hβ, hβe⟩ := hw (v • α) ⟨α, hα, rfl⟩
      rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
      exact hβ
    exact ⟨(e6Layer_finite_quasisimple tau (ℓ := l) hf hn' hmaps).2,
      ssOth_e6_layer hf hn' hu hπ hπ1 (fun j hj => by rw [hw']; exact hact j hj)⟩
  exact ssOth_noL2_of_layer S i hρ hlayer

theorem ssOth_e6class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc : (componentRoots (rootCharHom a) i).ncard = 72)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | D4 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E7 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i hr hc
    exact ssOth_e6 S hT i v hv hnin hℓ
  | E8 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i hr hc
    exact ssOth_e6 S hT i v hv hnin hℓ


end E6Lane

end CFSG.HardMathSupport.Dickson.Sec6.I1431
