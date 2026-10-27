module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcD4TPLevelS
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4B
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4C

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)


@[expose] def L154D4TPLay {G : Type*} [Group G] (q : ℕ) (P : Subgroup G) : Prop :=
  Subgroup.center ↥P = ⊥ ∧ twoPart (Nat.card ↥P) = q ^ 12

theorem L154D4TPLay.of_equiv {G G' : Type*} [Group G] [Group G'] {q : ℕ} {R : Subgroup G}
    {C : Subgroup G'} (e : ↥R ≃* ↥C) (h : L154D4TPLay q C) : L154D4TPLay q R := by
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_center_eq e.symm, h.1, Subgroup.map_bot]
  · rw [Nat.card_congr e.toEquiv]
    exact h.2

theorem L154D4TPLay.map_conj {G : Type*} [Group G] {q : ℕ} {R : Subgroup G} (φ : G ≃* G)
    (h : L154D4TPLay q R) : L154D4TPLay q (R.map φ.toMonoidHom) :=
  L154D4TPLay.of_equiv (R.equivMapOfInjective φ.toMonoidHom φ.injective).symm h

section Layer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section GraphFixed


theorem l154d4tp_lay_of_graphFixed {G : Type} [Group G] {P : Subgroup G} {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} {f e : ℕ} (hf : 1 ≤ f) (he : e = 1 ∨ e = 2)
    (hKc : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ ((2 ^ f) ^ e))
    (eP : ↥P ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : L154D4TPLay (2 ^ f) P := by
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hlie := l154r4_lieModel_graphFixed_trialityD4 Nat.prime_two hf hKc σ (by
    rcases he with rfl | rfl
    · exact Or.inl fun c => by rw [hσ, pow_one]
    · exact Or.inr hσ)
  have hc := CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) hlie
  have hcard : Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      CFSG.Open.ordTrialityD4 (2 ^ f) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
  obtain ⟨r, hr, hrr⟩ := (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf).two
  refine L154D4TPLay.of_equiv eP ⟨hZ, ?_⟩
  rw [hcard, hrr, l154d4tp_twoPart_two_pow_mul_odd hr, ← pow_mul]

end GraphFixed

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {f : ℕ}

theorem l154d4tp_trialityLayer
    [CharP L 2]
    (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ) (he : e = 1 ∨ e = 2)
    (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) :
    L154D4TPLay (2 ^ f) P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ :=
    triality_layer_graph_equiv (ℓ := 2) hf π e he hπe hπ hπ' n hn hact P hP
  exact l154d4tp_lay_of_graphFixed hf he hKc hσ eP

end Layer

section Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open scoped Matrix MatrixGroups

theorem l154d4tp_lin0
    {w₀ : WeylGroup Tag.E6} {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hw₀π : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π j) 1) :
    ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • α = permLattice π α := fun α hα => by
  have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set Tag.E6)
    (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
  rwa [one_smul] at this

theorem l154d4tp_conj_mem_parabolic
    {w₀ : WeylGroup Tag.E6} {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ : IsD4LeafPerm π)
    (hw₀π : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π j) 1)
    {x : WeylGroup Tag.E6} (hx : x ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) :
    w₀ * x * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
  have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
      parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π j, hπ.mem_d4Set hj, ?_⟩
    change simple Tag.E6 (π j) = w₀ * simple Tag.E6 j * w₀⁻¹
    rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
  exact hle ⟨x, hx, rfl⟩

theorem l154d4tp_lin_sq {w₀ : WeylGroup Tag.E6} {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ : IsD4LeafPerm π)
    (hlin0 : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • α = permLattice π α)
    (hππ : π * π = 1) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) : w₀ • w₀ • α = α := by
  have hα' : w₀ • α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    rw [hlin0 α hα]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← hlin0 α hα]
      exact IsRoot.smul hα.1 w₀
    · have hk' : π.symm k ∉ d4Nodes Tag.E6 := fun h => hk (by
        have h' := hπ.mem_d4Set (show π.symm k ∈ d4Set Tag.E6 from h)
        rw [Equiv.apply_symm_apply] at h'
        exact h')
      exact hα.2 _ hk'
  rw [hlin0 _ hα', hlin0 α hα, ← permLattice_mul, hππ]
  rfl

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem l154d4tp_layer_untw
    [CharP L 2]
    (S : LangSetup Tag.E6 L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup Tag.E6}
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w) (v : WeylGroup Tag.E6)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {a b c : Fin Tag.E6.rank} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4) (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4)
    (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    ∃ f : ℕ, 1 ≤ f ∧ S.D.q = 2 ^ f ∧ L154D4TPLay (2 ^ f)
      (rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        S.D.model) := by
  classical
  have hc2 : CharP L 2 := inferInstance
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have hℓ2 : ℓ = 2 := CharP.eq L hchar hc2
  subst hℓ2
  have hFr' : Fr = iterateFrobenius L 2 f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  refine ⟨f, hf, hq, ?_⟩
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α :=
    fun α hα => hα.1
  rw [l154r4_rootSpan_inf_model_eq S hFr' hΦ hn, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hπ : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  obtain ⟨hcyc, hπ₁, hπ₂⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∃ u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6),
      ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nv, hn'M⟩ • α =
          u • permLattice (List.formPerm [a, b, c]) α :=
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  rcases hcyc with h1 | h2
  · exact (l154d4tp_trialityLayer hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ₁ i hi) (fun i hi => hπ₂ i hi) _ hn'M hact' _ rfl).map_conj (MulAut.conj nv)
  · exact (l154d4tp_trialityLayer hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ₁ i hi) (fun i hi => hπ₂ i hi) _ hn'M hact' _ rfl).map_conj (MulAut.conj nv)

theorem l154d4tp_untw_mapsJ (S : LangSetup Tag.E6 L p) {w : WeylGroup Tag.E6}
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * v) := by
  intro α hα
  have hmem : v • α ∈ componentRoots (rootCharHom a) i := hΨ ▸ ⟨α, hα, rfl⟩
  have hw : w • v • α ∈ componentRoots (rootCharHom a) i := by
    rw [← hρw _ hmem.1.1]
    exact hρ _ hmem
  obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw :
    w • v • α ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
  exact hβ

theorem l154d4tp_untw_pi_ne_one (S : LangSetup Tag.E6 L p) {w : WeylGroup Tag.E6}
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α) : π ≠ 1 := by
  rintro rfl
  apply h1
  refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
  rintro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  rw [hρw _ hγ.1.1]
  calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
    _ = v • (u • α) := by
        rw [hact α hα]
        rfl
    _ = (v * u * v⁻¹) • v • α := by
        rw [mul_smul, mul_smul, inv_smul_smul]

theorem l154d4tp_untw_pi_sq_ne_one (S : LangSetup Tag.E6 L p) {w : WeylGroup Tag.E6}
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) {u w₀ : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) (hw₀ : v⁻¹ * w * v = u * w₀)
    {π : Equiv.Perm (Fin Tag.E6.rank)} (hπ : IsD4LeafPerm π)
    (hw₀π : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π j) 1) :
    π * π ≠ 1 := by
  intro hππ
  apply h2
  have hu' := l154d4tp_conj_mem_parabolic hπ hw₀π hu
  refine ⟨v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹,
    hΨ ▸ conj_mem_closure_rootReflection v (mul_mem hu hu'), ?_⟩
  rintro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  have hγr : IsRoot Tag.E6 (v • α) := hγ.1.1
  have hw2 := l154d4tp_lin_sq hπ (l154d4tp_lin0 hw₀π) hππ hα
  rw [Function.iterate_succ_apply, Function.iterate_one, hρw _ hγr,
    hρw _ ((isRoot_smul_iff w).2 hγr)]
  calc w • w • v • α = v • ((v⁻¹ * w * v) • (v⁻¹ * w * v) • α) := by
        simp only [mul_smul, smul_inv_smul]
    _ = v • (u • w₀ • u • w₀ • α) := by rw [hw₀]; simp only [mul_smul]
    _ = v • (u • (w₀ * u * w₀⁻¹) • w₀ • w₀ • α) := by simp only [mul_smul, inv_smul_smul]
    _ = (v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹) • v • α := by
        rw [hw2]
        simp only [mul_smul, inv_smul_smul]


theorem l154d4tp_outer_untw
    [CharP L 2]
    (S : LangSetup Tag.E6 L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup Tag.E6}
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, 1 ≤ f ∧ S.D.q = 2 ^ f ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
        L154D4TPLay (2 ^ f) (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  classical
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ :=
    exists_d4_action d4Base_E6 (l154d4tp_untw_mapsJ S hρw i v hΨ hρ)
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, l154d4tp_lin0 hw₀π α hα]
  have hπ1 : π ≠ 1 := l154d4tp_untw_pi_ne_one S hρw i v hΨ h1 hu hact
  have hπ2 : π * π ≠ 1 := l154d4tp_untw_pi_sq_ne_one S hρw i v hΨ h2 hu hw₀ hπ hw₀π
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  have hv1' : (e6Idx (τ := Tag.E6) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2' : (e6Idx (τ := Tag.E6) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4' : (e6Idx (τ := Tag.E6) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  rw [hΨ]
  rcases hπ.eq_cycle hπ1 hπ2 with rfl | rfl
  · obtain ⟨f, hf, hq, hlay⟩ := l154d4tp_layer_untw S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4 hact
    exact ⟨f, hf, hq, (rootSpan_inf_model_quasisimple_d4 d4TrialityLayer_E6 S hFr hΦ hn v hu
      h12 h24 h14 hv1' hv2' hv4' hact).2, hlay⟩
  · obtain ⟨f, hf, hq, hlay⟩ := l154d4tp_layer_untw S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
      hact
    exact ⟨f, hf, hq, (rootSpan_inf_model_quasisimple_d4 d4TrialityLayer_E6 S hFr hΦ hn v hu
      h14 h24.symm h12 hv1' hv4' hv2' hact).2, hlay⟩

end Untw

section Tw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open scoped Matrix MatrixGroups

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ}

theorem l154d4tp_twisted_triality_layer
    (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    L154D4TPLay (2 ^ f)
      (rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
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
  have key : ∀ e, StdTwist n₁ (List.formPerm [a, b, c]) e →
      L154D4TPLay (2 ^ f) (subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
    intro e hstd
    obtain ⟨K, _, _, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang rfl
    exact l154d4tp_lay_of_graphFixed hf hstd.he hKc hσ eP
  rcases hcyc with h1 | h2
  · exact key 1 ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
  · exact key 2 ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩

variable
  {p : ℕ}

theorem l154d4tp_twist_mem_parabolic {u : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) :
    e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
  have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
      parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
    exact (e6WeylTwist_simple j).symm
  exact hle ⟨u, hu, rfl⟩

theorem l154d4tp_tw_pi_sq_ne_one (S : LangSetup .E6 L p) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) {u w₀ : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) {π' : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ' : IsD4LeafPerm π')
    (hw₀π : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π' j) 1)
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) α) :
    (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) * (π' * Equiv.swap (e6Idx 2) (e6Idx 4)) ≠ 1 := by
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  intro hππ
  apply h2
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := l154r4_tw_lin hw₀π
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := l154td4_theta_mem S i v hΨ hρ hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hconj := l154d4tp_conj_mem_parabolic hπ' hw₀π (l154d4tp_twist_mem_parabolic hu)
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
  refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
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
    exact l154td4_theta_mem S i v hΨ hρ hα
  have e1 : S.ρ (v • α) = v • β := by
    rw [hβ, ← hθ' α hα, smul_inv_smul]
  have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
    rw [← hθ' β hβJ, smul_inv_smul]
  have e3 : permLattice πJ (permLattice πJ α) = α := by
    rw [← permLattice_mul, hππ]
    rfl
  calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
    _ = v • (u • permLattice πJ β) := by rw [e1, e2]
    _ = v • (u₂ • α) := by
        rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
    _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]

theorem l154d4tp_outer_tw
    (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, 1 ≤ f ∧ S.D.q = 2 ^ f ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
        L154D4TPLay (2 ^ f) (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  classical
  have hc2 : CharP L 2 := inferInstance
  obtain ⟨w, hn, hρw⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq S hS
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have hℓ2 : ℓ = 2 := CharP.eq L hchar hc2
  subst hℓ2
  have hFr' : Fr = iterateFrobenius L 2 f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  refine ⟨f, hf, hq, ?_⟩
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ :=
    exists_d4_action d4Base_E6 (l154r4_tw_mapsJ S hρw i v hΨ hρ)
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := l154r4_tw_lin hw₀π
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [l154r4_tw_theta S hρw v α hα, hw₀, mul_smul, hlin α hα]
  have hπ1 : πJ ≠ 1 := l154r4_tw_pi_ne_one S i v hΨ h1 hu hθ'
  have hπ2 : πJ * πJ ≠ 1 := l154d4tp_tw_pi_sq_ne_one S i v hΨ hρ h2 hu hπ' hw₀π hθ'
  obtain ⟨n', hn', hact, g, heq⟩ := l154r4_tw_layer_eq S hFr' hΦ' hn i v hΨ hw₀ hlin
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
    twistedFixedPoints (n' * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
    with hQ
  have hlayer : IsQuasisimple Q ∧ L154D4TPLay (2 ^ f) Q := by
    rcases hπJleaf.eq_cycle hπ1 hπ2 with hc | hc
    · rw [hc] at hact
      exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact).2,
        l154d4tp_twisted_triality_layer hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact⟩
    · rw [hc] at hact
      exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact).2,
        l154d4tp_twisted_triality_layer hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact⟩
  have e : Q ≃* Q.map (MulAut.conj g).toMonoidHom :=
    Q.equivMapOfInjective _ (MulAut.conj g).injective
  rw [heq]
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1, hlayer.2.map_conj (MulAut.conj g)⟩

end Tw

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
