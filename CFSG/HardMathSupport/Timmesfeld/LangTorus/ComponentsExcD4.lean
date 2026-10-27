module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)


theorem leafCycle_E6 : ∀ a b c : Fin Tag.E6.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
    b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
    a ≠ b → b ≠ c → a ≠ c →
    ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
      (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
    (∀ i : Fin Tag.E6.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
      (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
    (∀ i : Fin Tag.E6.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
      (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧ ((List.formPerm [a, b, c]).symm i).val ≤ 4)) :=
  by decide +kernel

theorem d4TrialityLayer_E6 :
    D4TrialityLayer .E6 := by
  exact d4TrialityLayer_of_leafCycle leafCycle_E6


section Layer


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootSpan_inf_model_quasisimple_d4_of_layer (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      Finite ↥(rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
        CFSG.IsQuasisimple ↥(rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    Finite ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple
        ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
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
  obtain ⟨hfin, hqs⟩ := hlayer ℓ f hf (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  set P := rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
    twistedFixedPoints (nv⁻¹ * nw * nv) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
  have e : P ≃* P.map (MulAut.conj nv).toMonoidHom :=
    P.equivMapOfInjective _ (MulAut.conj nv).injective
  exact ⟨Finite.of_equiv _ e.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs⟩

theorem rootSpan_inf_model_quasisimple_d4 (hL : D4TrialityLayer τ) (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {a b c : Fin τ.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    Finite ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple
        ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_quasisimple_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf n hn hC hex =>
      let h := hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC hex _ rfl
      ⟨h.1, h.2.1⟩) hact

end Layer

section Helpers

variable {τ : Tag}

theorem conj_mem_closure_rootReflection {J : Set (Fin τ.rank)} (v : WeylGroup τ) {u : WeylGroup τ}
    (hu : u ∈ parabolicWeylGroup τ J) :
    v * u * v⁻¹ ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ J, s = rootReflection γ} := by
  have hle : (parabolicWeylGroup τ J).map (MulAut.conj v).toMonoidHom ≤
      Subgroup.closure {s : WeylGroup τ |
        ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ J, s = rootReflection γ} := by
    rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨v • (Pi.single j 1 : Fin τ.rank → ℤ),
      ⟨Pi.single j 1, single_mem_parabolicRoots hj, rfl⟩, ?_⟩
    rw [rootReflection_eq_conj rfl]
    rfl
  exact hle ⟨u, hu, rfl⟩

theorem rootReflection_single (k : Fin τ.rank) :
    rootReflection (Pi.single k 1 : Fin τ.rank → ℤ) = simple τ k := by
  rw [rootReflection_eq_conj (w := 1) (one_smul _ _), one_mul, inv_one, mul_one]

theorem componentOrbitLength_eq_one {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (hfin : Ψ.Finite) (hρ : ∀ γ ∈ Ψ, ρ γ ∈ Ψ) : componentOrbitLength ρ Ψ = 1 := by
  have himg : (ρ : (Fin τ.rank → ℤ) → _)^[1] '' Ψ = Ψ := by
    rw [Function.iterate_one]
    exact ((hfin.injOn_iff_bijOn_of_mapsTo hρ).1 ρ.injective.injOn).image_eq
  have hmem : 1 ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} := ⟨one_pos, himg⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  exact (Nat.sInf_mem ⟨1, hmem⟩).1

end Helpers

section Twist


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem isQuasisimple_rootSpan_inf_model_of_d4 [E6Sub τ] (hsearch : D4BaseSearch τ)
    (hL : D4TrialityLayer τ) (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
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
  rw [hΨ]
  rcases hπ.eq_cycle hπ1 hπ2 with rfl | rfl
  · exact (rootSpan_inf_model_quasisimple_d4 hL S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
      hact).2
  · exact (rootSpan_inf_model_quasisimple_d4 hL S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
      hact).2

theorem isQuasisimple_rationalComponent_of_d4 [E6Sub τ] (hsearch : D4BaseSearch τ)
    (hL : D4TrialityLayer τ) (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
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
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  isQuasisimple_rationalComponent_of_layer S i hρ
    (isQuasisimple_rootSpan_inf_model_of_d4 hsearch hL S hFr hΦ hn hρw i v hΨ hρ h1 h2)

end Twist

end CFSG.HardMathSupport.Timmesfeld.LangTorus
