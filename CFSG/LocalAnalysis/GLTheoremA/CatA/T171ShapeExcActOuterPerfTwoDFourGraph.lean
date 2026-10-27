module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourGraphCheck
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDatum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice TauCeti


theorem rootReflection_mem_componentWeylGroup_of_mem {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    rootReflection γ ∈ componentWeylGroup Ψ := by
  obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hγ
  rw [rootReflection_smul_root w (simpleRoots_isRoot hβ)]
  exact mul_mem (mul_mem hw (rootReflection_mem_componentWeylGroup hβ)) (inv_mem hw)

theorem exists_rho_conj_realization {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ)
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) :
    ∃ z ∈ componentWeylGroup Ψ, ∀ γ ∈ Ψ, S.ρ (w • (S.ρ.symm γ)) = z • γ := by
  have hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ h => hst.subset (Set.mem_image_of_mem _ h)
  refine Subgroup.closure_induction (p := fun w _ => ∃ z ∈ componentWeylGroup Ψ,
    ∀ γ ∈ Ψ, S.ρ (w • (S.ρ.symm γ)) = z • γ) ?_ ?_ ?_ ?_ (componentWeylGroup_le Ψ hw)
  · rintro s ⟨γ, hγ, rfl⟩
    exact ⟨rootReflection (S.ρ γ), rootReflection_mem_componentWeylGroup_of_mem hΨ (hρ γ hγ),
      fun δ _ => (map_rootReflection_smul (δ := S.rhoHom) S.frob.iform_eq (hΨ.isRoot γ hγ)
        (hΨ.isRoot _ (hρ γ hγ)) (S.ρ.symm δ)).trans
          (congrArg (rootReflection (S.ρ γ) • ·) (S.ρ.apply_symm_apply δ))⟩
  · refine ⟨1, one_mem _, fun γ hγ => ?_⟩
    rw [one_smul, one_smul, Equiv.apply_symm_apply]
  · intro x y _ _ hx hy
    obtain ⟨zx, hzx, hzxγ⟩ := hx
    obtain ⟨zy, hzy, hzyγ⟩ := hy
    refine ⟨zx * zy, mul_mem hzx hzy, fun γ hγ => ?_⟩
    have hγ' : zy • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ hzy γ hγ
    have h1 : S.ρ (y • (S.ρ.symm γ)) = zy • γ := hzyγ γ hγ
    have h2 : S.ρ.symm (zy • γ) = y • (S.ρ.symm γ) := by
      rw [← h1, Equiv.symm_apply_apply]
    calc S.ρ ((x * y) • (S.ρ.symm γ))
        = S.ρ (x • (S.ρ.symm (zy • γ))) := by rw [mul_smul, h2]
      _ = zx • (zy • γ) := hzxγ (zy • γ) hγ'
      _ = (zx * zy) • γ := by rw [mul_smul]
  · intro x _ hx
    obtain ⟨zx, hzx, hzxγ⟩ := hx
    refine ⟨zx⁻¹, inv_mem hzx, fun γ hγ => ?_⟩
    have hγ' : zx⁻¹ • γ ∈ Ψ :=
      smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hzx) γ hγ
    have h1 : S.ρ (x • (S.ρ.symm (zx⁻¹ • γ))) = zx • (zx⁻¹ • γ) := hzxγ _ hγ'
    have h2 : x • (S.ρ.symm (zx⁻¹ • γ)) = S.ρ.symm γ := by
      have hh := congrArg S.ρ.symm h1
      rw [Equiv.symm_apply_apply, smul_inv_smul] at hh
      exact hh
    calc S.ρ (x⁻¹ • S.ρ.symm γ)
        = S.ρ (x⁻¹ • (x • (S.ρ.symm (zx⁻¹ • γ)))) := by rw [h2]
      _ = S.ρ (S.ρ.symm (zx⁻¹ • γ)) := by rw [inv_smul_smul]
      _ = zx⁻¹ • γ := Equiv.apply_symm_apply _ _

theorem rhoTwist_sq_eq_self {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ)
    (hinner2 : twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[2]))
    {v : WeylGroup τ} (hv : v ∈ componentWeylGroup Ψ)
    (hpos : ∀ γ ∈ posRoots Ψ, S.rhoTwist v γ ∈ posRoots Ψ) :
    ∀ γ ∈ Ψ, S.rhoTwist v (S.rhoTwist v γ) = γ := by
  obtain ⟨z, hz, hzv⟩ := exists_rho_conj_realization S hΨ hst hv
  obtain ⟨w, hw, hwv⟩ := hinner2
  have hwcomp : w ∈ componentWeylGroup Ψ := by
    refine (Subgroup.closure_le (componentWeylGroup Ψ)).2 ?_ hw
    rintro s ⟨γ, hγ, rfl⟩
    exact rootReflection_mem_componentWeylGroup_of_mem hΨ hγ
  have hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ h => hst.subset (Set.mem_image_of_mem _ h)
  have hmap : ∀ γ ∈ Ψ, S.rhoTwist v (S.rhoTwist v γ) = (v * z * w) • γ := by
    intro γ hγ
    have hγ1 : S.ρ γ ∈ Ψ := hρ γ hγ
    have hγ2 : S.ρ (S.ρ γ) ∈ Ψ := hρ _ hγ1
    have h1 : S.ρ (v • (S.ρ γ)) = z • (S.ρ (S.ρ γ)) := by
      have h := hzv (S.ρ (S.ρ γ)) hγ2
      rwa [Equiv.symm_apply_apply] at h
    have h2 : S.ρ (S.ρ γ) = w • γ := hwv γ hγ
    calc S.rhoTwist v (S.rhoTwist v γ)
        = v • (S.ρ (v • (S.ρ γ))) := by rw [S.rhoTwist_apply, S.rhoTwist_apply]
      _ = v • (z • (S.ρ (S.ρ γ))) := by rw [h1]
      _ = v • (z • (w • γ)) := by rw [h2]
      _ = (v * z * w) • γ := by rw [mul_smul, mul_smul]
  have hpos2 : ∀ β ∈ simpleRoots Ψ, (v * z * w) • β ∈ posRoots Ψ := by
    intro β hβ
    rw [← hmap β (simpleRoots_subset hβ)]
    exact hpos _ (hpos β (simpleRoot_mem_posRoots hβ))
  have h1 : v * z * w = 1 := by
    by_contra hne
    obtain ⟨β, hβ, hneg⟩ := exists_smul_mem_negRoots hΨ (mul_mem (mul_mem hv hz) hwcomp) hne
    exact not_mem_negRoots_of_mem_posRoots (hpos2 β hβ) hneg
  intro γ hγ
  rw [hmap γ hγ, h1, one_smul]

theorem twistInner_iterate_two_of_twistKind_twoD {τ : Tag} {L : Type} [Field L]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {i : KernelComponent χ} (hkind : twistKind ρ χ i = .twoD)
    (hs : componentOrbitLength ρ (componentRoots χ i) = 1)
    (hr : compRank (componentRoots χ i) = 4) :
    twistInner (componentRoots χ i) ((ρ : (Fin τ.rank → ℤ) → _)^[2]) := by
  have h := hkind
  unfold twistKind at h
  rw [hs, Function.iterate_one, Nat.mul_one] at h
  split_ifs at h with h1 h2 h3
  by_contra hcon
  have h24 : (componentRoots χ i).ncard = 24 := by
    rw [h3.2, hr]
  exact h2 (Or.inr ⟨hr, h24, hcon⟩)

theorem exists_rhoTwist_rankFour {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ) (hni : ¬ twistInner Ψ S.ρ) :
    ∃ v ∈ componentWeylGroup Ψ,
      (∀ γ ∈ Ψ, S.rhoTwist v γ ∈ Ψ) ∧
      (∀ γ ∈ posRoots Ψ, S.rhoTwist v γ ∈ posRoots Ψ) ∧
      ∃ β ∈ simpleRoots Ψ, S.rhoTwist v β ≠ β := by
  classical
  have hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ h => hst.subset (Set.mem_image_of_mem _ h)
  have hρs : ∀ γ ∈ Ψ, S.ρ.symm γ ∈ Ψ := fun γ h => Set.mem_image_equiv.1 (hst.symm.subset h)
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry Ψ S.ρ.symm := by
    refine ⟨⟨hρs, S.ρ.symm.injective.injOn, fun γ hγ => ?_⟩, fun γ _ δ _ => ?_,
      fun γ _ => ?_⟩
    · exact ⟨S.ρ γ, hρ γ hγ, Equiv.symm_apply_apply _ _⟩
    · have h := iform_rho S (S.ρ.symm γ) (S.ρ.symm δ)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    · apply S.ρ.injective
      rw [Equiv.apply_symm_apply, S.frob.neg_eq, Equiv.apply_symm_apply]
  obtain ⟨u, hu, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hg := hf.comp_smul hΨ hu
  have hv : u⁻¹ ∈ componentWeylGroup Ψ := inv_mem hu
  have hδg : ∀ γ, S.rhoTwist u⁻¹ (S.ρ.symm (u • γ)) = γ := fun γ => by
    rw [S.rhoTwist_apply, Equiv.apply_symm_apply, inv_smul_smul]
  have hmaps : ∀ γ ∈ Ψ, S.rhoTwist u⁻¹ γ ∈ Ψ := fun γ hγ =>
    smul_mem_of_mem_componentWeylGroup hΨ hv _ (hρ γ hγ)
  have hposδ : ∀ γ ∈ posRoots Ψ, S.rhoTwist u⁻¹ γ ∈ posRoots Ψ := by
    intro γ hγ
    obtain ⟨b, hb, rfl⟩ := hg.exists_posRoots hΨ hpos hγ
    rw [hδg]
    exact hb
  have hiso := S.iform_rhoTwist u⁻¹
  have hinj := injective_of_iform _ hiso
  have hfδ : IsIsometry Ψ (S.rhoTwist u⁻¹) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ _ => hiso γ δ,
      fun γ _ => map_neg _ γ⟩
  have hne : ∃ β ∈ simpleRoots Ψ, S.rhoTwist u⁻¹ β ≠ β := by
    by_contra h
    push Not at h
    apply hni
    refine ⟨u, componentWeylGroup_le Ψ hu, fun γ hγ => ?_⟩
    have h1 := hfδ.eq_self_of_simpleRoots hΨ h hγ
    rw [S.rhoTwist_apply] at h1
    calc S.ρ γ = u • (u⁻¹ • S.ρ γ) := by rw [smul_inv_smul]
      _ = u • γ := by rw [h1]
  exact ⟨u⁻¹, hv, hmaps, hposδ, hne⟩

theorem eq_D4_of_mem_countTypes {t : DynkinType} (hmem : t ∈ countTypes)
    (hrank : t.rank = 4) (hroots : t.numRoots = 24) : t = .D 4 := by
  simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [DynkinType.numRoots]

theorem exists_graphCoordinates_of_rankFour {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (hrank : compRank Ψ = 4)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hinvol : ∀ γ ∈ Ψ, δ (δ γ) = γ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) :
    ∃ (e : simpleRoots Ψ ≃ Fin 4) (σ : Equiv.Perm (Fin 4)),
      (∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
        CartanMatrix.D 4 (e β) (e γ)) ∧
      (∀ j : Fin 4, δ (e.symm j) = e.symm (σ j)) ∧
      (∀ i j : Fin 4, d4Fun (σ i) (σ j) = d4Fun i j) ∧
      (∀ i : Fin 4, σ (σ i) = i) ∧ σ ≠ 1 := by
  classical
  have hsl' : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => hsl β (simpleRoots_subset hβ)
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hinj := injective_of_iform δ hiso
  have hf : IsIsometry Ψ δ :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg δ γ⟩
  obtain ⟨β₀, hβ₀, hδβ₀⟩ := hne
  have hΨne : Ψ.Nonempty := ⟨β₀, simpleRoots_subset hβ₀⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank' : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcardΔ]
  have hr8 : t.rank ≤ 8 := hrank' ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨δ (β : Fin τ.rank → ℤ), hf.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := fun β γ h => Subtype.ext (hinj (congrArg Subtype.val h))
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσdef
  have hσ : ∀ j, δ (e.symm j) = e.symm (σ j) := fun j => by
    rw [hσdef]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hπe, Equiv.ofBijective_apply, hπ]
  have hσM : ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j := by
    intro i j
    have h1 := he' (e.symm (σ i)) (e.symm (σ j))
    have h2 := he' (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hσ, ← hσ]
    exact corootPair_isometry hf (simpleRoots_subset (e.symm i).2)
      (simpleRoots_subset (e.symm j).2)
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 := hσ (e ⟨β₀, hβ₀⟩)
    rw [h1, Equiv.Perm.one_apply, Equiv.symm_apply_apply] at h2
    exact hδβ₀ h2
  have hσ2 : ∀ j, σ (σ j) = j := by
    intro j
    have h1 := hinvol (e.symm j) (simpleRoots_subset (e.symm j).2)
    rw [hσ j, hσ (σ j)] at h1
    exact e.symm.injective (Subtype.ext h1)
  have hcount : t ∈ countTypes := by
    rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
    · exact absurd (eq_one_of_sepB
        (List.all_eq_true.1 Certificates.certificate13659.1 t hmem) hσM) hσ1
    · exact hmem
  have hN : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he',
      ncard_orbit_of_orbitOK (List.all_eq_true.1 Certificates.certificate13659.2 t hcount)]
  have ht24 : t.numRoots = 24 := by
    rw [← hN, hcard, hrank]
  have htr : t.rank = 4 := by rw [← hrank', hrank]
  have htD : t = .D 4 := eq_D4_of_mem_countTypes hcount htr ht24
  subst htD
  let e4 : simpleRoots Ψ ≃ Fin 4 := e
  let σ4 : Equiv.Perm (Fin 4) := σ
  have he4 : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      CartanMatrix.D 4 (e4 β) (e4 γ) := by
    intro β γ
    rw [← DynkinType.cartanMatrix_D]
    exact he' β γ
  have hσ4 : ∀ j : Fin 4, δ (e4.symm j) = e4.symm (σ4 j) := hσ
  have hσM4 : ∀ i j : Fin 4, d4Fun (σ4 i) (σ4 j) = d4Fun i j := by
    intro i j
    have h := hσM i j
    rwa [DynkinType.cartanMatrix_D] at h
  have hσ24 : ∀ i : Fin 4, σ4 (σ4 i) = i := hσ2
  exact ⟨e4, σ4, he4, hσ4, hσM4, hσ24, hσ1⟩

theorem graphTwist_and_fixed_adj_of_rankFour {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (hrank : compRank Ψ = 4)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hinvol : ∀ γ ∈ Ψ, δ (δ γ) = γ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) : IsGraphTwist Ψ δ ∧
      ∀ beta ∈ simpleRoots Ψ, δ beta ≠ beta →
        ∃ beta' ∈ simpleRoots Ψ, δ beta' = beta' ∧ iform beta beta' = -1 := by
  obtain ⟨e4, σ4, he4, hσ4, hσM4, hσ24, hσ1⟩ :=
    exists_graphCoordinates_of_rankFour hΨ hsl hrank hcard δ hiso hmaps hpos hinvol hne
  have hsl' : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => hsl β (simpleRoots_subset hβ)
  have hAdj := exists_fixed_adj_of_d4_swap hsl' e4 he4 δ hσ4 hσM4 hσ24
  refine ⟨?_, hAdj⟩
  rcases d4_perm_cases hσM4 hσ24 with h1 | h1 | h1 | h1
  · exact absurd (Equiv.ext h1) hσ1
  · have hσeq : σ4 = Equiv.swap 0 2 := Equiv.ext h1
    rw [hσeq] at hσ4
    exact isGraphTwist_of_dGraphCheck (a := 0) (b := 2) hΨ hsl' e4 he4 (by decide) δ hσ4
      dGraphCheck_D4_zero_two
  · have hσeq : σ4 = Equiv.swap 0 3 := Equiv.ext h1
    rw [hσeq] at hσ4
    exact isGraphTwist_of_dGraphCheck (a := 0) (b := 3) hΨ hsl' e4 he4 (by decide) δ hσ4
      dGraphCheck_D4_zero_three
  · have hσeq : σ4 = Equiv.swap 2 3 := Equiv.ext h1
    rw [hσeq] at hσ4
    exact isGraphTwist_of_dGraphCheck (a := 2) (b := 3) hΨ hsl' e4 he4 (by decide) δ hσ4
      dGraphCheck_D4_two_three
theorem isGraphTwist_of_rankFour {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (hrank : compRank Ψ = 4)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hinvol : ∀ γ ∈ Ψ, δ (δ γ) = γ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) : IsGraphTwist Ψ δ :=
  (graphTwist_and_fixed_adj_of_rankFour hΨ hsl hrank hcard δ hiso hmaps hpos hinvol hne).1

theorem rankFourGraphTwist_holds : RankFourGraphTwist := by
  intro τ L _ _ _ p S a hT i hkind hrank hst hsl
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ h => hst.subset (Set.mem_image_of_mem _ h)
  have hs : componentOrbitLength S.ρ Ψ = 1 := componentOrbitLength_eq_one hfin hρ
  have hni : ¬ twistInner Ψ S.ρ := by
    have h := not_twistInner_of_twistKind_twoD_exc (Or.inl hkind)
    rw [hs, Function.iterate_one] at h
    exact h
  have hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1) :=
    (shape_of_twistKind_twoD hkind).2
  have hinner2 : twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[2]) :=
    twistInner_iterate_two_of_twistKind_twoD hkind hs hrank
  obtain ⟨v, hv, hmaps, hpos, hne⟩ := exists_rhoTwist_rankFour S hΨ hst hni
  have hinvol : ∀ γ ∈ Ψ, S.rhoTwist v (S.rhoTwist v γ) = γ :=
    rhoTwist_sq_eq_self S hΨ hst hinner2 hv hpos
  exact ⟨v, hv, hmaps, hpos,
    isGraphTwist_of_rankFour hΨ hsl hrank hcard (S.rhoTwist v) (S.iform_rhoTwist v) hmaps hpos
      hinvol hne⟩

theorem d4_graph_root_cases
    {τ : Tag} {Psi : Set (Fin τ.rank → ℤ)} (hPsi : IsRootComponent Psi)
    (hsl : ∀ beta ∈ simpleRoots Psi, iform beta beta = 2)
    (e : simpleRoots Psi ≃ Fin 4)
    (he : ∀ beta gamma : simpleRoots Psi,
      corootPair (beta : Fin τ.rank → ℤ) gamma = CartanMatrix.D 4 (e beta) (e gamma))
    (delta : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hiso : ∀ x y, iform (delta x) (delta y) = iform x y)
    (hmaps : ∀ gamma ∈ Psi, delta gamma ∈ Psi)
    (hpos : ∀ gamma ∈ posRoots Psi, delta gamma ∈ posRoots Psi) :
    ∀ gamma ∈ Psi,
      (delta gamma = gamma ∨
        (delta (delta gamma) = gamma ∧ iform gamma (delta gamma) = 0) ∨
        (delta (delta (delta gamma)) = gamma ∧ iform gamma (delta gamma) = 0 ∧
          iform gamma (delta (delta gamma)) = 0 ∧
          iform (delta gamma) (delta (delta gamma)) = 0)) ∧
      ∃ beta ∈ Psi, delta beta = beta ∧ iform gamma beta = -1 := by
  classical
  have hfin : Psi.Finite := (finite_setOf_isRoot τ).subset fun gamma hg => hPsi.isRoot gamma hg
  have hinj := injective_of_iform delta hiso
  have hf : IsIsometry Psi delta :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn,
      fun x _ y _ => hiso x y, fun gamma _ => map_neg delta gamma⟩
  let pi : simpleRoots Psi → simpleRoots Psi := fun beta =>
    ⟨delta (beta : Fin τ.rank → ℤ), hf.apply_mem_simpleRoots hPsi hpos beta.2⟩
  have hpi : Function.Bijective pi :=
    Finite.injective_iff_bijective.mp fun beta gamma h => Subtype.ext (hinj (congrArg Subtype.val h))
  let sigma : Equiv.Perm (Fin 4) := (e.symm.trans (Equiv.ofBijective pi hpi)).trans e
  have hSigma : ∀ j, delta (e.symm j) = e.symm (sigma j) := by
    intro j
    simp only [sigma, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.ofBijective_apply, pi]
  have hCartan : ∀ i j, CartanMatrix.D 4 (sigma i) (sigma j) = CartanMatrix.D 4 i j := by
    intro i j
    have h1 := he (e.symm (sigma i)) (e.symm (sigma j))
    have h2 := he (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hSigma, ← hSigma]
    exact corootPair_isometry hf (simpleRoots_subset (e.symm i).2) (simpleRoots_subset (e.symm j).2)
  let perm : (Fin 4 → ℤ) → (Fin 4 → ℤ) := fun x j => x (sigma.symm j)
  have hLift : ∀ x, delta (rootLift e x) = rootLift e (perm x) :=
    map_rootLift delta e hSigma
  have hForm : ∀ x y : Fin 4 → ℤ,
      iform (rootLift e x) (rootLift e y) = ∑ i, ∑ j, x i * CartanMatrix.D 4 i j * y j :=
    iform_rootLift hsl e he
  have hCartanInv : ∀ i j, CartanMatrix.D 4 (sigma.symm i) (sigma.symm j) = CartanMatrix.D 4 i j := by
    intro i j
    have h := hCartan (sigma.symm i) (sigma.symm j)
    simpa only [Equiv.apply_symm_apply] using h.symm
  have himg := image_rootLift_orbit hPsi e he
  intro gamma hg
  have hgImage : gamma ∈ (rootLift e) '' {x | IsOrbitRoot (CartanMatrix.D 4) x} := by
    exact himg.symm ▸ hg
  obtain ⟨x,hx,hgamma⟩ := hgImage
  have hlist := ofFn_mem_of_closedB d4_graph_root_list_closed hx
  have hcases := d4_graph_root_cases_list sigma.symm hCartanInv (List.ofFn x) hlist
  dsimp only at hcases
  simp only [ofList_ofFn] at hcases
  change ((∀ i, perm x i = x i) ∨
      ((∀ i, perm (perm x) i = x i) ∧ (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * perm x j) = 0) ∨
      ((∀ i, perm (perm (perm x)) i = x i) ∧
        (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * perm x j) = 0 ∧
        (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * perm (perm x) j) = 0 ∧
        (∑ i, ∑ j, perm x i * CartanMatrix.D 4 i j * perm (perm x) j) = 0)) ∧
      ∃ k ∈ d4_graph_roots,
        (∀ i, perm (ofList k) i = ofList (n := 4) k i) ∧
        (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * ofList k j) = -1 at hcases
  rcases hcases with ⟨hPeriod,hNeighbour⟩
  have hResult :
      (delta (rootLift e x) = rootLift e x ∨
        (delta (delta (rootLift e x)) = rootLift e x ∧
          iform (rootLift e x) (delta (rootLift e x)) = 0) ∨
        (delta (delta (delta (rootLift e x))) = rootLift e x ∧
          iform (rootLift e x) (delta (rootLift e x)) = 0 ∧
          iform (rootLift e x) (delta (delta (rootLift e x))) = 0 ∧
          iform (delta (rootLift e x)) (delta (delta (rootLift e x))) = 0)) ∧
      ∃ beta ∈ Psi, delta beta = beta ∧ iform (rootLift e x) beta = -1 := by
    refine ⟨?_,?_⟩
    · rcases hPeriod with hfix | ⟨h2,horth⟩ | ⟨h3,horth1,horth2,horth3⟩
      · left
        rw [hLift,funext hfix]
      · right;left
        rw [hLift,hLift,funext h2,hForm]
        exact ⟨rfl,horth⟩
      · right;right
        rw [hLift,hLift,hLift,funext h3,hForm,hForm,hForm]
        exact ⟨rfl,horth1,horth2,horth3⟩
    · obtain ⟨k,hk,hfix,hform⟩ := hNeighbour
      have hFixFun : perm (ofList k) = ofList (n := 4) k := by
        funext i
        exact hfix i
      have hk' : k ∈ orbitIter (CartanMatrix.D 4) 5 := d4_graph_roots_members_mem_orbit k hk
      obtain ⟨y,hy,hky⟩ := mem_orbitIter (CartanMatrix.D 4) 5 hk'
      have hkRoot : IsOrbitRoot (CartanMatrix.D 4) (ofList k) := by
        rw [hky,ofList_ofFn]
        exact hy
      refine ⟨rootLift e (ofList k),rootLift_mem hPsi e he hkRoot,?_,?_⟩
      · rw [hLift,hFixFun]
      · rw [hForm]
        exact hform
  simpa only [hgamma] using hResult

theorem d4_graph_root_cases_of_noninner
    {tau : Tag} {Psi : Set (Fin tau.rank → ℤ)} (hPsi : IsRootComponent Psi)
    (hsl : ∀ beta ∈ Psi, iform beta beta = 2)
    (hRank : compRank Psi = 4) (hCard : Psi.ncard = 24)
    (delta : (Fin tau.rank → ℤ) →+ (Fin tau.rank → ℤ))
    (hiso : ∀ x y, iform (delta x) (delta y) = iform x y)
    (hmaps : ∀ gamma ∈ Psi, delta gamma ∈ Psi)
    (hpos : ∀ gamma ∈ posRoots Psi, delta gamma ∈ posRoots Psi)
    (hni : ¬ twistInner Psi delta) :
    ∀ gamma ∈ Psi,
      (delta gamma = gamma ∨
        (delta (delta gamma) = gamma ∧ iform gamma (delta gamma) = 0) ∨
        (delta (delta (delta gamma)) = gamma ∧ iform gamma (delta gamma) = 0 ∧
          iform gamma (delta (delta gamma)) = 0 ∧
          iform (delta gamma) (delta (delta gamma)) = 0)) ∧
      ∃ beta ∈ Psi, delta beta = beta ∧ iform gamma beta = -1 := by
  classical
  have hfin : Psi.Finite := (finite_setOf_isRoot tau).subset fun gamma hg => hPsi.isRoot gamma hg
  have hinj := injective_of_iform delta hiso
  have hf : IsIsometry Psi delta :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn,
      fun x _ y _ => hiso x y, fun gamma _ => map_neg delta gamma⟩
  have hD : Psi.ncard = 2 * compRank Psi * (compRank Psi - 1) := by rw [hRank,hCard]
  obtain ⟨r,hr,e,he⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_cartanD_of_nonInner
    hPsi delta hf.bijOn hf.iform_eq hf.neg hni (by omega) hD
  have hrank : compRank Psi = r := by
    rw [compRank_eq_card hPsi, ← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hr4 : r = 4 := hrank.symm.trans hRank
  subst hr4
  have hCartan : ∀ beta gamma : simpleRoots Psi,
      corootPair (beta : Fin tau.rank → ℤ) gamma = CartanMatrix.D 4 (e beta) (e gamma) := by
    simpa only [CFSG.LieType.Universal.Spin.cartanD_eq] using he
  exact d4_graph_root_cases hPsi (fun beta hb => hsl beta (simpleRoots_subset hb))
    e hCartan delta hiso hmaps hpos


end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
