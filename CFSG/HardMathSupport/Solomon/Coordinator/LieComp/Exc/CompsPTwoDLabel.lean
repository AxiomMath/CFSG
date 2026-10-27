module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Timmesfeld.LangTorus TauCeti

namespace CompsPTwoDLabel

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)}

@[expose] def IsForkLabelling (Ψ : Set (Fin τ.rank → ℤ))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) {m : ℕ} (e : simpleRoots Ψ ≃ Fin m) : Prop :=
  (∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      CFSG.LieType.Universal.Spin.cartanD m (e β) (e γ)) ∧
    (∀ j : Fin m, j.val + 2 < m → δ (e.symm j) = e.symm j) ∧
    (∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      δ (e.symm a) = e.symm b ∧ δ (e.symm b) = e.symm a)

theorem isForkLabelling_of_swap {δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)} {m : ℕ}
    (e : simpleRoots Ψ ≃ Fin m)
    (hM : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      CFSG.LieType.Universal.Spin.cartanD m (e β) (e γ)) (a b : Fin m) (ha : a.val + 2 = m)
    (hb : b.val + 1 = m) (hσ : ∀ j, δ (e.symm j) = e.symm (Equiv.swap a b j)) :
    IsForkLabelling Ψ δ e := by
  have hab : a ≠ b := fun h => by rw [h] at ha; omega
  refine ⟨hM, fun j hj => ?_, fun a' b' ha' hb' => ?_⟩
  · rw [hσ, Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => by rw [h] at hj; omega
    · exact fun h => by rw [h] at hj; omega
  · have h1 : a' = a := Fin.ext (by omega)
    have h2 : b' = b := Fin.ext (by omega)
    subst h1 h2
    exact ⟨by rw [hσ, Equiv.swap_apply_left], by rw [hσ, Equiv.swap_apply_right]⟩

theorem exists_labelling_twoD
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (h5 : 5 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) :
    ∃ (m : ℕ) (_ : 5 ≤ m) (e : simpleRoots Ψ ≃ Fin m), IsForkLabelling Ψ δ e := by
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
    (Proving.isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (Proving.diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcardΔ]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨δ (β : Fin τ.rank → ℤ), hf.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := fun β γ h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
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
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · exact absurd (eq_one_of_sepB
      (List.all_eq_true.1 Certificates.certificate13659.1 t hmem) hσM) hσ1
  have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
  have hN : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he', ncard_orbit_of_orbitOK hok]
  rw [hN, hrank] at hcard
  rw [hrank] at h5
  simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate13660
  have key : ∀ {r : ℕ} (hr : 5 ≤ r) {N : ℕ} (ee : simpleRoots Ψ ≃ Fin r)
      (hee : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
        (DynkinType.D r).cartanMatrix (ee β) (ee γ))
      (σ' : Equiv.Perm (Fin r)) (hσ' : ∀ j, δ (ee.symm j) = ee.symm (σ' j))
      (hσM' : ∀ i j, (DynkinType.D r).cartanMatrix (σ' i) (σ' j) =
        (DynkinType.D r).cartanMatrix i j) (hσ1' : σ' ≠ 1)
      (a b : Fin r), a.val + 2 = r → b.val + 1 = r →
        dGraphOK (DynkinType.D r).cartanMatrix a b N = true →
        ∃ (m : ℕ) (_ : 5 ≤ m) (e : simpleRoots Ψ ≃ Fin m), IsForkLabelling Ψ δ e := by
    intro r hr N ee hee σ' hσ' hσM' hσ1' a b ha hb hchk
    obtain ⟨-, -, hsep, -⟩ := dGraphOK_spec hchk
    have hab : a ≠ b := fun h => by rw [h] at ha; omega
    have hsw := (eq_one_or_eq_swap_of_sepPairB hsep hab hσM').resolve_left hσ1'
    refine ⟨r, hr, ee, isForkLabelling_of_swap ee ?_ a b ha hb (fun j => by rw [hσ', hsw]; rfl)⟩
    intro β γ
    rw [hee, DynkinType.cartanMatrix_D, ← CFSG.LieType.Universal.Spin.cartanD_eq]
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd h5 (by decide)
  · exact key (by norm_num) e he' σ hσ hσM hσ1 ⟨3, by decide⟩ ⟨4, by decide⟩ rfl rfl h1
  · exact key (by norm_num) e he' σ hσ hσM hσ1 ⟨4, by decide⟩ ⟨5, by decide⟩ rfl rfl h2
  · exact key (by norm_num) e he' σ hσ hσM hσ1 ⟨5, by decide⟩ ⟨6, by decide⟩ rfl rfl h3
  · exact key (by norm_num) e he' σ hσ hσM hσ1 ⟨6, by decide⟩ ⟨7, by decide⟩ rfl rfl h4
  · exact absurd hcard (by decide)

end CompsPTwoDLabel

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
