module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedConfig
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus TauCeti
  CFSG.RankThree.PartOne.KD4T

namespace Up34Chev2

section Cfg

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}

theorem D4Cfg.swap_ab {βa βb βk βc : Fin τ.rank → ℤ} (h : D4Cfg τ βa βb βk βc) :
    D4Cfg τ βb βa βk βc :=
  ⟨h.rb, h.ra, h.rk, h.rc, by rw [iform_comm]; exact h.ab, h.bk, h.ak, h.cb, h.ca, h.ck⟩

theorem exists_d4cfg_of_twoD
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (h5 : 5 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) :
    ∃ βa βb βk βc : Fin τ.rank → ℤ, βa ∈ simpleRoots Ψ ∧ βb ∈ simpleRoots Ψ ∧
      βk ∈ simpleRoots Ψ ∧ βc ∈ simpleRoots Ψ ∧ D4Cfg τ βa βb βk βc ∧ δ βa = βb ∧
      δ βb = βa ∧ δ βk = βk ∧ δ βc = βc := by
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
    (CFSG.HardMathSupport.Timmesfeld.Proving.isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hΨne)
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
  have hiform : ∀ x y : Fin t.rank, iform (e.symm x : Fin τ.rank → ℤ) (e.symm y) =
      t.cartanMatrix x y := by
    intro x y
    have h := he' (e.symm x) (e.symm y)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    have h2 := corootPair_mul (simpleRoots_isRoot (e.symm x).2) (e.symm y : Fin τ.rank → ℤ)
    rw [h, hsl' _ (e.symm x).2] at h2
    omega
  have key : ∀ {N : ℕ} {a b k c : Fin t.rank}, a ≠ b → dGraphOK t.cartanMatrix a b N = true →
      k ≠ a → k ≠ b → c ≠ a → c ≠ b → t.cartanMatrix a b = 0 → t.cartanMatrix a k = 0 →
      t.cartanMatrix b k = 0 → t.cartanMatrix c a = -1 → t.cartanMatrix c b = -1 →
      t.cartanMatrix c k = -1 →
      ∃ βa βb βk βc : Fin τ.rank → ℤ, βa ∈ simpleRoots Ψ ∧ βb ∈ simpleRoots Ψ ∧
        βk ∈ simpleRoots Ψ ∧ βc ∈ simpleRoots Ψ ∧ D4Cfg τ βa βb βk βc ∧ δ βa = βb ∧
        δ βb = βa ∧ δ βk = βk ∧ δ βc = βc := by
    intro N a b k c hab hchk hka hkb hca hcb h1 h2 h3 h4 h5 h6
    obtain ⟨-, -, hsep, -⟩ := dGraphOK_spec hchk
    have hsw := (eq_one_or_eq_swap_of_sepPairB hsep hab hσM).resolve_left hσ1
    refine ⟨e.symm a, e.symm b, e.symm k, e.symm c, (e.symm a).2, (e.symm b).2, (e.symm k).2,
      (e.symm c).2, ⟨simpleRoots_isRoot (e.symm a).2, simpleRoots_isRoot (e.symm b).2,
        simpleRoots_isRoot (e.symm k).2, simpleRoots_isRoot (e.symm c).2, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · rw [hiform]; exact h1
    · rw [hiform]; exact h2
    · rw [hiform]; exact h3
    · rw [hiform]; exact h4
    · rw [hiform]; exact h5
    · rw [hiform]; exact h6
    · rw [hσ, hsw, Equiv.swap_apply_left]
    · rw [hσ, hsw, Equiv.swap_apply_right]
    · rw [hσ, hsw, Equiv.swap_apply_of_ne_of_ne hka hkb]
    · rw [hσ, hsw, Equiv.swap_apply_of_ne_of_ne hca hcb]
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
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd h5 (by decide)
  · exact key (a := ⟨3, by decide⟩) (b := ⟨4, by decide⟩) (k := ⟨1, by decide⟩)
      (c := ⟨2, by decide⟩) (by decide) h1 (by decide) (by decide) (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact key (a := ⟨4, by decide⟩) (b := ⟨5, by decide⟩) (k := ⟨2, by decide⟩)
      (c := ⟨3, by decide⟩) (by decide) h2 (by decide) (by decide) (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact key (a := ⟨5, by decide⟩) (b := ⟨6, by decide⟩) (k := ⟨3, by decide⟩)
      (c := ⟨4, by decide⟩) (by decide) h3 (by decide) (by decide) (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact key (a := ⟨6, by decide⟩) (b := ⟨7, by decide⟩) (k := ⟨4, by decide⟩)
      (c := ⟨5, by decide⟩) (by decide) h4 (by decide) (by decide) (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact absurd hcard (by decide)

end Cfg

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
