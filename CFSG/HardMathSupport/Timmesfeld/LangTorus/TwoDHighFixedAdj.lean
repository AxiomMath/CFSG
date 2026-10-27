module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDatum
public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut TauCeti

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)} {δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)}

private theorem exists_dynkinType_of_twoD (hΨ : IsRootComponent Ψ) (h5 : 5 ≤ compRank Ψ) :
    ∃ (t : DynkinType) (e : simpleRoots Ψ ≃ Fin t.rank),
      t.Valid ∧
        (∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
          t.cartanMatrix (e β) (e γ)) ∧
        compRank Ψ = t.rank ∧ t.rank ≤ 8 := by
  classical
  have hΨne : Ψ.Nonempty := by
    have hΔ : (simpleRoots Ψ).Nonempty := by
      refine Finset.card_pos.1 ?_
      rw [← compRank_eq_card hΨ]
      omega
    exact hΔ.imp fun β hβ => simpleRoots_subset hβ
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (Proving.isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (Proving.diagramGraph_simpleRoots_connected hΨ hΨne)
  have hrank : compRank Ψ = t.rank := by
    rw [compRank_eq_card hΨ, ← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  refine ⟨t, e, ht, fun β γ => ?_, hrank, ?_⟩
  · simpa only [Matrix.of_apply] using he β γ
  · rw [← hrank]
    exact (compRank_le Ψ).trans (rank_le_eight τ)

private theorem exists_perm_of_twoD (hΨ : IsRootComponent Ψ)
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y) (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ)
    (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β)
    {t : DynkinType} {e : simpleRoots Ψ ≃ Fin t.rank}
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ)) :
    ∃ σ : Equiv.Perm (Fin t.rank),
      (∀ j, δ (e.symm j) = e.symm (σ j)) ∧
      (∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j) ∧ σ ≠ 1 := by
  classical
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hinj := injective_of_iform δ hiso
  have hf : IsIsometry Ψ δ :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg δ γ⟩
  obtain ⟨β₀, hβ₀, hδβ₀⟩ := hne
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
    have h1 := he (e.symm (σ i)) (e.symm (σ j))
    have h2 := he (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hσ, ← hσ]
    exact corootPair_isometry hf (simpleRoots_subset (e.symm i).2)
      (simpleRoots_subset (e.symm j).2)
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 := hσ (e ⟨β₀, hβ₀⟩)
    rw [h1, Equiv.Perm.one_apply, Equiv.symm_apply_apply] at h2
    exact hδβ₀ h2
  exact ⟨σ, hσ, hσM, hσ1⟩

private theorem exists_fixed_adj_of_fork (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2)
    {t : DynkinType} {e : simpleRoots Ψ ≃ Fin t.rank}
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ))
    {σ : Equiv.Perm (Fin t.rank)} (hσ : ∀ j, δ (e.symm j) = e.symm (σ j))
    (hσM : ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j) (hσ1 : σ ≠ 1)
    {N : ℕ} {a b c₀ : Fin t.rank} (hab : a ≠ b) (hca : c₀ ≠ a) (hcb : c₀ ≠ b)
    (hchk : dGraphOK t.cartanMatrix a b N = true)
    (hac : t.cartanMatrix a c₀ = -1) (hbc : t.cartanMatrix b c₀ = -1) :
    ∀ β ∈ simpleRoots Ψ, δ β ≠ β →
      ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform β β' = -1 := by
  have hsw : ∀ j, δ (e.symm j) = e.symm (Equiv.swap a b j) := by
    intro j
    obtain ⟨-, -, hsep, -⟩ := dGraphOK_spec hchk
    rw [hσ, (eq_one_or_eq_swap_of_sepPairB hsep hab hσM).resolve_left hσ1]
  intro β hβ hβm
  refine ⟨e.symm c₀, (e.symm c₀).2, ?_, ?_⟩
  · rw [hsw c₀, Equiv.swap_apply_of_ne_of_ne hca hcb]
  · let j : Fin t.rank := e ⟨β, hβ⟩
    have hβj : (e.symm j : Fin τ.rank → ℤ) = β := by
      change (e.symm (e ⟨β, hβ⟩) : Fin τ.rank → ℤ) = β
      simpa using congrArg Subtype.val (Equiv.symm_apply_apply e ⟨β, hβ⟩)
    have hmoved : Equiv.swap a b j ≠ j := by
      intro heq
      apply hβm
      calc δ β = δ (e.symm j) := by rw [hβj]
        _ = e.symm (Equiv.swap a b j) := hsw j
        _ = e.symm j := by rw [heq]
        _ = β := hβj
    have hjab : j = a ∨ j = b := by
      by_contra h
      push Not at h
      exact hmoved (Equiv.swap_apply_of_ne_of_ne h.1 h.2)
    have h := iform_rootLift hsl e he (Pi.single j 1) (Pi.single c₀ 1)
    rw [rootLift_single, rootLift_single, hβj] at h
    rw [h]
    rcases hjab with hja | hjb
    · rw [hja]
      simpa [Pi.single_apply] using hac
    · rw [hjb]
      simpa [Pi.single_apply] using hbc

private theorem cartanD_fork_adj :
    ((DynkinType.D 5).cartanMatrix (⟨3, by decide⟩ : Fin 5) ⟨2, by decide⟩ = -1 ∧
      (DynkinType.D 5).cartanMatrix (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ = -1) ∧
    ((DynkinType.D 6).cartanMatrix (⟨4, by decide⟩ : Fin 6) ⟨3, by decide⟩ = -1 ∧
      (DynkinType.D 6).cartanMatrix (⟨5, by decide⟩ : Fin 6) ⟨3, by decide⟩ = -1) ∧
    ((DynkinType.D 7).cartanMatrix (⟨5, by decide⟩ : Fin 7) ⟨4, by decide⟩ = -1 ∧
      (DynkinType.D 7).cartanMatrix (⟨6, by decide⟩ : Fin 7) ⟨4, by decide⟩ = -1) ∧
    ((DynkinType.D 8).cartanMatrix (⟨6, by decide⟩ : Fin 8) ⟨5, by decide⟩ = -1 ∧
      (DynkinType.D 8).cartanMatrix (⟨7, by decide⟩ : Fin 8) ⟨5, by decide⟩ = -1) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [DynkinType.cartanMatrix_D, ← CFSG.LieType.Universal.Spin.cartanD_eq,
      CFSG.Timmesfeld.LevisSpin.cartanD_apply] <;>
    decide

private theorem exists_fixed_adj_of_countType
    (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2)
    {t : DynkinType} {e : simpleRoots Ψ ≃ Fin t.rank}
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ))
    {σ : Equiv.Perm (Fin t.rank)} (hσ : ∀ j, δ (e.symm j) = e.symm (σ j))
    (hσM : ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j) (hσ1 : σ ≠ 1)
    (hmem : t ∈ countTypes) (h5t : 5 ≤ t.rank)
    (hcardt : t.numRoots = 2 * t.rank * (t.rank - 1)) :
    ∀ β ∈ simpleRoots Ψ, δ β ≠ β →
      ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform β β' = -1 := by
  simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate13660
  obtain ⟨⟨h51, h52⟩, ⟨h61, h62⟩, ⟨h71, h72⟩, ⟨h81, h82⟩⟩ := cartanD_fork_adj
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h5t (by decide)
  · exact absurd h5t (by decide)
  · exact absurd h5t (by decide)
  · exact absurd hcardt (by decide)
  · exact absurd hcardt (by decide)
  · exact absurd hcardt (by decide)
  · exact absurd hcardt (by decide)
  · exact absurd h5t (by decide)
  · exact exists_fixed_adj_of_fork hsl he hσ hσM hσ1
      (N := 40) (a := ⟨3, by decide⟩) (b := ⟨4, by decide⟩) (c₀ := ⟨2, by decide⟩)
      (by decide) (by decide) (by decide) h1 h51 h52
  · exact exists_fixed_adj_of_fork hsl he hσ hσM hσ1
      (N := 60) (a := ⟨4, by decide⟩) (b := ⟨5, by decide⟩) (c₀ := ⟨3, by decide⟩)
      (by decide) (by decide) (by decide) h2 h61 h62
  · exact exists_fixed_adj_of_fork hsl he hσ hσM hσ1
      (N := 84) (a := ⟨5, by decide⟩) (b := ⟨6, by decide⟩) (c₀ := ⟨4, by decide⟩)
      (by decide) (by decide) (by decide) h3 h71 h72
  · exact exists_fixed_adj_of_fork hsl he hσ hσM hσ1
      (N := 112) (a := ⟨6, by decide⟩) (b := ⟨7, by decide⟩) (c₀ := ⟨5, by decide⟩)
      (by decide) (by decide) (by decide) h4 h81 h82
  · exact absurd hcardt (by decide)

theorem exists_fixed_adj_of_twoD
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (h5 : 5 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) :
    ∀ β ∈ simpleRoots Ψ, δ β ≠ β →
      ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform β β' = -1 := by
  classical
  obtain ⟨t, e, ht, he, hrank, hr8⟩ := exists_dynkinType_of_twoD hΨ h5
  obtain ⟨σ, hσ, hσM, hσ1⟩ := exists_perm_of_twoD hΨ hiso hmaps hpos hne he
  have hsl' : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => hsl β (simpleRoots_subset hβ)
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · exact absurd (eq_one_of_sepB
      (List.all_eq_true.1 Certificates.certificate13659.1 t hmem) hσM) hσ1
  have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
  have hncard : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he, ncard_orbit_of_orbitOK hok]
  have hcardt : t.numRoots = 2 * t.rank * (t.rank - 1) := by
    rw [← hncard, ← hrank]
    exact hcard
  have h5t : 5 ≤ t.rank := by rw [← hrank]; exact h5
  exact exists_fixed_adj_of_countType hsl' he hσ hσM hσ1 hmem h5t hcardt

section Certificates


theorem IsGraphTwist.adj_all (hG : IsGraphTwist Ψ δ)
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y) (hΨ : IsRootComponent Ψ)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ)
    (hN : ∀ β ∈ simpleRoots Ψ, δ β ≠ β →
      ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform β β' = -1)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    ∃ γ' ∈ Ψ, δ γ' = γ' ∧ iform γ γ' = -1 := by
  classical
  obtain ⟨w, hw, hwγ⟩ := hG.reach γ hγ
  have hwbig : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
    have hle : Subgroup.closure {g : WeylGroup τ | ∃ β ∈ simpleRoots Ψ,
        g = setReflection ({β, δ β} : Set (Fin τ.rank → ℤ))} ≤
        Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
      rw [Subgroup.closure_le]
      rintro g ⟨β, hβ, rfl⟩
      have hβΨ := simpleRoots_subset hβ
      by_cases hfix : δ β = β
      · rw [hfix, Set.pair_eq_singleton, setReflection_singleton]
        exact Subgroup.subset_closure (show rootReflection β ∈
          {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} from ⟨β, hβΨ, rfl⟩)
      · rw [setReflection_pair (simpleRoots_isRoot hβ) (hΨ.isRoot _ (hmaps β hβΨ))
          (Ne.symm hfix) (hG.orth β hβΨ hfix)]
        exact mul_mem
          (Subgroup.subset_closure (show rootReflection β ∈
            {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} from ⟨β, hβΨ, rfl⟩))
          (Subgroup.subset_closure (show rootReflection (δ β) ∈
            {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}
              from ⟨δ β, hmaps β hβΨ, rfl⟩))
    exact hle hw
  have hwsm : ∀ x : Fin τ.rank → ℤ, w • x ∈ Ψ ↔ x ∈ Ψ := outer_smul_mem_iff hΨ hwbig
  obtain ⟨β', hβ'Δ, hfixβ', hadj⟩ :
      ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform (w • γ) β' = -1 := by
    by_cases hfixw : δ (w • γ) = w • γ
    · exact hG.adj _ hwγ hfixw
    · exact hN _ hwγ hfixw
  refine ⟨w⁻¹ • β', ?_, ?_, ?_⟩
  · have h := (hwsm (w⁻¹ • β')).1
    rw [smul_inv_smul] at h
    exact h (simpleRoots_subset hβ'Δ)
  · have h := smul_comm_of_mem_closure hG hΨ hiso hmaps (inv_mem hw) β'
    rw [hfixβ'] at h
    exact h.symm
  · rw [← iform_smul w γ (w⁻¹ • β'), smul_inv_smul]
    exact hadj

theorem IsGraphTwist.root_facts (hG : IsGraphTwist Ψ δ)
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y) (hΨ : IsRootComponent Ψ)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ)
    (hN : ∀ β ∈ simpleRoots Ψ, δ β ≠ β →
      ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform β β' = -1) :
    (∀ γ ∈ Ψ, δ (δ γ) = γ) ∧
      (∀ γ ∈ Ψ, δ γ ≠ γ → iform γ (δ γ) = 0) ∧
      (∀ γ ∈ Ψ, δ γ = γ → ∃ γ' ∈ Ψ, δ γ' = γ' ∧ iform γ γ' = -1) ∧
      ∀ γ ∈ Ψ, δ γ ≠ γ → ∃ γ' ∈ Ψ, δ γ' = γ' ∧ iform γ γ' = -1 :=
  ⟨hG.invol, hG.orth, fun γ hγ _ => hG.adj_all hiso hΨ hmaps hN hγ,
    fun γ hγ _ => hG.adj_all hiso hΨ hmaps hN hγ⟩

end Certificates

theorem eq_of_eq_on_simpleRoots (hΨ : IsRootComponent Ψ)
    (hfix : ∀ β ∈ simpleRoots Ψ, δ β = β) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    δ γ = γ := by
  obtain ⟨c, e⟩ := exists_coords hΨ hγ
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [map_zsmul, hfix β hβ]

theorem exists_simpleRoot_ne_of_exists_ne (hΨ : IsRootComponent Ψ)
    (h : ∃ γ ∈ Ψ, δ γ ≠ γ) : ∃ β ∈ simpleRoots Ψ, δ β ≠ β := by
  by_contra hcon
  push Not at hcon
  obtain ⟨γ, hγ, hne⟩ := h
  exact hne (eq_of_eq_on_simpleRoots hΨ hcon hγ)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
