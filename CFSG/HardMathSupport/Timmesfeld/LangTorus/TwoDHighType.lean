module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import Certificates.Certificate13660

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut TauCeti

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}

theorem rootLift_eq_sum (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) :
    rootLift e x = ∑ j, x j • (e.symm j : Fin τ.rank → ℤ) := by
  rw [rootLift, ← Finset.sum_coe_sort (simpleRoots Ψ), ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [liftCoeff]

theorem map_rootLift (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (e : simpleRoots Ψ ≃ Fin n)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ j, δ (e.symm j) = e.symm (σ j)) (x : Fin n → ℤ) :
    δ (rootLift e x) = rootLift e (fun j => x (σ.symm j)) := by
  rw [rootLift_eq_sum, rootLift_eq_sum, map_sum]
  simp only [map_zsmul, hσ]
  exact Fintype.sum_equiv σ _ _ fun i => by rw [Equiv.symm_apply_apply]

theorem iform_rootLift (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2) (e : simpleRoots Ψ ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    (x y : Fin n → ℤ) :
    iform (rootLift e x) (rootLift e y) = ∑ i, ∑ j, x i * M i j * y j := by
  rw [rootLift_eq_sum, rootLift_eq_sum, iform_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iform_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : iform (e.symm i : Fin τ.rank → ℤ) (e.symm j) = M i j := by
    have h := he (e.symm i) (e.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h, corootPair, hsl _ (e.symm i).2]
    omega
  rw [h1]
  ring

structure IsGraphTwist (Ψ : Set (Fin τ.rank → ℤ)) (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) :
    Prop where
  invol : ∀ γ ∈ Ψ, δ (δ γ) = γ
  orth : ∀ γ ∈ Ψ, δ γ ≠ γ → iform γ (δ γ) = 0
  reach : ∀ γ ∈ Ψ, ∃ w ∈ Subgroup.closure {g : WeylGroup τ | ∃ β ∈ simpleRoots Ψ,
    g = setReflection ({β, δ β} : Set (Fin τ.rank → ℤ))}, w • γ ∈ simpleRoots Ψ
  adj : ∀ β ∈ simpleRoots Ψ, δ β = β →
    ∃ β' ∈ simpleRoots Ψ, δ β' = β' ∧ iform β β' = -1

theorem setReflection_singleton (β : Fin τ.rank → ℤ) :
    setReflection ({β} : Set (Fin τ.rank → ℤ)) = rootReflection β := by
  rw [setReflection_eq_list_prod (Set.finite_singleton β) (Set.pairwise_singleton _ _)
    (List.nodup_singleton β) (fun γ => by simp)]
  simp

theorem setReflection_pair {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hne : β ≠ γ) (h0 : iform β γ = 0) :
    setReflection ({β, γ} : Set (Fin τ.rank → ℤ)) = rootReflection β * rootReflection γ := by
  have hc := commute_rootReflection_of_iform_eq_zero hβ hγ h0
  have hpw : ({β, γ} : Set (Fin τ.rank → ℤ)).Pairwise
      fun x y => Commute (rootReflection x) (rootReflection y) := by
    rw [Set.pairwise_pair]
    exact fun _ => ⟨hc, hc.symm⟩
  rw [setReflection_eq_list_prod (Set.toFinite _) hpw (l := [β, γ]) (by simp [hne])
    (fun x => by simp)]
  simp

section Generic

variable (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2)
  (e : simpleRoots Ψ ≃ Fin n) {M : Matrix (Fin n) (Fin n) ℤ}
  (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
  {a b : Fin n} (hab : a ≠ b) (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
  (hσ : ∀ j, δ (e.symm j) = e.symm (Equiv.swap a b j))

include hsl he hab hσ

theorem exists_smul_of_isFoldReach (hMab : M a b = 0) {x : Fin n → ℤ}
    (hx : IsFoldReach M a b x) :
    ∃ w ∈ Subgroup.closure {g : WeylGroup τ | ∃ β ∈ simpleRoots Ψ,
      g = setReflection ({β, δ β} : Set (Fin τ.rank → ℤ))},
      ∃ j, rootLift e x = w • (e.symm j : Fin τ.rank → ℤ) := by
  induction hx with
  | single i => exact ⟨1, one_mem _, i, by rw [rootLift_single, one_smul]⟩
  | pair _ ih =>
    obtain ⟨w, hw, j, hj⟩ := ih
    have ha := simpleRoots_isRoot (e.symm a).2
    have hb := simpleRoots_isRoot (e.symm b).2
    have hne : (e.symm a : Fin τ.rank → ℤ) ≠ e.symm b := fun h =>
      hab (e.symm.injective (Subtype.ext h))
    have h0 : iform (e.symm a : Fin τ.rank → ℤ) (e.symm b) = 0 := by
      have h := iform_rootLift hsl e he (Pi.single a 1) (Pi.single b 1)
      rw [rootLift_single, rootLift_single] at h
      rw [h]
      simp [Pi.single_apply, hMab]
    have hδa : δ (e.symm a) = e.symm b := by rw [hσ, Equiv.swap_apply_left]
    refine ⟨setReflection ({(e.symm a : Fin τ.rank → ℤ), δ (e.symm a)} : Set _) * w,
      mul_mem (Subgroup.subset_closure ⟨_, (e.symm a).2, rfl⟩) hw, j, ?_⟩
    rw [hδa, setReflection_pair ha hb hne h0, rootLift_coordReflect e he,
      rootLift_coordReflect e he, hj, mul_smul, mul_smul]
  | one i hia hib _ ih =>
    obtain ⟨w, hw, j, hj⟩ := ih
    have hδi : δ (e.symm i) = e.symm i := by rw [hσ, Equiv.swap_apply_of_ne_of_ne hia hib]
    refine ⟨setReflection ({(e.symm i : Fin τ.rank → ℤ), δ (e.symm i)} : Set _) * w,
      mul_mem (Subgroup.subset_closure ⟨_, (e.symm i).2, rfl⟩) hw, j, ?_⟩
    rw [hδi, Set.pair_eq_singleton, setReflection_singleton, rootLift_coordReflect e he, hj,
      mul_smul]

include hΨ in
theorem isGraphTwist_of_dGraphOK {N : ℕ} (hchk : dGraphOK M a b N = true) :
    IsGraphTwist Ψ δ := by
  obtain ⟨hcl, -, -, hMab, horth, hreach, hadj⟩ := dGraphOK_spec hchk
  have himg := image_rootLift_orbit hΨ e he
  have hlift : ∀ x : Fin n → ℤ, δ (rootLift e x) =
      rootLift e (fun j => x (Equiv.swap a b j)) := fun x => by
    rw [map_rootLift δ e hσ x, Equiv.symm_swap]
  have hmem : ∀ γ ∈ Ψ, ∃ x, IsOrbitRoot M x ∧ rootLift e x = γ := by
    intro γ hγ
    rw [← himg] at hγ
    exact hγ
  refine ⟨fun γ hγ => ?_, fun γ hγ hne => ?_, fun γ hγ => ?_, fun β hβ hfix => ?_⟩
  · obtain ⟨x, -, rfl⟩ := hmem γ hγ
    rw [hlift, hlift]
    simp only [Equiv.swap_apply_self]
  · obtain ⟨x, hx, rfl⟩ := hmem γ hγ
    rw [hlift] at hne ⊢
    have hne' : (fun j => x (Equiv.swap a b j)) ≠ x := fun h => hne (by rw [h])
    rw [iform_rootLift hsl e he]
    exact form_swap_eq_zero_of_orthOK horth (ofFn_mem_of_closedB hcl hx) hne'
  · obtain ⟨x, hx, rfl⟩ := hmem γ hγ
    have hfr := isFoldReach_of_reachOK hreach (ofFn_mem_of_closedB hcl hx)
    obtain ⟨w, hw, j, hj⟩ := exists_smul_of_isFoldReach hsl e he hab δ hσ hMab hfr
    refine ⟨w⁻¹, inv_mem hw, ?_⟩
    rw [hj, inv_smul_smul]
    exact (e.symm j).2
  · set i := e ⟨β, hβ⟩ with hi
    have hβi : (e.symm i : Fin τ.rank → ℤ) = β := by rw [hi, Equiv.symm_apply_apply]
    have hia : i ≠ a := by
      rintro rfl
      have h := hσ i
      rw [Equiv.swap_apply_left, hβi, hfix] at h
      exact hab (e.symm.injective (Subtype.ext (hβi.trans h)))
    have hib : i ≠ b := by
      rintro rfl
      have h := hσ i
      rw [Equiv.swap_apply_right, hβi, hfix] at h
      exact hab (e.symm.injective (Subtype.ext (hβi.trans h).symm))
    obtain ⟨j, hja, hjb, hM⟩ := exists_adj_of_adjOK hadj hia hib
    refine ⟨e.symm j, (e.symm j).2, by rw [hσ, Equiv.swap_apply_of_ne_of_ne hja hjb], ?_⟩
    have h := iform_rootLift hsl e he (Pi.single i 1) (Pi.single j 1)
    rw [rootLift_single, rootLift_single, hβi] at h
    rw [h]
    simp [Pi.single_apply, hM]

end Generic

theorem injective_of_iform (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y) : Function.Injective δ := by
  intro x y h
  have h0 : iform (x - y) (x - y) = 0 := by
    rw [← hiso, map_sub, h, sub_self]
    exact iform_self_eq_zero_of_zero
  exact sub_eq_zero.1 (eq_zero_of_iform_self_eq_zero h0)

theorem isGraphTwist_of_twoD
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (h5 : 5 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) : IsGraphTwist Ψ δ := by
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
  have key : ∀ {N : ℕ} {a b : Fin t.rank}, a ≠ b → dGraphOK t.cartanMatrix a b N = true →
      IsGraphTwist Ψ δ := by
    intro N a b hab hchk
    obtain ⟨-, -, hsep, -⟩ := dGraphOK_spec hchk
    have hsw := (eq_one_or_eq_swap_of_sepPairB hsep hab hσM).resolve_left hσ1
    exact isGraphTwist_of_dGraphOK hΨ hsl' e he' hab δ (fun j => by rw [hσ, hsw]) hchk
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
  · exact key (by decide) h1
  · exact key (by decide) h2
  · exact key (by decide) h3
  · exact key (by decide) h4
  · exact absurd hcard (by decide)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
