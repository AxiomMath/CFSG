module

public import CFSG.HardMathSupport.C14IdxA2Cycle
public import CFSG.HardMathSupport.C14IdxOrbitA2
public import CFSG.HardMathSupport.C14IdxA2SumFree
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
import CFSG.HardMathSupport.C14IdxReeOrbitTools
public import CFSG.HardMathSupport.C14IdxRankOne

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)

private theorem iterate_mem_finset {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} {D : Finset (Fin τ.rank → ℤ)}
    (h : ∀ ⦃x⦄, x ∈ D → θ x ∈ D) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ D) (i : ℕ) :
    (⇑θ)^[i] γ ∈ D := by
  induction i with
  | zero => simpa using hγ
  | succ i ih => rw [Function.iterate_succ_apply']; exact h ih

private theorem iterate_injOn_Iio_of_min {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ} {n : ℕ}
    (hmin : ∀ m, 0 < m → m < n → (⇑θ)^[m] α ≠ α) :
    Set.InjOn (fun i => (⇑θ)^[i] α) (Set.Iio n) := by
  intro a ha b hb hab
  have ha' : a < n := ha
  have hb' : b < n := hb
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    have hz : (⇑θ)^[b - a] α = α :=
      Function.iterate_cancel (f := ⇑θ) θ.injective hab.symm
    exact hmin (b - a) (Nat.sub_pos_of_lt hlt) (by omega) hz
  · exact heq
  · exfalso
    have hz : (⇑θ)^[a - b] α = α :=
      Function.iterate_cancel (f := ⇑θ) θ.injective hab
    exact hmin (a - b) (Nat.sub_pos_of_lt hgt) (by omega) hz

private theorem isRoot_iterate {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (i : ℕ) : IsRoot τ ((⇑θ)^[i] γ) := by
  induction i with
  | zero => simpa using hγ
  | succ i ih => rw [Function.iterate_succ_apply']; exact hθΦ _ ih

private def orbitOf {τ : Tag} (θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ))
    (α : Fin τ.rank → ℤ) (n : ℕ) : Finset (Fin τ.rank → ℤ) :=
  (Finset.range n).image fun i => (⇑θ)^[i] α

private theorem a2PairRoots_iterate_mem {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} (i : ℕ) {α β δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ a2PairRoots α β) :
    (⇑θ)^[i] δ ∈ a2PairRoots ((⇑θ)^[i] α) ((⇑θ)^[i] β) := by
  simp only [a2PairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ ⊢
  rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [iterate_map_add, iterate_map_neg]

private theorem isRoot_add_of_oddDerivPair
    {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) : IsRoot τ (α + β) := by
  have hb : oddDerivPairB τ α β = true := oddDerivPairB_iff.mpr h
  simp only [oddDerivPairB, Bool.and_eq_true] at hb
  exact RootOps.isRootB_iff.mp hb.1.1.1.2

private theorem isRoot_of_mem_a2PairRoots
    {τ : Tag} {α β γ : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) (hγ : γ ∈ a2PairRoots α β) : IsRoot τ γ := by
  have hb : oddDerivPairB τ α β = true := oddDerivPairB_iff.mpr h
  simp only [oddDerivPairB, Bool.and_eq_true] at hb
  have hα : IsRoot τ α := RootOps.isRootB_iff.mp hb.1.1.1.1.1.1.1
  have hβ : IsRoot τ β := RootOps.isRootB_iff.mp hb.1.1.1.1.1.1.2
  have hsum : IsRoot τ (α + β) := RootOps.isRootB_iff.mp hb.1.1.1.2
  simp only [a2PairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hβ
  · exact hsum
  · exact IsRoot.neg hα
  · exact IsRoot.neg hβ
  · exact IsRoot.neg hsum

private theorem add_mem_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) (hδ : δ ∈ kernelRoots χ) (h : IsRoot τ (γ + δ)) :
    γ + δ ∈ kernelRoots χ := by
  obtain ⟨-, hγχ⟩ := hγ
  obtain ⟨-, hδχ⟩ := hδ
  exact ⟨h, by rw [ofAdd_add, map_mul, hγχ, hδχ, one_mul]⟩

private theorem commute_pinnedX_of_a2Cycle
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hΔ : Set.MapsTo θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    {α : Fin τ.rank → ℤ} (hα : α ∈ simpleRoots (kernelRoots χ)) {k : ℕ}
    (hmin : ∀ m, 0 < m → m < 2 * k → (⇑θ)^[m] α ≠ α)
    (hαβ : OddDerivPair τ α ((⇑θ)^[k] α))
    (horth : ∀ i, 0 < i → i < k →
      ∀ γ ∈ ({α, (⇑θ)^[k] α} : Set (Fin τ.rank → ℤ)),
      ∀ δ ∈ ({α, (⇑θ)^[k] α} : Set (Fin τ.rank → ℤ)),
        iform γ ((⇑θ)^[i] δ) = 0) :
    ∀ i, 0 < i → i < k → ∀ γ ∈ a2PairRoots α ((⇑θ)^[k] α),
      ∀ δ ∈ a2PairRoots α ((⇑θ)^[k] α), ∀ s t : L,
        Commute (pinnedX τ L γ s) (pinnedX τ L ((⇑θ)^[i] δ) t) := by
  intro i hi0 hik γ hγ δ hδ s t
  set β : Fin τ.rank → ℤ := (⇑θ)^[k] α with hβ
  set α' : Fin τ.rank → ℤ := (⇑θ)^[i] α with hα'
  set β' : Fin τ.rank → ℤ := (⇑θ)^[i] β with hβ'
  have hstep : ∀ ⦃x : Fin τ.rank → ℤ⦄, x ∈ simpleRoots (kernelRoots χ) →
      θ x ∈ simpleRoots (kernelRoots χ) :=
    fun {x} hx => by simpa using hΔ (by simpa using hx)
  have hβΔ : β ∈ simpleRoots (kernelRoots χ) := by
    rw [hβ]
    exact iterate_mem_finset hstep hα k
  have hα'Δ : α' ∈ simpleRoots (kernelRoots χ) := by
    rw [hα']
    exact iterate_mem_finset hstep hα i
  have hβ'Δ : β' ∈ simpleRoots (kernelRoots χ) := by
    rw [hβ']
    exact iterate_mem_finset hstep hβΔ i
  have hδ' : (⇑θ)^[i] δ ∈ a2PairRoots α' β' := by
    simpa [α', β'] using a2PairRoots_iterate_mem (θ := θ) i hδ
  have hβ'eq : β' = (⇑θ)^[i + k] α := by
    rw [hβ', hβ]
    exact (Function.iterate_add_apply (f := ⇑θ) (m := i) (n := k) (x := α)).symm
  have hbnd : ∀ e ∈ ([0, k, i, i + k] : List ℕ), e < 2 * k := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> omega
  have hnd : ([0, k, i, i + k] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, and_true, List.nodup_nil, and_self, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
  have hneList : [α, β, α', β'].Nodup := by
    have hlist : [α, β, α', β'] =
        List.map (fun e : ℕ => (⇑θ)^[e] α) [0, k, i, i + k] := by
      simp only [List.map_cons, List.map_nil, Function.iterate_zero_apply]
      rw [← hβ, ← hα', ← hβ'eq]
    rw [hlist]
    refine List.Nodup.map_on ?_ hnd
    intro a ha b hb hab
    exact iterate_injOn_Iio_of_min (θ := θ) (α := α) hmin (hbnd a ha) (hbnd b hb) hab
  have hsum : IsRoot τ (α + β) := isRoot_add_of_oddDerivPair hαβ
  have hsum' : IsRoot τ (α' + β') := by
    rw [show α' + β' = (⇑θ)^[i] (α + β) by
      rw [hα', hβ', iterate_map_add]]
    exact isRoot_iterate hθΦ hsum i
  have horth' : ∀ x ∈ ({α, β} : Set (Fin τ.rank → ℤ)),
      ∀ y ∈ ({α', β'} : Set (Fin τ.rank → ℤ)), iform x y = 0 := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hy with rfl | rfl
    · simpa [α'] using horth i hi0 hik x hx α (by simp)
    · simpa [β'] using horth i hi0 hik x hx β (by simp)
  have h11b := not_isRoot_add_of_mem_a2PairRoots (χ := χ) hα hβΔ hα'Δ hβ'Δ hneList hsum
    hsum' horth' hγ hδ'
  exact commute_pinnedX_of_oddDeriv (isRoot_of_mem_a2PairRoots hαβ hγ)
    (isRoot_iterate hθΦ (isRoot_of_mem_a2PairRoots hαβ hδ) i) h11b.2 h11b.1 s t

private theorem rootDiagUnit_coordTuple_orbit_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hΨ : Set.BijOn θ (kernelRoots χ) (kernelRoots χ))
    (hΔ : Set.BijOn θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    {α : Fin τ.rank → ℤ} (hα : α ∈ simpleRoots (kernelRoots χ)) {n : ℕ} (hn : 0 < n)
    (hnα : (⇑θ)^[n] α = α) (hmin : ∀ m, 0 < m → m < n → (⇑θ)^[m] α ≠ α)
    (c : (Fin τ.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ simpleRoots (kernelRoots χ), c (θ β) = c β ^ 2 ^ e) :
    rootDiagUnit τ (coordTuple (orbitOf θ α n) c) ∈ Subgroup.closure
      {x : ModGL τ L | x ∈ unionRootSpan L χ Set.univ ∧
        frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  have hstep : ∀ ⦃x : Fin τ.rank → ℤ⦄, x ∈ simpleRoots (kernelRoots χ) →
      θ x ∈ simpleRoots (kernelRoots χ) :=
    fun {x} hx => by simpa using hΔ.mapsTo (by simpa using hx)
  have hOsubΔ : ∀ β ∈ orbitOf θ α n, β ∈ simpleRoots (kernelRoots χ) :=
    range_image_iterate_subset hΔ.mapsTo hα n
  have hOstable : ∀ β ∈ orbitOf θ α n, θ β ∈ orbitOf θ α n := range_image_iterate_stable hn hnα
  have hOcard : (orbitOf θ α n).card = n := range_image_iterate_card hnα hmin
  have hcO : ∀ β ∈ orbitOf θ α n, c (θ β) = c β ^ 2 ^ e :=
    fun β hβ => hc β (hOsubΔ β hβ)
  rcases orthogonal_or_a2Cycle hθ hΔ.mapsTo hα hn hnα hmin with horth | ⟨k, hkn, hαβ, horth⟩
  · have hOorth : ∀ β ∈ orbitOf θ α n, ∀ γ ∈ orbitOf θ α n, β ≠ γ → iform β γ = 0 := by
      intro β hβ γ hγ hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hβ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
      have hi' : i < n := Finset.mem_range.1 hi
      have hj' : j < n := Finset.mem_range.1 hj
      exact horth i hi' j hj' (fun h => hne (by rw [h]))
    exact rootDiagUnit_coordTuple_mem_closure_of_orthogonal (J := Set.univ)
      hθ hθΦ hQX hQT (by simpa only [unionRoots_univ_eq_kernelRoots] using hΨ)
      (fun β hβ => by
        simpa only [unionRoots_univ_eq_kernelRoots] using simpleRoots_subset (hOsubΔ β hβ))
      hOstable hOorth c hcO
  · have hk : 0 < k := by omega
    have hθk : (⇑θ)^[2 * k] α = α := by rw [← hkn]; exact hnα
    have hOcard' : (orbitOf θ α n).card = 2 * k := by rw [hOcard, hkn]
    have hOeq : orbitOf θ α n = (Finset.range (2 * k)).image (fun i => (⇑θ)^[i] α) := by
      show (Finset.range n).image (fun i => (⇑θ)^[i] α) = _
      rw [hkn]
    have hmin' : ∀ m, 0 < m → m < 2 * k → (⇑θ)^[m] α ≠ α := by
      intro m hm hlt
      exact hmin m hm (by omega)
    have hcomm := commute_pinnedX_of_a2Cycle (L := L) hθΦ hΔ.mapsTo hα hmin' hαβ horth
    have hmem := rootDiagUnit_coordTuple_mem_closure_of_a2Cycle (k := k) (he := he)
      hθ hθΦ hQX hQT hk hαβ hθk hcomm (O := orbitOf θ α n) hOeq hOcard' c hcO
    have hαker : α ∈ kernelRoots χ := simpleRoots_subset hα
    have hβΔ : (⇑θ)^[k] α ∈ simpleRoots (kernelRoots χ) := iterate_mem_finset hstep hα k
    have hβker : (⇑θ)^[k] α ∈ kernelRoots χ := simpleRoots_subset hβΔ
    have hSsub : {γ : Fin τ.rank → ℤ | ∃ i < k,
        ∃ δ ∈ a2PairRoots α ((⇑θ)^[k] α), (⇑θ)^[i] δ = γ} ⊆ kernelRoots χ := by
      rintro γ ⟨i, -, δ, hδ, rfl⟩
      exact Set.MapsTo.iterate hΨ.mapsTo i (mem_kernelRoots_of_mem_a2PairRoots hαker hβker
        (add_mem_kernelRoots hαker hβker (isRoot_add_of_oddDerivPair hαβ)) hδ)
    refine Subgroup.closure_mono ?_ hmem
    intro x hx
    refine ⟨?_, hx.2.1, hx.2.2⟩
    have hx' : x ∈ rootSpan τ L (kernelRoots χ) := rootSpan_mono hSsub hx.1
    simpa only [unionRootSpan, unionRoots_univ_eq_kernelRoots] using hx'

private theorem rootDiagUnit_coordTuple_mem_of_stable_subset
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hΨ : Set.BijOn θ (kernelRoots χ) (kernelRoots χ))
    (hΔ : Set.BijOn θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    (c : (Fin τ.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ simpleRoots (kernelRoots χ), c (θ β) = c β ^ 2 ^ e) :
    ∀ A : Finset (Fin τ.rank → ℤ), A ⊆ simpleRoots (kernelRoots χ) →
      (∀ β ∈ A, θ β ∈ A) → rootDiagUnit τ (coordTuple A c) ∈ Subgroup.closure
        {x : ModGL τ L | x ∈ unionRootSpan L χ Set.univ ∧
          frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  intro A
  refine Finset.strongInduction (p := fun A => A ⊆ simpleRoots (kernelRoots χ) →
      (∀ β ∈ A, θ β ∈ A) → rootDiagUnit τ (coordTuple A c) ∈ Subgroup.closure
        {x : ModGL τ L | x ∈ unionRootSpan L χ Set.univ ∧
          frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}) ?_ A
  intro A ih hA hAθ
  by_cases hA0 : A.Nonempty
  · obtain ⟨α, hαA⟩ := hA0
    have hα : α ∈ simpleRoots (kernelRoots χ) := hA hαA
    obtain ⟨N, hNpos, hN⟩ :=
      exists_iterate_eq_of_mapsTo (simpleRoots (kernelRoots χ)).finite_toSet hΔ.mapsTo hΔ.injOn
    let n : ℕ := Function.minimalPeriod (⇑θ) α
    have hn : 0 < n := Function.IsPeriodicPt.minimalPeriod_pos hNpos (hN α hα)
    have hnα : (⇑θ)^[n] α = α := Function.iterate_minimalPeriod
    have hmin : ∀ m, 0 < m → m < n → (⇑θ)^[m] α ≠ α := fun m hm hlt =>
      Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hm.ne' hlt
    have hOsubA : orbitOf θ α n ⊆ A :=
      range_image_iterate_subset (θ := ⇑θ) (D := A) (fun x hx => hAθ x hx) hαA n
    have hαO : α ∈ orbitOf θ α n := mem_range_image_iterate (θ := ⇑θ) (α := α) hn
    have hO_mem : rootDiagUnit τ (coordTuple (orbitOf θ α n) c) ∈ Subgroup.closure
        {x : ModGL τ L | x ∈ unionRootSpan L χ Set.univ ∧
          frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} :=
      rootDiagUnit_coordTuple_orbit_mem he hθ hθΦ hQX hQT hΨ hΔ hα hn hnα hmin c hc
    have hA'Δ : A \ orbitOf θ α n ⊆ simpleRoots (kernelRoots χ) := fun x hx =>
      hA (Finset.sdiff_subset hx)
    have hA'θ : ∀ β ∈ A \ orbitOf θ α n, θ β ∈ A \ orbitOf θ α n := by
      intro β hβ
      obtain ⟨hβA, hβO⟩ := Finset.mem_sdiff.1 hβ
      refine Finset.mem_sdiff.2 ⟨hAθ β hβA, fun hθO => hβO ?_⟩
      exact mem_range_image_iterate_of_theta_mem (D := A) (fun x hx => hAθ x hx)
        θ.injective.injOn hn hnα hαA hβA hθO
    have hsub : A \ orbitOf θ α n ⊂ A :=
      Finset.sdiff_ssubset hOsubA ⟨α, hαO⟩
    have hA'mem : rootDiagUnit τ (coordTuple (A \ orbitOf θ α n) c) ∈ Subgroup.closure
        {x : ModGL τ L | x ∈ unionRootSpan L χ Set.univ ∧
          frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} :=
      ih (A \ orbitOf θ α n) hsub hA'Δ hA'θ
    have hcoord : coordTuple (orbitOf θ α n ∪ A \ orbitOf θ α n) c =
        coordTuple (orbitOf θ α n) c * coordTuple (A \ orbitOf θ α n) c := by
      funext i
      simp only [coordTuple, Pi.mul_apply]
      exact Finset.prod_union Finset.disjoint_sdiff
    rw [← Finset.union_sdiff_of_subset hOsubA, hcoord, rootDiagUnit_mul]
    exact (Subgroup.closure _).mul_mem hO_mem hA'mem
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA0
    rw [hAe]
    have hcoord : coordTuple (∅ : Finset (Fin τ.rank → ℤ)) c = 1 := by
      funext i
      simp [coordTuple]
    rw [hcoord, rootDiagUnit_one]
    exact (Subgroup.closure _).one_mem

theorem rootDiagUnit_coordTuple_mem_closure_of_simpleRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hΨ : Set.BijOn θ (kernelRoots χ) (kernelRoots χ))
    (hΔ : Set.BijOn θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)))
    (c : (Fin τ.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ simpleRoots (kernelRoots χ), c (θ β) = c β ^ 2 ^ e) :
    rootDiagUnit τ (coordTuple (simpleRoots (kernelRoots χ)) c) ∈ Subgroup.closure
      {x : ModGL τ L | x ∈ unionRootSpan L χ Set.univ ∧ frobTwistGL τ L 2 e Q x = x ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  exact rootDiagUnit_coordTuple_mem_of_stable_subset he hθ hθΦ hQX hQT hΨ hΔ c hc
    (simpleRoots (kernelRoots χ)) (fun _ h => h) (fun _ h => hΔ.mapsTo h)

end CFSG.HardMathSupport.C14Idx
