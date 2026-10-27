module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open MulAction

section Orbits

variable {G α : Type*} [Group G] [MulAction G α]

theorem orbit_subset_of_invariant (Γ : Subgroup G) {Z : Set α} {s e : α}
    (hZ : ∀ γ ∈ Γ, ∀ z ∈ Z, γ • z ∈ Z) (he : e ∈ Z) (hes : e ∈ orbit Γ s) : orbit Γ s ⊆ Z := by
  obtain ⟨γ, hγ⟩ := hes
  have hs : s ∈ Z := by
    have := hZ γ⁻¹ (Subgroup.inv_mem _ γ.2) e he
    have h2 : (γ⁻¹ : G) • e = s := by
      rw [← hγ]
      show (γ : G)⁻¹ • ((γ : G) • s) = s
      simp
    rwa [h2] at this
  rintro _ ⟨γ', rfl⟩
  exact hZ γ' γ'.2 s hs

theorem card_eq_ncard_orbit_mul [Finite G] (s : α) :
    Nat.card G = (orbit G s).ncard * Nat.card (stabilizer G s) := by
  have h := (stabilizer G s).card_mul_index
  rw [index_stabilizer] at h
  rw [← h, mul_comm]

theorem maximal_of_orbit_pieces [Finite G] (s₀ : α) (Γ : Subgroup G)
    (hΓ : Γ ≤ stabilizer G s₀) {N : ℕ} (hN : Nat.card G ≤ N * Nat.card Γ)
    (s : Fin 4 → α) (hs₀ : s 0 = s₀) (hs : ∀ j, s j ∈ orbit G s₀)
    (E : Fin 4 → Set α) (hE : ∀ j, E j ⊆ orbit Γ (s j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (ℓ : Fin 4 → ℕ) (hcard : ∀ j, (E j).ncard = ℓ j) (hfin : ∀ j, (E j).Finite)
    (hℓ0 : ℓ 0 = 1) (hsum : ∑ j, ℓ j = N)
    (harith : ∀ I : Finset (Fin 4), 0 ∈ I → (∑ j ∈ I, ℓ j) ∣ N → I = {0} ∨ I = Finset.univ) :
    Γ = stabilizer G s₀ ∧ ∀ Y : Subgroup G, Γ ≤ Y → Y = Γ ∨ Y = ⊤ := by
  classical
  set X : Set α := orbit G s₀ with hXdef
  set M : Subgroup G := stabilizer G s₀ with hMdef
  have hXfin : X.Finite := Set.finite_range _
  have hGXM : Nat.card G = X.ncard * Nat.card M := card_eq_ncard_orbit_mul s₀
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hΓpos : 0 < Nat.card Γ := Nat.card_pos
  have hNpos : 0 < N := by
    rw [← hsum]
    have : ℓ 0 ≤ ∑ j, ℓ j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ 0)
    omega
  have hEX : ∀ j, E j ⊆ X := by
    intro j e he
    obtain ⟨γ, hγ⟩ := hE j he
    obtain ⟨g, hg⟩ := hs j
    refine mem_orbit_iff.2 ⟨(γ : G) * g, ?_⟩
    rw [← hγ, ← hg]
    show ((γ : G) * g) • s₀ = (γ : G) • (g • s₀)
    exact mul_smul _ _ _
  let Ef : Fin 4 → Finset α := fun j => (hfin j).toFinset
  have hEf : ∀ j, (Ef j : Set α) = E j := fun j => (hfin j).coe_toFinset
  have hEfcard : ∀ j, (Ef j).card = ℓ j := fun j => by
    rw [← hcard j, Set.ncard_eq_toFinset_card _ (hfin j)]
  have hEfdisj : ∀ i j, i ≠ j → Disjoint (Ef i) (Ef j) := fun i j hij => by
    rw [← Finset.disjoint_coe, hEf, hEf]
    exact hdisj i j hij
  have hbi : ∀ I : Finset (Fin 4), (I.biUnion Ef).card = ∑ j ∈ I, ℓ j := fun I => by
    rw [Finset.card_biUnion (fun i _ j _ hij => hEfdisj i j hij)]
    exact Finset.sum_congr rfl fun j _ => hEfcard j
  have hbicoe : ∀ I : Finset (Fin 4), ((I.biUnion Ef : Finset α) : Set α) = ⋃ j ∈ I, E j := by
    intro I
    ext e
    simp [hEf]
  have hUX : ((Finset.univ.biUnion Ef : Finset α) : Set α) ⊆ X := by
    rw [hbicoe]
    intro e he
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at he
    obtain ⟨j, hj⟩ := he
    exact hEX j hj
  have hUcard : (Finset.univ.biUnion Ef).card = N := by rw [hbi, hsum]
  have hXN : N ≤ X.ncard := by
    have := Set.ncard_le_ncard hUX hXfin
    rwa [Set.ncard_coe_finset, hUcard] at this
  have hMle : Nat.card M ≤ Nat.card Γ := by
    have h1 : N * Nat.card M ≤ N * Nat.card Γ := by
      calc N * Nat.card M ≤ X.ncard * Nat.card M := Nat.mul_le_mul_right _ hXN
        _ = Nat.card G := hGXM.symm
        _ ≤ N * Nat.card Γ := hN
    exact Nat.le_of_mul_le_mul_left h1 hNpos
  have hΓM : Γ = M := Subgroup.eq_of_le_of_card_ge hΓ hMle
  have hXeq : X.ncard = N := by
    have h1 : X.ncard * Nat.card M ≤ N * Nat.card M := by
      calc X.ncard * Nat.card M = Nat.card G := hGXM.symm
        _ ≤ N * Nat.card Γ := hN
        _ = N * Nat.card M := by rw [hΓM]
    exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hMpos) hXN
  have hNG : Nat.card G = N * Nat.card M := by rw [hGXM, hXeq]
  have hUeq : ((Finset.univ.biUnion Ef : Finset α) : Set α) = X := by
    apply Set.eq_of_subset_of_ncard_le hUX _ hXfin
    rw [Set.ncard_coe_finset, hUcard, hXeq]
  refine ⟨hΓM, fun Y hΓY => ?_⟩
  have hMY : M ≤ Y := hΓM ▸ hΓY
  let Z : Set α := orbit Y s₀
  have hZX : Z ⊆ X := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(y : G), rfl⟩
  have hs₀Z : s₀ ∈ Z := ⟨1, one_smul _ _⟩
  have hZinv : ∀ γ ∈ Γ, ∀ z ∈ Z, γ • z ∈ Z := by
    rintro γ hγ _ ⟨y, rfl⟩
    refine ⟨⟨γ, hΓY hγ⟩ * y, ?_⟩
    show (γ * (y : G)) • s₀ = γ • ((y : G) • s₀)
    exact mul_smul _ _ _
  have hEZ : ∀ j, (E j ∩ Z).Nonempty → E j ⊆ Z := by
    rintro j ⟨e, heE, heZ⟩
    exact (hE j).trans (orbit_subset_of_invariant Γ hZinv heZ (hE j heE))
  let I : Finset (Fin 4) := Finset.univ.filter fun j => E j ⊆ Z
  have hZI : ((I.biUnion Ef : Finset α) : Set α) = Z := by
    rw [hbicoe]
    apply Set.Subset.antisymm
    · intro e he
      simp only [Set.mem_iUnion] at he
      obtain ⟨j, hj, hje⟩ := he
      have : E j ⊆ Z := (Finset.mem_filter.1 hj).2
      exact this hje
    · intro z hz
      have hzX := hZX hz
      rw [← hUeq, hbicoe] at hzX
      simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hzX
      obtain ⟨j, hjz⟩ := hzX
      simp only [Set.mem_iUnion]
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hEZ j ⟨z, hjz, hz⟩⟩, hjz⟩
  have hZcard : Z.ncard = ∑ j ∈ I, ℓ j := by
    rw [← hZI, Set.ncard_coe_finset, hbi]
  have hΓorb : orbit Γ s₀ ⊆ {s₀} := by
    rintro _ ⟨γ, rfl⟩
    exact mem_stabilizer_iff.1 (hΓ γ.2)
  have h0I : (0 : Fin 4) ∈ I := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    intro e he
    have : e ∈ orbit Γ s₀ := by
      have := hE 0 he
      rwa [hs₀] at this
    have := hΓorb this
    rw [Set.mem_singleton_iff.1 this]
    exact hs₀Z
  have hstab : Nat.card (stabilizer Y s₀) = Nat.card M := by
    rw [← stabilizer_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMY).toEquiv
  have hZY : N = Z.ncard * Y.index := by
    have h1 := (stabilizer Y s₀).card_mul_index
    rw [index_stabilizer] at h1
    have h2 := Y.card_mul_index
    have h3 : N * Nat.card M = Z.ncard * Y.index * Nat.card M := by
      calc N * Nat.card M = Nat.card G := hNG.symm
        _ = Nat.card Y * Y.index := h2.symm
        _ = (Nat.card M * Z.ncard) * Y.index := by rw [← h1, hstab]
        _ = Z.ncard * Y.index * Nat.card M := by ring
    exact Nat.eq_of_mul_eq_mul_right hMpos h3
  have hZN : Z.ncard ∣ N := ⟨Y.index, hZY⟩
  rcases harith I h0I (hZcard ▸ hZN) with hI | hI
  ·
    left
    have h1 : Z.ncard = 1 := by rw [hZcard, hI]; simpa using hℓ0
    obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 h1
    have hYM : Y ≤ M := by
      intro y hy
      have : (y • s₀ : α) ∈ Z := ⟨⟨y, hy⟩, rfl⟩
      rw [hz, Set.mem_singleton_iff] at this
      have h2 : s₀ ∈ Z := hs₀Z
      rw [hz, Set.mem_singleton_iff] at h2
      exact mem_stabilizer_iff.2 (this.trans h2.symm)
    exact le_antisymm (hΓM ▸ hYM) hΓY
  ·
    right
    have h1 : Z.ncard = N := by rw [hZcard, hI, hsum]
    rw [h1] at hZY
    have : Y.index = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hNpos (show N * Y.index = N * 1 by rw [← hZY]; ring)
      exact this
    exact Subgroup.index_eq_one.1 this

theorem le_card_of_orbit_stabilizer [Finite G] (Γ B : Subgroup G) (a : α) (hBΓ : B ≤ Γ)
    (hBa : B ≤ stabilizer G a) {m k : ℕ} (hm : m ≤ (orbit Γ a).ncard)
    (hk : k ≤ Nat.card B) : m * k ≤ Nat.card Γ := by
  rw [card_eq_ncard_orbit_mul (G := Γ) a]
  refine Nat.mul_le_mul hm (hk.trans ?_)
  have hle : B.subgroupOf Γ ≤ stabilizer Γ a := by
    intro g hg
    exact mem_stabilizer_iff.2 (mem_stabilizer_iff.1 (hBa hg))
  calc Nat.card B = Nat.card (B.subgroupOf Γ) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv.symm
    _ ≤ Nat.card (stabilizer Γ a) := Nat.card_mono (Set.toFinite _) hle

end Orbits

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
