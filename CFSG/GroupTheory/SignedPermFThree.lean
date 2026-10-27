module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Action.Pi

public section

namespace CFSG.GroupTheory

private def zeroCount (v : Fin 3 → ZMod 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin 3 => v i = 0)).card

private abbrev noZero (v : Fin 3 → ZMod 3) : Prop := ∀ i, v i ≠ 0

private def stdBasis (j : Fin 3) : Fin 3 → ZMod 3 := fun i => if i = j then 1 else 0

private def noZeroSet : Finset (Fin 3 → ZMod 3) := Finset.univ.filter noZero

private abbrev signedApply (p : (Fin 3 → Fin 3) × (Fin 3 → ZMod 3))
    (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun i => p.2 i * v (p.1 i)

private def signPerms : Finset ((Fin 3 → Fin 3) × (Fin 3 → ZMod 3)) :=
  Finset.univ.filter (fun p => Function.Injective p.1 ∧ ∀ i, p.2 i ≠ 0)

private abbrev orbit (v : Fin 3 → ZMod 3) : Finset (Fin 3 → ZMod 3) :=
  Finset.univ.filter (fun w => ∃ p ∈ signPerms, w = signedApply p v)

private def stratum (z : ℕ) : Finset (Fin 3 → ZMod 3) :=
  Finset.univ.filter (fun w => zeroCount w = z)

private def u0Vec : Fin 3 → ZMod 3 := fun _ => 1

private def u1Vec : Fin 3 → ZMod 3 := fun i => if i = 0 then 0 else 1

private lemma two_pow_inj {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b :=
  le_antisymm
    ((Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).mp (le_of_eq h))
    ((Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).mp (le_of_eq h.symm))

private lemma card_filter_noZero_add (u : Fin 3 → ZMod 3) :
    (Finset.univ.filter (fun w : Fin 3 → ZMod 3 => noZero w ∧ noZero (u + w))).card
      = 2 ^ zeroCount u := by
  decide +revert

private lemma zeroCount_stdBasis (j : Fin 3) : zeroCount (stdBasis j) = 2 := by
  decide +revert

private lemma eq_smul_stdBasis_of_zeroCount_eq_two (u : Fin 3 → ZMod 3)
    (h : zeroCount u = 2) :
    ∃ (j : Fin 3) (c : ZMod 3), c ≠ 0 ∧ u = c • stdBasis j := by
  decide +revert

private lemma smul_stdBasis_eq_or_neg (c : ZMod 3) (j : Fin 3) :
    c ≠ 0 → c • stdBasis j = stdBasis j ∨ c • stdBasis j = -stdBasis j := by
  decide +revert

private lemma stdBasis_injective : Function.Injective (stdBasis : Fin 3 → Fin 3 → ZMod 3) := by
  intro j k h
  by_contra hne
  have h1 : (1 : ZMod 3) = 0 := by
    have h' := congrFun h j
    simpa [stdBasis, hne] using h'
  exact one_ne_zero h1

private lemma stdBasis_ne_neg_of_ne {j k : Fin 3} (h : j ≠ k) : stdBasis j ≠ -stdBasis k := by
  intro hc
  have h1 : (1 : ZMod 3) = 0 := by
    have h' := congrFun hc j
    simpa [stdBasis, h] using h'
  exact one_ne_zero h1

private lemma zmod_smul_eq_nsmul_val (a : ZMod 3) (x : Fin 3 → ZMod 3) :
    a • x = a.val • x := by
  funext i
  change a • x i = a.val • x i
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]

private lemma sum_smul_stdBasis_eq (v : Fin 3 → ZMod 3) :
    (∑ j, v j • stdBasis j) = v := by
  decide +revert

private lemma smul_stdBasis_self (c : ZMod 3) (i : Fin 3) :
    (c • stdBasis i) i = c := by
  decide +revert

private lemma smul_stdBasis_of_ne (c : ZMod 3) (m i : Fin 3) (h : i ≠ m) :
    (c • stdBasis m) i = 0 := by
  decide +revert

private lemma map_noZeroSet (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ v, noZero v → noZero (α v)) :
    noZeroSet.map α.toEquiv.toEmbedding = noZeroSet := by
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rw [Finset.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    simp only [noZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hα x hx
  · rw [Finset.card_map]

private lemma noZero_of_map_noZero (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ v, noZero v → noZero (α v)) {v : Fin 3 → ZMod 3}
    (hv : noZero (α v)) : noZero v := by
  have hmap := map_noZeroSet α hα
  have hmem : α v ∈ noZeroSet := by
    simp only [noZeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hv
  rw [← hmap] at hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨x, hx, hxv⟩ := hmem
  have hx' : noZero x := by
    simp only [noZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx
  have hxv' : α x = α v := by simpa using hxv
  have hxeq : x = v := α.injective hxv'
  subst hxeq
  exact hx'

private lemma filter_map_noZero_add (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ v, noZero v → noZero (α v)) (u : Fin 3 → ZMod 3) :
    (Finset.univ.filter (fun w : Fin 3 → ZMod 3 => noZero w ∧ noZero (α u + w))) =
      (Finset.univ.filter (fun w : Fin 3 → ZMod 3 => noZero w ∧ noZero (u + w))).map
        α.toEquiv.toEmbedding := by
  apply Finset.ext
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hw, huw⟩
    refine ⟨α.symm w, ⟨?_, ?_⟩, ?_⟩
    · exact noZero_of_map_noZero α hα (by simpa using hw)
    · apply noZero_of_map_noZero α hα
      have h : α (u + α.symm w) = α u + w := by simp
      rw [h]; exact huw
    · simp
  · rintro ⟨x, ⟨hx, hux⟩, rfl⟩
    exact ⟨by simpa using hα x hx, by simpa [map_add] using hα (u + x) hux⟩

private lemma zeroCount_map (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ v, noZero v → noZero (α v)) (u : Fin 3 → ZMod 3) :
    zeroCount (α u) = zeroCount u := by
  have hcard : (Finset.univ.filter (fun w : Fin 3 → ZMod 3 =>
        noZero w ∧ noZero (α u + w))).card =
      (Finset.univ.filter (fun w : Fin 3 → ZMod 3 =>
        noZero w ∧ noZero (u + w))).card := by
    rw [filter_map_noZero_add α hα u, Finset.card_map]
  have hpow : 2 ^ zeroCount (α u) = 2 ^ zeroCount u := by
    rw [← card_filter_noZero_add (α u), ← card_filter_noZero_add u]
    exact hcard
  exact two_pow_inj hpow

private lemma injective_tau_of_stdBasis (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (τ : Fin 3 → Fin 3) (ε' : Fin 3 → ZMod 3) (hε' : ∀ j, ε' j ≠ 0)
    (hαe : ∀ j, α (stdBasis j) = ε' j • stdBasis (τ j)) :
    Function.Injective τ := by
  intro j k hjk
  by_contra hne
  have hj : α (stdBasis j) = stdBasis (τ j) ∨ α (stdBasis j) = -stdBasis (τ j) := by
    rw [hαe j]; exact smul_stdBasis_eq_or_neg (ε' j) (τ j) (hε' j)
  have hk : α (stdBasis k) = stdBasis (τ k) ∨ α (stdBasis k) = -stdBasis (τ k) := by
    rw [hαe k]; exact smul_stdBasis_eq_or_neg (ε' k) (τ k) (hε' k)
  rcases hj with hj | hj <;> rcases hk with hk | hk
  · exact hne (stdBasis_injective (α.injective (by rw [hj, hk, hjk])))
  · have heq : α (stdBasis j) = α (-(stdBasis k)) := by
      rw [map_neg, hk, neg_neg, ← hjk, ← hj]
    exact stdBasis_ne_neg_of_ne hne (α.injective heq)
  · have heq : α (stdBasis j) = α (-(stdBasis k)) := by
      rw [map_neg, hk, ← hjk, hj]
    exact stdBasis_ne_neg_of_ne hne (α.injective heq)
  · exact hne (stdBasis_injective (α.injective (by rw [hj, hk, hjk])))

private lemma exists_formula_of_stdBasis (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (τ : Fin 3 → Fin 3) (ε' : Fin 3 → ZMod 3) (hτinj : Function.Injective τ)
    (hε' : ∀ j, ε' j ≠ 0)
    (hαe : ∀ j, α (stdBasis j) = ε' j • stdBasis (τ j)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ v, α v = fun i => ε i * v (σ i) := by
  let τe : Equiv.Perm (Fin 3) := Equiv.ofBijective τ hτinj.bijective_of_finite
  let σ : Equiv.Perm (Fin 3) := τe.symm
  let ε : Fin 3 → ZMod 3 := fun i => ε' (σ i)
  refine ⟨σ, ε, fun i => hε' (σ i), ?_⟩
  intro v
  have hαsmul : ∀ (a : ZMod 3) (x : Fin 3 → ZMod 3), α (a • x) = a • α x := by
    intro a x
    rw [zmod_smul_eq_nsmul_val a x, map_nsmul, zmod_smul_eq_nsmul_val a (α x)]
  have hexp : α v = ∑ j, (v j * ε' j) • stdBasis (τ j) := by
    calc α v = α (∑ j, v j • stdBasis j) := by rw [sum_smul_stdBasis_eq v]
      _ = ∑ j, α (v j • stdBasis j) := map_sum α _ Finset.univ
      _ = ∑ j, v j • α (stdBasis j) :=
            Finset.sum_congr rfl (fun j _ => hαsmul (v j) (stdBasis j))
      _ = ∑ j, v j • (ε' j • stdBasis (τ j)) :=
            Finset.sum_congr rfl (fun j _ => by rw [hαe j])
      _ = ∑ j, (v j * ε' j) • stdBasis (τ j) :=
            Finset.sum_congr rfl (fun j _ => by rw [smul_smul])
  ext i
  rw [hexp]
  have hτσ : τ (σ i) = i := by
    change τ (τe.symm i) = i
    exact Equiv.ofBijective_apply_symm_apply τ hτinj.bijective_of_finite i
  have hgoal : (∑ j, ((v j * ε' j) • stdBasis (τ j)) i) = ε i * v (σ i) := by
    rw [Finset.sum_eq_single (σ i)]
    · rw [hτσ, smul_stdBasis_self]
      exact mul_comm (v (σ i)) (ε' (σ i))
    · intro j _ hj
      have hji : τ j ≠ i := by
        intro h
        exact hj (hτinj (h.trans hτσ.symm))
      have hij : i ≠ τ j := fun h => hji h.symm
      rw [smul_stdBasis_of_ne (v j * ε' j) (τ j) i hij]
    · intro hmem; exact absurd (Finset.mem_univ (σ i)) hmem
  exact hgoal

theorem exists_signedPerm_of_preserves (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) → ∀ i, α v i ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ v, α v = fun i => ε i * v (σ i) := by
  classical
  have hnoz : ∀ v, noZero v → noZero (α v) := fun v hv i => hα v hv i
  have hzero : ∀ v, zeroCount (α v) = zeroCount v := fun v => zeroCount_map α hnoz v
  have hbasis : ∀ j : Fin 3, ∃ (m : Fin 3) (c : ZMod 3), c ≠ 0 ∧
      α (stdBasis j) = c • stdBasis m := by
    intro j
    have hz : zeroCount (α (stdBasis j)) = 2 := by
      rw [hzero (stdBasis j), zeroCount_stdBasis]
    exact eq_smul_stdBasis_of_zeroCount_eq_two (α (stdBasis j)) hz
  choose τ hτ using hbasis
  choose ε' hε' using hτ
  have hε'ne : ∀ j, ε' j ≠ 0 := fun j => (hε' j).1
  have hαe : ∀ j, α (stdBasis j) = ε' j • stdBasis (τ j) := fun j => (hε' j).2
  exact exists_formula_of_stdBasis α τ ε' (injective_tau_of_stdBasis α τ ε' hε'ne hαe) hε'ne hαe

private lemma zeroCount_signedApply (p : (Fin 3 → Fin 3) × (Fin 3 → ZMod 3))
    (hp : p ∈ signPerms) (v : Fin 3 → ZMod 3) :
    zeroCount (signedApply p v) = zeroCount v := by
  obtain ⟨-, hinj, hnz⟩ := Finset.mem_filter.mp hp
  classical
  rw [zeroCount, zeroCount]
  refine Finset.card_bij (fun i _ => p.1 i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (mul_eq_zero.mp hi).resolve_left (hnz i)
  · intro i₁ _ i₂ _ heq
    exact hinj heq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨i, hi⟩ := (hinj.bijective_of_finite).surjective j
    refine ⟨i, ?_, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show p.2 i * v (p.1 i) = 0
    rw [hi, hj, mul_zero]

private lemma orbit_subset_stratum (v : Fin 3 → ZMod 3) :
    orbit v ⊆ stratum (zeroCount v) := by
  intro w hw
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  simp only [stratum, Finset.mem_filter, Finset.mem_univ, true_and]
  exact zeroCount_signedApply p hp v

private lemma orbit_u0Vec : orbit u0Vec = stratum 0 := by decide

private lemma orbit_u1Vec : orbit u1Vec = stratum 1 := by decide

private lemma card_stratum_zero : (stratum 0).card = 8 := by decide

private lemma card_stratum_one : (stratum 1).card = 12 := by decide

private lemma image_orbit_subset (β : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hβ : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ (τ : Equiv.Perm (Fin 3)) (δ : Fin 3 → ZMod 3), (∀ i, δ i ≠ 0) ∧ ∀ v,
        β (fun i => ε i * v (σ i)) = fun i => δ i * β v (τ i))
    (v : Fin 3 → ZMod 3) :
    (orbit v).image β ⊆ orbit (β v) := by
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨-, hbinj, hnz⟩ := Finset.mem_filter.mp hp
  obtain ⟨τ, δ, hδ, heq⟩ := hβ (Equiv.ofBijective p.1 hbinj.bijective_of_finite) p.2 hnz
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(τ, δ), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, τ.injective, hδ⟩
  · rw [hpx]
    exact heq v

private lemma zeroCount_eq_zero_of_noZero (v : Fin 3 → ZMod 3) (hv : noZero v) :
    zeroCount v = 0 := by
  decide +revert

private lemma noZero_of_zeroCount_eq_zero (v : Fin 3 → ZMod 3) (hv : zeroCount v = 0) :
    noZero v := by
  decide +revert

private lemma zeroCount_eq_one_of_stratum_card_ge_twelve (w : Fin 3 → ZMod 3)
    (h : 12 ≤ (stratum (zeroCount w)).card) : zeroCount w = 1 := by
  decide +revert

private lemma zeroCount_eq_zero_of_stratum_card_ge_eight_ne_one (w : Fin 3 → ZMod 3)
    (h : 8 ≤ (stratum (zeroCount w)).card) (h1 : zeroCount w ≠ 1) :
    zeroCount w = 0 := by
  decide +revert

private lemma zeroCount_alpha_u1Vec (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ (τ : Equiv.Perm (Fin 3)) (δ : Fin 3 → ZMod 3), (∀ i, δ i ≠ 0) ∧ ∀ v,
        α (fun i => ε i * v (σ i)) = fun i => δ i * α v (τ i)) :
    zeroCount (α u1Vec) = 1 := by
  have hcard_u1 : (orbit u1Vec).card = 12 := by rw [orbit_u1Vec, card_stratum_one]
  have hsub1 : (orbit u1Vec).image α ⊆ stratum (zeroCount (α u1Vec)) := by
    intro z hz
    exact orbit_subset_stratum (α u1Vec) (image_orbit_subset α hα u1Vec hz)
  have hle : 12 ≤ (stratum (zeroCount (α u1Vec))).card := by
    have h := Finset.card_le_card hsub1
    rwa [Finset.card_image_of_injective (orbit u1Vec) α.injective, hcard_u1] at h
  exact zeroCount_eq_one_of_stratum_card_ge_twelve (α u1Vec) hle

private lemma zeroCount_alpha_u0Vec (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ (τ : Equiv.Perm (Fin 3)) (δ : Fin 3 → ZMod 3), (∀ i, δ i ≠ 0) ∧ ∀ v,
        α (fun i => ε i * v (σ i)) = fun i => δ i * α v (τ i)) :
    zeroCount (α u0Vec) = 0 := by
  have hcard_u0 : (orbit u0Vec).card = 8 := by rw [orbit_u0Vec, card_stratum_zero]
  have hcard_u1 : (orbit u1Vec).card = 12 := by rw [orbit_u1Vec, card_stratum_one]
  have hk1 : zeroCount (α u1Vec) = 1 := zeroCount_alpha_u1Vec α hα
  have hk0ne : zeroCount (α u0Vec) ≠ 1 := by
    intro hk
    have hsub0 : (orbit u0Vec).image α ⊆ stratum 1 := by
      intro z hz
      have hz' := orbit_subset_stratum (α u0Vec) (image_orbit_subset α hα u0Vec hz)
      rwa [hk] at hz'
    have hsub1 : (orbit u1Vec).image α ⊆ stratum 1 := by
      intro z hz
      have hz' := orbit_subset_stratum (α u1Vec) (image_orbit_subset α hα u1Vec hz)
      rwa [hk1] at hz'
    have hdisj : Disjoint (orbit u0Vec) (orbit u1Vec) := by
      rw [orbit_u0Vec, orbit_u1Vec, Finset.disjoint_left]
      intro x hx0 hx1
      simp only [stratum, Finset.mem_filter, Finset.mem_univ, true_and] at hx0 hx1
      rw [hx0] at hx1
      exact Nat.zero_ne_one hx1
    have hunion : ((orbit u0Vec ∪ orbit u1Vec).image α) ⊆ stratum 1 := by
      rw [Finset.image_union]
      exact Finset.union_subset hsub0 hsub1
    have hcardu : ((orbit u0Vec ∪ orbit u1Vec).image α).card = 20 := by
      rw [Finset.card_image_of_injective (orbit u0Vec ∪ orbit u1Vec) α.injective,
        Finset.card_union_of_disjoint hdisj, hcard_u0, hcard_u1]
    have hle2 := Finset.card_le_card hunion
    rw [hcardu, card_stratum_one] at hle2
    exact absurd hle2 (by decide)
  have hsub0 : (orbit u0Vec).image α ⊆ stratum (zeroCount (α u0Vec)) := by
    intro z hz
    exact orbit_subset_stratum (α u0Vec) (image_orbit_subset α hα u0Vec hz)
  have hle : 8 ≤ (stratum (zeroCount (α u0Vec))).card := by
    have h := Finset.card_le_card hsub0
    rwa [Finset.card_image_of_injective (orbit u0Vec) α.injective, hcard_u0] at h
  exact zeroCount_eq_zero_of_stratum_card_ge_eight_ne_one (α u0Vec) hle hk0ne

theorem eq_signedPerm_of_normalizes (α : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3))
    (hα : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ (τ : Equiv.Perm (Fin 3)) (δ : Fin 3 → ZMod 3), (∀ i, δ i ≠ 0) ∧ ∀ v,
        α (fun i => ε i * v (σ i)) = fun i => δ i * α v (τ i)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ v, α v = fun i => ε i * v (σ i) := by
  classical
  have hpres : ∀ v, noZero v → noZero (α v) := by
    intro v hv
    have hvmem : v ∈ orbit u0Vec := by
      rw [orbit_u0Vec]
      simp only [stratum, Finset.mem_filter, Finset.mem_univ, true_and]
      exact zeroCount_eq_zero_of_noZero v hv
    have hmem : α v ∈ stratum (zeroCount (α u0Vec)) :=
      orbit_subset_stratum (α u0Vec)
        (image_orbit_subset α hα u0Vec (Finset.mem_image.mpr ⟨v, hvmem, rfl⟩))
    rw [zeroCount_alpha_u0Vec α hα] at hmem
    have hzc : zeroCount (α v) = 0 := by
      simpa only [stratum, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    exact noZero_of_zeroCount_eq_zero (α v) hzc
  exact exists_signedPerm_of_preserves α hpres

end CFSG.GroupTheory
