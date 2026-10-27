module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RankBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv Equiv.Perm CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem isElemAbelian_mono {G : Type*} [Group G] {p : ℕ} {E E' : Subgroup G} (h : E' ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p E' := by
  refine ⟨isMulCommutative_iff.mpr fun a b => ?_, fun x hx => hE.2 x (h hx)⟩
  have := isMulCommutative_iff.mp hE.1 ⟨a, h a.2⟩ ⟨b, h b.2⟩
  have h2 : ((a : G) * b : G) = (b : G) * a := congrArg Subtype.val this
  exact Subtype.ext h2

section Bound

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_le_three_pow_of_fixes (s : Finset α) :
    ∀ E : Subgroup (Perm α), IsElemAbelian 3 E → (∀ g ∈ E, ∀ y, y ∉ s → g y = y) →
      Nat.card E ≤ 3 ^ (s.card / 3) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro E hE hfix
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases htriv : ∀ g ∈ E, g = 1
  · have : Nat.card E = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
    rw [this]
    exact Nat.one_le_pow _ _ (by norm_num)
  push Not at htriv
  obtain ⟨g, hgE, hg1⟩ := htriv
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ x := by
    by_contra h
    push Not at h
    exact hg1 (Equiv.ext h)
  have hxs : x ∈ s := by
    by_contra h
    exact hx (hfix g hgE x h)
  let O : Set α := MulAction.orbit E x
  have hxO : x ∈ O := MulAction.mem_orbit_self x
  have hOs : ∀ y ∈ O, y ∈ s := by
    rintro y ⟨h, rfl⟩
    by_contra hy
    have h2 : (h : Perm α) ((h : Perm α) x) = (h : Perm α) x := hfix h h.2 _ hy
    have h1 : (h : Perm α) x = x := (h : Perm α).injective h2
    exact hy (show (h : Perm α) x ∈ s by rw [h1]; exact hxs)
  let E' : Subgroup (Perm α) := (MulAction.stabilizer E x).map E.subtype
  have hE'le : E' ≤ E := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hE'ab := isElemAbelian_mono hE'le hE
  have hE'fix : ∀ g ∈ E', ∀ y ∈ O, g y = y := by
    rintro _ ⟨k, hk, rfl⟩ y ⟨h, rfl⟩
    have hk' : (k : Perm α) x = x := MulAction.mem_stabilizer_iff.mp hk
    have := hcomm k k.2 h h.2
    change (k : Perm α) ((h : Perm α) x) = (h : Perm α) x
    rw [← Perm.mul_apply, this, Perm.mul_apply, hk']
  set s' : Finset α := s.filter (fun y => y ∉ O) with hs'
  have hs'lt : s' ⊂ s := Finset.filter_ssubset.mpr ⟨x, hxs, by simpa using hxO⟩
  have hfix' : ∀ g ∈ E', ∀ y, y ∉ s' → g y = y := by
    intro g hg y hy
    by_cases hyO : y ∈ O
    · exact hE'fix g hg y hyO
    · have : y ∉ s := fun hys => hy (Finset.mem_filter.mpr ⟨hys, hyO⟩)
      exact hfix g (hE'le hg) y this
  have ihE' := ih s' hs'lt E' hE'ab hfix'
  have hcardE' : Nat.card E' = Nat.card (MulAction.stabilizer E x) :=
    Subgroup.card_map_of_injective E.subtype_injective
  have horb : Nat.card O * Nat.card (MulAction.stabilizer E x) = Nat.card E := by
    simpa [Nat.card_eq_fintype_card] using MulAction.card_orbit_mul_card_stabilizer_eq_card_group E x
  have hsc : s.card = s'.card + Nat.card O := by
    have hfO : s.filter (· ∈ O) = O.toFinset := by
      ext y
      simp only [Finset.mem_filter, Set.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hOs y h, h⟩⟩
    have h1 := Finset.card_filter_add_card_filter_not (s := s) (fun y => y ∈ O)
    rw [hfO, Set.toFinset_card, ← Nat.card_eq_fintype_card] at h1
    have e : s' = s.filter (fun y => ¬ y ∈ O) := by ext; simp [hs']
    rw [e]
    omega
  have hpg : IsPGroup 3 E := elementary_isPGroup 3 E hE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hdvd : Nat.card O ∣ 3 ^ n := hn ▸ Dvd.intro _ horb
  obtain ⟨j, -, hjO⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    have h1 : Nat.card O = 1 := by simpa using hjO
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp h1
    have hgO : g x ∈ O := MulAction.mem_orbit x (⟨g, hgE⟩ : E)
    exact hx (congrArg Subtype.val (hsub.elim ⟨g x, hgO⟩ ⟨x, hxO⟩))
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i + 1 ≤ 3 ^ i := Nat.lt_pow_self (by norm_num)
  have hpow : 3 ^ (i + 1) = 3 ^ i * 3 := pow_succ 3 i
  have h3 : s.card / 3 = s'.card / 3 + 3 ^ i := by omega
  rw [h3]
  calc Nat.card E = 3 ^ (i + 1) * Nat.card E' := by rw [← horb, hjO, hcardE']
    _ ≤ 3 ^ (3 ^ i) * 3 ^ (s'.card / 3) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hi) ihE'
    _ = 3 ^ (s'.card / 3 + 3 ^ i) := by rw [← pow_add, add_comm]

theorem card_le_three_pow_perm (E : Subgroup (Perm α)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ (Fintype.card α / 3) := by
  simpa using card_le_three_pow_of_fixes Finset.univ E hE (fun g _ y hy => absurd (Finset.mem_univ y) hy)

end Bound

theorem pRank_three_alternating_le {N : ℕ} :
    pRank 3 (⊤ : Subgroup (alternatingGroup (Fin N))) ≤ N / 3 := by
  unfold pRank
  apply csSup_le'
  rintro k ⟨E, -, hE, hcard⟩
  have hE' := elementary_map_injective 3 E (alternatingGroup (Fin N)).subtype
    (alternatingGroup (Fin N)).subtype_injective hE
  have h1 := card_le_three_pow_perm (E.map (alternatingGroup (Fin N)).subtype) hE'
  rw [Subgroup.card_map_of_injective (alternatingGroup (Fin N)).subtype_injective, hcard,
    Fintype.card_fin] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

section Drop

@[expose] def rowShift (ι : Type*) : Multiplicative (ι → ZMod 3) →* Perm (ι × ZMod 3) where
  toFun v :=
    { toFun := fun p => (p.1, p.2 + Multiplicative.toAdd v p.1)
      invFun := fun p => (p.1, p.2 - Multiplicative.toAdd v p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  map_one' := by
    ext p <;> simp
  map_mul' v w := by
    ext p <;> simp
    ring

theorem rowShift_apply {ι : Type*} (v : Multiplicative (ι → ZMod 3)) (i : ι) (t : ZMod 3) :
    rowShift ι v (i, t) = (i, t + Multiplicative.toAdd v i) := rfl

theorem rowShift_injective (ι : Type*) : Function.Injective (rowShift ι) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  have := congrArg (fun σ : Perm (ι × ZMod 3) => (σ (i, 0)).2) h
  simpa [rowShift_apply] using this

theorem rowShift_cube {ι : Type*} (v : Multiplicative (ι → ZMod 3)) : v ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3)]
  simp only [Nat.cast_ofNat]
  have : (3 : ZMod 3) = 0 := by decide
  rw [this, zero_smul]

variable {α : Type*}

open scoped Classical in
noncomputable def embedShift {ι : Type*} (j : ι × ZMod 3 → α) (hj : Function.Injective j) :
    Multiplicative (ι → ZMod 3) →* Perm α :=
  (Perm.extendDomainHom (p := (· ∈ Set.range j)) (Equiv.ofInjective j hj)).comp (rowShift ι)

theorem embedShift_apply_range {ι : Type*} (j : ι × ZMod 3 → α) (hj : Function.Injective j)
    (v : Multiplicative (ι → ZMod 3)) (i : ι) (t : ZMod 3) :
    embedShift j hj v (j (i, t)) = j (i, t + Multiplicative.toAdd v i) := by
  classical
  have := Perm.extendDomain_apply_image (rowShift ι v) (Equiv.ofInjective j hj) (i, t)
  simpa [embedShift, rowShift_apply] using this

theorem embedShift_apply_not_range {ι : Type*} (j : ι × ZMod 3 → α) (hj : Function.Injective j)
    (v : Multiplicative (ι → ZMod 3)) {y : α} (hy : y ∉ Set.range j) :
    embedShift j hj v y = y := by
  classical
  exact Perm.extendDomain_apply_not_subtype (rowShift ι v) (Equiv.ofInjective j hj) hy

theorem embedShift_injective {ι : Type*} (j : ι × ZMod 3 → α) (hj : Function.Injective j) :
    Function.Injective (embedShift j hj) := by
  classical
  exact (Perm.extendDomainHom_injective (Equiv.ofInjective j hj)).comp (rowShift_injective ι)

theorem embedShift_cube {ι : Type*} (j : ι × ZMod 3 → α) (hj : Function.Injective j)
    (v : Multiplicative (ι → ZMod 3)) : embedShift j hj v ^ 3 = 1 := by
  rw [← map_pow, rowShift_cube, map_one]

theorem embedShift_mem_alternatingGroup [Fintype α] [DecidableEq α] {ι : Type*} (j : ι × ZMod 3 → α)
    (hj : Function.Injective j) (v : Multiplicative (ι → ZMod 3)) :
    embedShift j hj v ∈ alternatingGroup α := by
  rw [mem_alternatingGroup]
  have h : sign (embedShift j hj v) ^ 3 = 1 := by
    rw [← map_pow, embedShift_cube, map_one]
  rcases Int.units_eq_one_or (sign (embedShift j hj v)) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem exists_elemAbelian_fixing {N : ℕ} (f : Fin N → ZMod 2) {ι : Type*} [Fintype ι]
    (j : ι × ZMod 3 → Fin N) (hj : Function.Injective j)
    (hrow : ∀ i t, f (j (i, t)) = f (j (i, 0))) :
    ∃ E : Subgroup (alternatingGroup (Fin N)), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ Fintype.card ι ∧ ∀ g ∈ E, g • f = f := by
  classical
  let Ψ : Multiplicative (ι → ZMod 3) →* alternatingGroup (Fin N) :=
    (embedShift j hj).codRestrict _ (embedShift_mem_alternatingGroup j hj)
  have hΨ : ∀ v, ((Ψ v : alternatingGroup (Fin N)) : Perm (Fin N)) = embedShift j hj v :=
    fun v => rfl
  have hΨinj : Function.Injective Ψ := by
    intro v w h
    apply embedShift_injective j hj
    rw [← hΨ, ← hΨ, h]
  have hfixf : ∀ v y, f (embedShift j hj v y) = f y := by
    intro v y
    by_cases hy : y ∈ Set.range j
    · obtain ⟨⟨i, t⟩, rfl⟩ := hy
      rw [embedShift_apply_range, hrow i (t + _), hrow i t]
    · rw [embedShift_apply_not_range j hj v hy]
  refine ⟨Ψ.range, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine isMulCommutative_iff.mpr ?_
    rintro ⟨_, v, rfl⟩ ⟨_, w, rfl⟩
    exact Subtype.ext (by simp [← map_mul, mul_comm])
  · rintro _ ⟨v, rfl⟩
    rw [← map_pow, rowShift_cube, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv.symm]
    simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]
  · rintro _ ⟨v, rfl⟩
    funext y
    change f ((((Ψ v)⁻¹ : alternatingGroup (Fin N)) : Perm (Fin N)) y) = f y
    rw [← map_inv, hΨ]
    exact hfixf _ y

theorem rankDropModel_altPerm {N : ℕ} (_hN : 5 ≤ N) :
    RankDropModel (alternatingGroup (Fin N)) (Fin N → ZMod 2) := by
  classical
  intro f
  let n : ZMod 2 → ℕ := fun y => Fintype.card {i // f i = y}
  let a : ZMod 2 → ℕ := fun y => n y / 3
  have hemb : ∀ y, Nonempty (Fin (a y) × ZMod 3 ↪ {i // f i = y}) := fun y =>
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
      change n y / 3 * 3 ≤ n y
      exact Nat.div_mul_le_self _ _)
  let e : ∀ y, Fin (a y) × ZMod 3 ↪ {i // f i = y} := fun y => Classical.choice (hemb y)
  let j : (Σ y : ZMod 2, Fin (a y)) × ZMod 3 → Fin N := fun p => (e p.1.1 (p.1.2, p.2) : Fin N)
  have hjf : ∀ p, f (j p) = p.1.1 := fun p => (e p.1.1 (p.1.2, p.2)).2
  have hj : Function.Injective j := by
    rintro ⟨⟨y, i⟩, t⟩ ⟨⟨y', i'⟩, t'⟩ h
    have hy : y = y' := by
      have := hjf ⟨⟨y, i⟩, t⟩
      rw [h, hjf] at this
      exact this.symm
    subst hy
    have := (e y).injective (Subtype.ext h)
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    rfl
  obtain ⟨E, hE, hcard, hfix⟩ := exists_elemAbelian_fixing f j hj (fun i t => by
    rw [hjf, hjf])
  have hsum : ∀ g : ZMod 2 → ℕ, ∑ y, g y = g 0 + g 1 := fun g => Fin.sum_univ_two g
  have hcardι : Fintype.card (Σ y : ZMod 2, Fin (a y)) = a 0 + a 1 := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hsum a
  have hN : n 0 + n 1 = N := by
    have h1 := Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    rw [Fintype.card_sigma, Fintype.card_fin] at h1
    rw [h1]
    exact (hsum n).symm
  refine ⟨E, a 0 + a 1, hE, hcard.trans (by rw [hcardι]), hfix, ?_⟩
  have := pRank_three_alternating_le (N := N)
  have h0 : a 0 = n 0 / 3 := rfl
  have h1 : a 1 = n 1 / 3 := rfl
  omega

end Drop

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
