module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResKacCheck
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacCheck
open scoped Matrix

namespace ExcKacNodes

section Comp

variable {τ : Tag} (K : KacData τ)

theorem zRel_symm {p : ℕ} {μ : Fin τ.rank → ℤ} {x y : Option (Fin τ.rank)}
    (h : K.ZRel p μ x y) : K.ZRel p μ y x :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by rw [iform_comm]; exact h.2.2.2⟩

theorem comp_eq_singleton {p : ℕ} {μ : Fin τ.rank → ℤ} {x : Option (Fin τ.rank)}
    (hx : K.IsZ p μ x) (hiso : ∀ y, ¬ K.ZRel p μ x y) : K.comp p μ x = {x} := by
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hxy⟩
    have key : ∀ a b, Relation.EqvGen (K.ZRel p μ) a b → (a = x ↔ b = x) := by
      intro a b hab
      induction hab with
      | rel a b h =>
        constructor
        · rintro rfl
          exact absurd h (hiso b)
        · rintro rfl
          exact absurd (zRel_symm K h) (hiso a)
      | refl a => exact Iff.rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    exact (key x y hxy).1 rfl
  · rintro rfl
    exact K.mem_comp_self hx

theorem combo_ind (y : Option (Fin τ.rank)) :
    K.combo (fun z => if z = y then 1 else 0) = K.extRoot y := by
  rw [KacData.combo, Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem extRoot_mem_rootsOf {C : Set (Option (Fin τ.rank))} {y : Option (Fin τ.rank)}
    (hy : y ∈ C) : K.extRoot y ∈ K.rootsOf C :=
  ⟨K.isRoot_extRoot y, fun z => if z = y then 1 else 0, fun z hz => by
    by_cases h : z = y
    · exact h ▸ hy
    · simp [h] at hz, Or.inl (combo_ind K y).symm⟩

theorem neg_extRoot_mem_rootsOf {C : Set (Option (Fin τ.rank))} {y : Option (Fin τ.rank)}
    (hy : y ∈ C) : -K.extRoot y ∈ K.rootsOf C :=
  ⟨IsRoot.neg (K.isRoot_extRoot y), fun z => if z = y then 1 else 0, fun z hz => by
    by_cases h : z = y
    · exact h ▸ hy
    · simp [h] at hz, Or.inr (by rw [combo_ind K y])⟩

theorem extRoot_ne_neg (x : Option (Fin τ.rank)) : K.extRoot x ≠ -K.extRoot x := by
  intro h
  have h0 : K.extRoot x = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]
    omega
  exact (K.isRoot_extRoot x).ne_zero h0

theorem rootsOf_singleton (x : Option (Fin τ.rank)) :
    K.rootsOf {x} = {K.extRoot x, -K.extRoot x} := by
  ext γ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hγ, n, hn, hγn⟩
    have hc : K.combo n = (n x : ℤ) • K.extRoot x := by
      rw [KacData.combo, Finset.sum_eq_single x]
      · intro b _ hb
        have : n b = 0 := by
          by_contra h
          exact hb (hn b h)
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ x) h
    rcases hγn with e | e
    · rw [hc] at e
      rcases hγ.eq_one_or_neg_one_of_eq_smul e with h1 | h1
      · left
        rw [e, h1, one_smul]
      · omega
    · have e' : γ = (-(n x : ℤ)) • K.extRoot x := by rw [e, hc, neg_smul]
      rcases hγ.eq_one_or_neg_one_of_eq_smul e' with h1 | h1
      · omega
      · right
        have h2 : (n x : ℤ) = 1 := by omega
        rw [e, hc, h2, one_smul]
  · rintro (rfl | rfl)
    · exact extRoot_mem_rootsOf K rfl
    · exact neg_extRoot_mem_rootsOf K rfl

theorem ncard_rootsOf_singleton (x : Option (Fin τ.rank)) : (K.rootsOf {x}).ncard = 2 := by
  rw [rootsOf_singleton, Set.ncard_pair (extRoot_ne_neg K x)]

theorem two_lt_ncard_rootsOf_comp {p : ℕ} {μ : Fin τ.rank → ℤ} {x y : Option (Fin τ.rank)}
    (hxy : K.ZRel p μ x y) (hd : K.extRoot x ≠ K.extRoot y ∧ K.extRoot x ≠ -K.extRoot y) :
    2 < (K.rootsOf (K.comp p μ x)).ncard := by
  have hx : x ∈ K.comp p μ x := K.mem_comp_self hxy.1
  have hy : y ∈ K.comp p μ x := ⟨hxy.2.1, Relation.EqvGen.rel _ _ hxy⟩
  have hfin : (K.rootsOf (K.comp p μ x)).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1
  rw [Set.two_lt_ncard_iff hfin]
  refine ⟨K.extRoot x, -K.extRoot x, K.extRoot y, extRoot_mem_rootsOf K hx,
    neg_extRoot_mem_rootsOf K hx, extRoot_mem_rootsOf K hy, extRoot_ne_neg K x, hd.1, ?_⟩
  intro h
  exact hd.2 (neg_eq_iff_eq_neg.1 h)

end Comp

section A2

variable {τ : Tag}

theorem A2T.isRoot {a b : Fin τ.rank → ℤ} (h : A2T τ a b) :
    IsRoot τ (a + b) ∧ ¬ IsRoot τ (a - b) ∧ ¬ IsRoot τ ((2 : ℤ) • a + b) ∧
      ¬ IsRoot τ (a + (2 : ℤ) • b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨isRoot_iff_mem_artifactRoots.2 h1, fun h => h2 (isRoot_iff_mem_artifactRoots.1 h),
    fun h => h3 (isRoot_iff_mem_artifactRoots.1 h),
    fun h => h4 (isRoot_iff_mem_artifactRoots.1 h)⟩

theorem hasA2Pair_image (v : WeylGroup τ) {S : Set (Fin τ.rank → ℤ)} {a b : Fin τ.rank → ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (h : A2T τ a b) :
    HasA2Pair τ ((fun α => v • α) '' S) := by
  obtain ⟨h1, h2, h3, h4⟩ := A2T.isRoot h
  refine ⟨v • a, ⟨a, ha, rfl⟩, v • b, ⟨b, hb, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add]
    exact IsRoot.smul h1 v
  · rw [← smul_sub, isRoot_smul_iff]
    exact h2
  · rw [show (2 : ℤ) • (v • a) + v • b = v • ((2 : ℤ) • a + b) by rw [smul_add, smul_comm],
      isRoot_smul_iff]
    exact h3
  · rw [show v • a + (2 : ℤ) • (v • b) = v • (a + (2 : ℤ) • b) by rw [smul_add, smul_comm],
      isRoot_smul_iff]
    exact h4

end A2

section Bridge

variable {τ : Tag}

theorem isZ_iff (K : KacData τ) (μ : Fin τ.rank → ℤ) (x : Option (Fin τ.rank)) :
    K.IsZ 3 μ x ↔ zT K.θ μ x := by
  cases x <;> exact Iff.rfl

theorem extRoot_eq (K : KacData τ) : K.extRoot = eV K.θ := by
  funext x
  cases x <;> rfl

theorem zRel_iff (K : KacData τ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank)))
    (hadj : ∀ x y, (x ≠ y ∧ iform (eV K.θ x) (eV K.θ y) ≠ 0) ↔ adjL E x y)
    (μ : Fin τ.rank → ℤ) (x y : Option (Fin τ.rank)) :
    K.ZRel 3 μ x y ↔ nT K.θ μ E x y := by
  show (K.IsZ 3 μ x ∧ K.IsZ 3 μ y ∧ (x ≠ y ∧ iform (K.extRoot x) (K.extRoot y) ≠ 0)) ↔ _
  rw [extRoot_eq K]
  exact and_congr (isZ_iff K μ x) (and_congr (isZ_iff K μ y) (hadj x y))

theorem forall_normal_of_boxAll (K : KacData τ) (bnd : Fin τ.rank → ℕ)
    (hbnd : ∀ j, 3 < K.θ j * (((bnd j : ℕ) : ℤ) + 1)) {P : (Fin τ.rank → ℤ) → Prop}
    (h : BoxAll K.θ bnd P) : ∀ μ, K.IsNormal 3 μ → P μ := by
  intro μ hμ
  have hnn : ∀ j, 0 ≤ μ j := hμ.1
  have hle : ∀ j, μ j < ((bnd j : ℕ) : ℤ) + 1 := by
    intro j
    by_contra hcon
    push Not at hcon
    have h1 : K.θ j * μ j ≤ K.θ ⬝ᵥ μ :=
      Finset.single_le_sum (f := fun i => K.θ i * μ i)
        (fun i _ => mul_nonneg (K.θ_nonneg i) (hnn i)) (Finset.mem_univ j)
    have h4 : K.θ j * (((bnd j : ℕ) : ℤ) + 1) ≤ K.θ j * μ j :=
      mul_le_mul_of_nonneg_left hcon (K.θ_nonneg j)
    have h2 := hμ.2
    have h3 := hbnd j
    push_cast at h2
    linarith
  let m : (j : Fin τ.rank) → Fin (bnd j + 1) := fun j =>
    ⟨(μ j).toNat, by have := hle j; have := hnn j; omega⟩
  have hm : (fun j => ((m j : ℕ) : ℤ)) = μ := by
    funext j
    exact Int.toNat_of_nonneg (hnn j)
  have := h m (by rw [hm]; exact hμ.2)
  rwa [hm] at this

end Bridge

open CFSG.LieType.AlgebraicGroups (rootCharHom)

theorem excKac_of_checks {τ : Tag}
    (K : KacData τ) (hK : K.Facts)
    (E G : List (Option (Fin τ.rank) × Option (Fin τ.rank))) (bnd : Fin τ.rank → ℕ)
    (hbnd : ∀ j, 3 < K.θ j * (((bnd j : ℕ) : ℤ) + 1))
    (hadj : ∀ x y, (x ≠ y ∧ iform (eV K.θ x) (eV K.θ y) ≠ 0) ↔ adjL E x y)
    (hdist : ∀ x y, x ≠ y → eV K.θ x ≠ eV K.θ y ∧ eV K.θ x ≠ -eV K.θ y)
    (hG : ∀ x y, (x, y) ∈ G → A2T τ (eV K.θ x) (eV K.θ y))
    (hQ1 : BoxAll K.θ bnd fun μ => Q1 K.θ μ E G)
    (hQ2 : (τ = Tag.F4 ∨ τ = Tag.E8) → BoxAll K.θ bnd fun μ => Q2 K.θ μ E)
    (hQ3 : (τ = Tag.E6 ∨ τ = Tag.E7) → BoxAll K.θ bnd fun μ => Q3 K.θ μ E) :
    ExcKac τ := by
  intro L _ _ h3 a ha _
  haveI : NeZero ((3 : ℕ) : L) := ⟨by simpa using h3⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  obtain ⟨ζ, hζ⟩ := hζ0.isUnit (by norm_num)
  have hζ' : IsPrimitiveRoot (ζ : L) 3 := hζ ▸ hζ0
  obtain ⟨v, μ, hμ, hcls⟩ := K.exists_smul_rootsOf hK (N := 3) (by norm_num) hζ' a ha
  have hzr := fun x y => zRel_iff K E hadj μ x y
  have hd : ∀ x y, x ≠ y → K.extRoot x ≠ K.extRoot y ∧ K.extRoot x ≠ -K.extRoot y := by
    intro x y hxy
    rw [extRoot_eq K]
    exact hdist x y hxy
  have hQ1' := forall_normal_of_boxAll K bnd hbnd hQ1 μ hμ
  have H1 : ∀ x, K.IsZ 3 μ x → (∀ y, ¬ K.ZRel 3 μ x y) ∨
      (∃ y, K.ZRel 3 μ x y ∧ A2T τ (K.extRoot x) (K.extRoot y)) ∨
      (∃ y, K.ZRel 3 μ x y ∧ ∃ z, K.ZRel 3 μ y z ∧ A2T τ (K.extRoot y) (K.extRoot z)) := by
    intro x hx
    rcases hQ1' x ((isZ_iff K μ x).1 hx) with h0 | ⟨y, hy, hxy⟩ | ⟨y, hy, z, hz, hyz⟩
    · left
      exact fun y hy => h0 y ((hzr x y).1 hy)
    · right
      left
      exact ⟨y, (hzr x y).2 hy, by rw [extRoot_eq K]; exact hG x y hxy⟩
    · right
      right
      exact ⟨y, (hzr x y).2 hy, z, (hzr y z).2 hz, by rw [extRoot_eq K]; exact hG y z hyz⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx, hi⟩ := hcls i
    rw [hi]
    rcases H1 x hx with hiso | ⟨y, hy, hA⟩ | ⟨y, hy, z, hz, hA⟩
    · left
      rw [Set.ncard_image_of_injective _ (MulAction.injective v), comp_eq_singleton K hx hiso,
        ncard_rootsOf_singleton]
    · right
      have hyc : y ∈ K.comp 3 μ x := ⟨hy.2.1, Relation.EqvGen.rel _ _ hy⟩
      exact hasA2Pair_image v (extRoot_mem_rootsOf K (K.mem_comp_self hx))
        (extRoot_mem_rootsOf K hyc) hA
    · right
      have hyc : y ∈ K.comp 3 μ x := ⟨hy.2.1, Relation.EqvGen.rel _ _ hy⟩
      have hzc : z ∈ K.comp 3 μ x := ⟨hz.2.1, (Relation.EqvGen.rel _ _ hy).trans _ _ _
        (Relation.EqvGen.rel _ _ hz)⟩
      exact hasA2Pair_image v (extRoot_mem_rootsOf K hyc) (extRoot_mem_rootsOf K hzc) hA
  · intro hτ i
    obtain ⟨x, hx, hi⟩ := hcls i
    have hQ2' := forall_normal_of_boxAll K bnd hbnd (hQ2 hτ) μ hμ
    have hni := hQ2' x ((isZ_iff K μ x).1 hx)
    obtain ⟨y, hy⟩ : ∃ y, nT K.θ μ E x y := by
      by_contra hcon
      exact hni fun y hy => hcon ⟨y, hy⟩
    have hzxy := (hzr x y).2 hy
    rw [hi, Set.ncard_image_of_injective _ (MulAction.injective v)]
    exact (two_lt_ncard_rootsOf_comp K hzxy (hd x y hzxy.2.2.1)).ne'
  · intro hτ i j hi hj
    obtain ⟨x, hx, hxi⟩ := hcls i
    obtain ⟨x', hx', hxj⟩ := hcls j
    rw [hxi, Set.ncard_image_of_injective _ (MulAction.injective v)] at hi
    rw [hxj, Set.ncard_image_of_injective _ (MulAction.injective v)] at hj
    have hQ3' := forall_normal_of_boxAll K bnd hbnd (hQ3 hτ) μ hμ
    have iso : ∀ z, K.IsZ 3 μ z → (K.rootsOf (K.comp 3 μ z)).ncard = 2 → Iso K.θ μ E z := by
      intro z hz h y hy
      have hzz := (hzr z y).2 hy
      have := two_lt_ncard_rootsOf_comp K hzz (hd z y hzz.2.2.1)
      omega
    have hxx' : x = x' := hQ3' x x' ((isZ_iff K μ x).1 hx) ((isZ_iff K μ x').1 hx')
      (iso x hx hi) (iso x' hx' hj)
    subst hxx'
    have hmem : ∀ k, componentRoots (rootCharHom a) k =
        (fun α => v • α) '' K.rootsOf (K.comp 3 μ x) →
        v • K.extRoot x ∈ componentRoots (rootCharHom a) k := by
      intro k hk
      rw [hk]
      exact ⟨K.extRoot x, extRoot_mem_rootsOf K (K.mem_comp_self hx), rfl⟩
    obtain ⟨h1, hq1⟩ := hmem i hxi
    obtain ⟨h2, hq2⟩ := hmem j hxj
    exact hq1.symm.trans hq2

end ExcKacNodes

end CFSG.HardMathSupport.Dickson.Sec6.I1431
