module

public import CFSG.LieType.Chevalley.SimpleRootSubgroupStructure
public import CFSG.LieType.Chevalley.CartanColumns
public import CFSG.LieType.Chevalley.OppositeNoncommutativity
public import CFSG.GroupActions.CoreFreeMaximal
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GroupActions

theorem generated_group_finite
    (τ : Tag) (K : Type*) [Field K] [Finite K] :
    Finite (adjointGroup τ K) := by
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  infer_instance

variable {τ : Tag} {K : Type*} [Field K]

@[expose] def xElt
    (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩

@[expose] def yElt
    (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩

@[expose] def dElt
    (i : Fin τ.rank) (t : Kˣ) : adjointGroup τ K :=
  ⟨torusElt τ K i t, torusElt_mem_adjointGroup i t⟩

theorem xElt_mem_simplePosSubgroup
    (i : Fin τ.rank) (c : K) :
    xElt i c ∈ simplePosSubgroup τ K i :=
  ⟨c, rfl⟩

theorem yElt_mem_simpleNegSubgroup
    (i : Fin τ.rank) (c : K) :
    yElt i c ∈ simpleNegSubgroup τ K i :=
  ⟨c, rfl⟩

theorem dElt_mul_xElt_mul_inv
    (i j : Fin τ.rank) (t : Kˣ) (c : K) :
    dElt i t * xElt j c * (dElt i t)⁻¹ = xElt j (((t ^ τ.cartan i j : Kˣ) : K) * c) :=
  Subtype.ext (simple_torus_root_conjugation τ K i j t c).1

theorem dElt_mul_yElt_mul_inv
    (i j : Fin τ.rank) (t : Kˣ) (c : K) :
    dElt i t * yElt j c * (dElt i t)⁻¹ = yElt j (((t ^ (-τ.cartan i j) : Kˣ) : K) * c) :=
  Subtype.ext (simple_torus_root_conjugation τ K i j t c).2

theorem mem_commutator_of_scaling {Γ : Type*} [Group Γ] (u : Multiplicative K →* Γ) (h : Γ)
    {lam : K} (hlam : lam ≠ 1)
    (hconj : ∀ a : K, h * u (Multiplicative.ofAdd a) * h⁻¹ = u (Multiplicative.ofAdd (lam * a)))
    (c : K) : u (Multiplicative.ofAdd c) ∈ commutator Γ :=
  (additive_scaling_commutator u h lam (lam - 1)⁻¹ (inv_mul_cancel₀ (sub_ne_zero.2 hlam)) hconj
    c).2

theorem odd_characteristic_perfect
    (τ : Tag) (K : Type*) [Field K] (hK : ringChar K ≠ 2) :
    commutator (adjointGroup τ K) = ⊤ := by
  have h2 : (-1 : K) ≠ 1 := fun h => by
    have : (2 : K) = 0 := by linear_combination -h
    exact Ring.two_ne_zero hK this
  have hmem : ∀ j : Fin τ.rank, ∀ c : K,
      xElt j c ∈ commutator (adjointGroup τ K) ∧ yElt j c ∈ commutator (adjointGroup τ K) := by
    intro j c
    obtain ⟨i, -, hodd⟩ := cartan_odd_column τ j
    have hodd' : Odd (τ.cartan i j) := by rcases hodd with h | h <;> rw [h] <;> decide
    have hodd'' : Odd (-τ.cartan i j) := hodd'.neg
    let ux : Multiplicative K →* adjointGroup τ K :=
      (simplePosSubgroup τ K j).subtype.comp (simplePosHom τ K j)
    let uy : Multiplicative K →* adjointGroup τ K :=
      (simpleNegSubgroup τ K j).subtype.comp (simpleNegHom τ K j)
    refine ⟨mem_commutator_of_scaling ux (dElt i (-1)) h2 (fun a => ?_) c,
      mem_commutator_of_scaling uy (dElt i (-1)) h2 (fun a => ?_) c⟩
    · change dElt i (-1) * xElt j a * (dElt i (-1))⁻¹ = xElt j (-1 * a)
      rw [dElt_mul_xElt_mul_inv, hodd'.neg_one_zpow, Units.val_neg, Units.val_one]
    · change dElt i (-1) * yElt j a * (dElt i (-1))⁻¹ = yElt j (-1 * a)
      rw [dElt_mul_yElt_mul_inv, hodd''.neg_one_zpow, Units.val_neg, Units.val_one]
  rw [eq_top_iff, ← iSup_simplePosSubgroup_sup_simpleNegSubgroup]
  refine iSup_le fun j => sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hg
    rw [show g = xElt j c from Subtype.ext hc]
    exact (hmem j c).1
  · obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hg
    rw [show g = yElt j c from Subtype.ext hc]
    exact (hmem j c).2

@[expose] def rankOneSubgroup
    (i : Fin τ.rank) : Subgroup (adjointGroup τ K) :=
  simplePosSubgroup τ K i ⊔ simpleNegSubgroup τ K i

theorem dElt_mem_rankOneSubgroup
    (i : Fin τ.rank) (t : Kˣ) : dElt i t ∈ rankOneSubgroup i := by
  have hw : ∀ s : Kˣ, (⟨weylElt τ K i s, weylElt_mem_adjointGroup i s⟩ : adjointGroup τ K) =
      xElt i (s : K) * yElt i (-((s⁻¹ : Kˣ) : K)) * xElt i (s : K) :=
    fun s => Subtype.ext (weylElt_eq_xUnit_mul i s)
  have hd : dElt i t = (⟨weylElt τ K i t, weylElt_mem_adjointGroup i t⟩ : adjointGroup τ K) *
      ⟨weylElt τ K i (-1), weylElt_mem_adjointGroup i (-1)⟩ := rfl
  have hx : ∀ a, xElt i a ∈ rankOneSubgroup (K := K) i := fun a =>
    Subgroup.mem_sup_left (xElt_mem_simplePosSubgroup i a)
  have hy : ∀ a, yElt i a ∈ rankOneSubgroup (K := K) i := fun a =>
    Subgroup.mem_sup_right (yElt_mem_simpleNegSubgroup i a)
  rw [hd, hw, hw]
  exact mul_mem (mul_mem (mul_mem (hx _) (hy _)) (hx _)) (mul_mem (mul_mem (hx _) (hy _)) (hx _))

theorem rank_one_scalar_perfect
    (τ : Tag) (K : Type*) [Field K] (i : Fin τ.rank) :
    (∀ t : Kˣ, (t : K) ^ 2 ≠ 1 → commutator (rankOneSubgroup (τ := τ) (K := K) i) = ⊤) ∧
    ((4 : ℕ∞) ≤ ENat.card K → commutator (rankOneSubgroup (τ := τ) (K := K) i) = ⊤) := by
  have hmain : ∀ t : Kˣ, (t : K) ^ 2 ≠ 1 →
      commutator (rankOneSubgroup (τ := τ) (K := K) i) = ⊤ := by
    intro t ht
    set G := rankOneSubgroup (τ := τ) (K := K) i
    have haii : τ.cartan i i = 2 := τ.cartan_self i
    let d : G := ⟨dElt i t, dElt_mem_rankOneSubgroup i t⟩
    let ux : Multiplicative K →* G :=
      (Subgroup.inclusion (le_sup_left : simplePosSubgroup τ K i ≤ G)).comp (simplePosHom τ K i)
    let uy : Multiplicative K →* G :=
      (Subgroup.inclusion (le_sup_right : simpleNegSubgroup τ K i ≤ G)).comp
        (simpleNegHom τ K i)
    have ht0 : (t : K) ≠ 0 := t.ne_zero
    have hlx : ((t ^ τ.cartan i i : Kˣ) : K) ≠ 1 := by
      rw [haii, zpow_two, ← sq, Units.val_pow_eq_pow_val]
      exact ht
    have hly : ((t ^ (-τ.cartan i i) : Kˣ) : K) ≠ 1 := by
      rw [haii, zpow_neg, zpow_two, ← sq, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      exact fun h => ht (by rw [← inv_inj, h, inv_one])
    have hx : ∀ c, ux (Multiplicative.ofAdd c) ∈ commutator G :=
      mem_commutator_of_scaling ux d hlx fun a => Subtype.ext (dElt_mul_xElt_mul_inv i i t a)
    have hy : ∀ c, uy (Multiplicative.ofAdd c) ∈ commutator G :=
      mem_commutator_of_scaling uy d hly fun a => Subtype.ext (dElt_mul_yElt_mul_inv i i t a)
    have hle : G ≤ (commutator G).map G.subtype := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hg
        refine ⟨ux (Multiplicative.ofAdd c), hx c, Subtype.ext ?_⟩
        exact hc.symm
      · obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hg
        refine ⟨uy (Multiplicative.ofAdd c), hy c, Subtype.ext ?_⟩
        exact hc.symm
    rw [eq_top_iff]
    intro g _
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  refine ⟨hmain, fun hK => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 := by
    by_contra! h
    have hsub : (Set.univ : Set K) ⊆ {0, 1, -1} := fun t _ => by
      by_cases h0 : t = 0
      · exact Or.inl h0
      by_cases h1 : t = 1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (h t h0 h1))
    have hcard : ENat.card K ≤ 3 := by
      rw [← Set.encard_univ]
      refine (Set.encard_le_encard hsub).trans ?_
      refine (Set.encard_insert_le _ _).trans ?_
      have := Set.encard_insert_le ({-1} : Set K) (1 : K)
      rw [Set.encard_singleton] at this
      calc ({1, -1} : Set K).encard + 1 ≤ (1 + 1) + 1 := by gcongr
        _ = 3 := by norm_num
    exact absurd (hK.trans hcard) (by norm_num)
  refine hmain (Units.mk0 t ht.1) fun h => ?_
  have h' : (t - 1) * (t + 1) = 0 := by
    have : t ^ 2 = 1 := h
    linear_combination this
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact ht.2.1 (sub_eq_zero.1 h1)
  · exact ht.2.2 (eq_neg_of_add_eq_zero_left h1)

theorem nontrivial_adjointQuotient
    (τ : Tag) (K : Type) [Field K] :
    Nontrivial (AdjointQuotient τ K) :=
  (opposite_simple_root_noncommutativity τ K).2.2.2

theorem untwisted_chevalley_model_nontrivial
    (G : Type) [Group G]
    (t : Assembly.LowTwoRank.StatedLieTag)
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (p f : ℕ)
    (h : ChevalleyExceptionalModel G t p f) : Nontrivial G := by
  have key : ∀ τ : Tag, ∀ q, UntwistedChevalleyModel G τ q → Nontrivial G := by
    rintro τ q ⟨K, _, _, -, ⟨e⟩⟩
    have := nontrivial_adjointQuotient τ K
    exact e.toEquiv.nontrivial
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact key _ _ h.2
  · exact key _ _ h.2
  · exact key _ _ h.2
  · exact key _ _ h.2
  · exact key _ _ h.2

end CFSG.LieType.Chevalley
