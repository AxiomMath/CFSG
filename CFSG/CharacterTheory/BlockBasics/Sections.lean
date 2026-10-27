module

public import CFSG.CharacterTheory.BlockBasics.Defects
public import CFSG.CharacterTheory.BlockSectionOrthogonality
public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalSectionIntertwining

public section

open scoped Classical

namespace CFSG.BlockBasics

open CFSG CFSG.BrauerThirdMainTheorem.Helpers

theorem exists_pPart (p : ℕ) (hp : p.Prime) {G : Type*} [Group G] [Finite G] (g : G) :
    ∃ a : G, BlocksIsPPart p g a := by
  obtain ⟨a, b, e, -, -, hab, hprod, hord, hcop⟩ :=
    CFSG.TwoRankLowerBound.Helpers.finite_prime_primary_factorization g p hp
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).mp hord
  exact ⟨a, b, hprod, hab.eq ▸ hprod, ⟨n, hn⟩, orderOf_pos b, hcop.symm⟩

section Stability

variable {G : Type} [Group G] [Fintype G]

theorem blocksInnerProduct_apply (f χ : G → ℂ) :
    BlocksInnerProduct f χ = (Nat.card G : ℂ)⁻¹ * ∑ y : G, f y * starRingEnd ℂ (χ y) := rfl

theorem blockProjection_apply {B : Set (G → ℂ)} (hB : B.Finite) (f : G → ℂ) (x : G) :
    (∑ᶠ χ ∈ B, BlocksInnerProduct f χ • χ) x =
      (Nat.card G : ℂ)⁻¹ * ∑ y : G, f y * ∑ χ ∈ hB.toFinset, χ x * starRingEnd ℂ (χ y) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hB, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, blocksInnerProduct_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun χ _ => ?_
  ring

theorem blockProjection_eq_self_of_mem_span {B : Set (G → ℂ)} (hBirr : B ⊆ BlocksIrr G)
    {f : G → ℂ} (hf : f ∈ Submodule.span ℂ B) :
    (∑ᶠ χ ∈ B, BlocksInnerProduct f χ • χ) = f := by
  have hB : B.Finite := (irr_finite G).subset hBirr
  have horth := (irreducible_character_basis G).1
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      rw [finsum_mem_eq_finite_toFinset_sum _ hB, Finset.sum_eq_single ψ]
      · rw [horth ψ (hBirr hψ) ψ (hBirr hψ), ite_eq_left rfl, one_smul]
      · intro χ hχ hne
        rw [horth ψ (hBirr hψ) χ (hBirr (by simpa using hχ)), ite_eq_right (Ne.symm hne),
          zero_smul]
      · intro hnot
        exact absurd (by simpa using hψ) hnot
  | zero =>
      simp [blocksInnerProduct_apply]
  | add f g _ _ hf hg =>
      conv_rhs => rw [← hf, ← hg]
      rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
        finsum_mem_eq_finite_toFinset_sum _ hB, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [← add_smul]
      congr 1
      simp only [blocksInnerProduct_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib,
        mul_add]
  | smul c f _ hf =>
      conv_rhs => rw [← hf]
      rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [smul_smul]
      congr 1
      simp only [blocksInnerProduct_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring

theorem blockProjection_mem_span {B : Set (G → ℂ)} (hB : B.Finite) (f : G → ℂ) :
    (∑ᶠ χ ∈ B, BlocksInnerProduct f χ • χ) ∈ Submodule.span ℂ B := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hB]
  exact Submodule.sum_mem _ fun χ hχ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (by simpa using hχ))

theorem blocksInnerProduct_span_eq_zero {B C : Set (G → ℂ)} (hBirr : B ⊆ BlocksIrr G)
    (hCirr : C ⊆ BlocksIrr G) (hdisj : Disjoint B C) {f h : G → ℂ}
    (hf : f ∈ Submodule.span ℂ B) (hh : h ∈ Submodule.span ℂ C) :
    BlocksInnerProduct f h = 0 := by
  have horth := (irreducible_character_basis G).1
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      induction hh using Submodule.span_induction with
      | mem ψ hψ =>
          rw [horth χ (hBirr hχ) ψ (hCirr hψ), ite_eq_right]
          rintro rfl
          exact Set.disjoint_left.mp hdisj hχ hψ
      | zero => simp [blocksInnerProduct_apply]
      | add a b _ _ ha hb =>
          simp only [blocksInnerProduct_apply, Pi.add_apply, map_add, mul_add,
            Finset.sum_add_distrib] at ha hb ⊢
          rw [ha, hb, add_zero]
      | smul c a _ ha =>
          simp only [blocksInnerProduct_apply, Pi.smul_apply, smul_eq_mul, map_mul] at ha ⊢
          have hsum : ∑ y, χ y * (starRingEnd ℂ c * starRingEnd ℂ (a y)) =
              starRingEnd ℂ c * ∑ y, χ y * starRingEnd ℂ (a y) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
          rw [hsum]
          have h0 : ∑ y, χ y * starRingEnd ℂ (a y) = 0 := by
            have hcard : (Nat.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.card_pos.ne')
            exact (mul_eq_zero.mp ha).resolve_left hcard
          rw [h0, mul_zero, mul_zero]
  | zero => simp [blocksInnerProduct_apply]
  | add a b _ _ ha hb =>
      simp only [blocksInnerProduct_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib,
        mul_add] at ha hb ⊢
      rw [ha, hb, add_zero]
  | smul c a _ ha =>
      simp only [blocksInnerProduct_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
      have hsum : ∑ y, c * a y * starRingEnd ℂ (h y) = c * ∑ y, a y * starRingEnd ℂ (h y) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hsum, mul_left_comm, ha, mul_zero]

end Stability

theorem blockProjection_indicator_comm (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) (hpm : (p : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Fintype G]
    (B : Set (G → ℂ)) (hB : BlocksIsBlock m G B) (D : Set G)
    (hD : ∀ g h gp hp' : G, g ∈ D → BlocksIsPPart p g gp → BlocksIsPPart p h hp' →
      IsConj gp hp' → h ∈ D) (f : G → ℂ) :
    (∑ᶠ χ ∈ B, BlocksInnerProduct (D.indicator f) χ • χ) =
      D.indicator (∑ᶠ χ ∈ B, BlocksInnerProduct f χ • χ) := by
  have hBirr := block_subset_irr m hB
  have hBfin : B.Finite := (irr_finite G).subset hBirr
  have hK : ∀ x y : G, (x ∈ D ↔ y ∉ D) →
      ∑ χ ∈ hBfin.toFinset, χ x * starRingEnd ℂ (χ y) = 0 := by
    intro x y hxy
    obtain ⟨xp, hxp⟩ := exists_pPart p hp x
    obtain ⟨yp, hyp⟩ := exists_pPart p hp y
    have hnot : ¬ IsConj xp yp := by
      intro hconj
      by_cases hx : x ∈ D
      · exact (hxy.mp hx) (hD x y xp yp hx hxp hyp hconj)
      · have hy : y ∈ D := by
          by_contra hy
          exact hx (hxy.mpr hy)
        exact hx (hD y x yp xp hy hyp hxp hconj.symm)
    have h := CFSG.BlockSectionOrthogonality.block_section_orthogonality p hp m hm hpm G B hB x y
      xp yp hxp hyp hnot
    rwa [finsum_mem_eq_finite_toFinset_sum _ hBfin] at h
  funext x
  rw [blockProjection_apply hBfin, Set.indicator_apply, blockProjection_apply hBfin]
  by_cases hx : x ∈ D
  · rw [ite_eq_left hx]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ D
    · rw [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, hK x y ⟨fun _ => hy, fun _ => hx⟩, mul_zero]
  · rw [ite_eq_right hx]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y ∈ D
    · rw [hK x y ⟨fun h => absurd h hx, fun h => absurd hy h⟩, mul_zero]
    · rw [Set.indicator_of_notMem hy, zero_mul]

theorem indicator_mem_span_block (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) (hpm : (p : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Fintype G]
    (B : Set (G → ℂ)) (hB : BlocksIsBlock m G B) (D : Set G)
    (hD : ∀ g h gp hp' : G, g ∈ D → BlocksIsPPart p g gp → BlocksIsPPart p h hp' →
      IsConj gp hp' → h ∈ D) {f : G → ℂ} (hf : f ∈ Submodule.span ℂ B) :
    D.indicator f ∈ Submodule.span ℂ B := by
  have hBirr := block_subset_irr m hB
  have h := blockProjection_indicator_comm p hp m hm hpm G B hB D hD f
  rw [blockProjection_eq_self_of_mem_span hBirr hf] at h
  rw [← h]
  exact blockProjection_mem_span ((irr_finite G).subset hBirr) _

theorem block_section_restriction_stability (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) [CharP (BlocksAlgInt ⧸ m) p] (G : Type) [Group G] [Fintype G]
    (B : Set (G → ℂ)) (hB : BlocksIsBlock m G B) (D : Set G)
    (hD : ∀ g h gp hp' : G, g ∈ D → BlocksIsPPart p g gp → BlocksIsPPart p h hp' →
      IsConj gp hp' → h ∈ D) :
    let PB : (G → ℂ) → (G → ℂ) := fun f => ∑ᶠ χ ∈ B, BlocksInnerProduct f χ • χ
    (∀ f : G → ℂ, PB (D.indicator f) = D.indicator (PB f)) ∧
    (∀ f ∈ Submodule.span ℂ B, D.indicator f ∈ Submodule.span ℂ B) ∧
    ∀ C : Set (G → ℂ), BlocksIsBlock m G C → B ≠ C →
      ∀ f ∈ Submodule.span ℂ B, ∀ h ∈ Submodule.span ℂ C,
        BlocksInnerProduct (D.indicator f) (D.indicator h) = 0 := by
  intro PB
  have hpm := prime_mem_of_charP p m
  refine ⟨blockProjection_indicator_comm p hp m hm hpm G B hB D hD,
    fun f hf => indicator_mem_span_block p hp m hm hpm G B hB D hD hf,
    fun C hC hBC f hf h hh => ?_⟩
  have hdisj : Disjoint B C := by
    rw [Set.disjoint_left]
    intro χ hχB hχC
    exact hBC (blocks_eq_of_common_member m hB hC hχB hχC)
  exact blocksInnerProduct_span_eq_zero (block_subset_irr m hB) (block_subset_irr m hC) hdisj
    (indicator_mem_span_block p hp m hm hpm G B hB D hD hf)
    (indicator_mem_span_block p hp m hm hpm G C hC D hD hh)

theorem blockProjection_eq_characterSubsetProjection (m : Ideal BlocksAlgInt) [m.IsMaximal]
    {E : Type} [Group E] [Fintype E]
    (basis : CFSG.TwoRankLowerBound.Helpers.FiniteIrreducibleCharacterBasis E) (l : basis.index)
    (a : E → ℂ) :
    (∑ᶠ χ ∈ BlocksBlockOf m E (basis.representation l).character, BlocksInnerProduct a χ • χ) =
      CFSG.TwoRankLowerBound.Helpers.characterSubsetProjection basis
        (CFSG.TwoRankLowerBound.Helpers.coefficientBlock basis
          (CFSG.TwoRankLowerBound.Helpers.localizedComplexIntegerRing m) l) a := by
  rw [← coefficientBlock_image basis m l]
  have hinj : Set.InjOn (fun l => (basis.representation l).character)
      ((CFSG.TwoRankLowerBound.Helpers.coefficientBlock basis
        (CFSG.TwoRankLowerBound.Helpers.localizedComplexIntegerRing m) l : Finset _) : Set _) :=
    fun _ _ _ _ h => basis.distinct h
  rw [finsum_mem_image hinj, finsum_mem_coe_finset]
  change _ = ∑ l' ∈ _, CFSG.TwoRankLowerBound.Helpers.characterPairing a
    (basis.representation l').character • (basis.representation l').character
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [blocksInnerProduct_eq_characterPairing a
    (AddSubgroup.subset_closure (basis_character_mem_irr basis l'))]

theorem centralizer_zpowers_eq_centralizer_singleton {G : Type*} [Group G] (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h u (Subgroup.mem_zpowers u)).symm
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left h.symm k).eq)

theorem principal_local_section_projection_aux (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    [hm : m.IsMaximal] [CharP (BlocksAlgInt ⧸ m) p] (G : Type) [Group G] [Fintype G]
    (u : G) (n : ℕ) (hu : orderOf u = p ^ n) (f : G → ℂ) (hf : BlocksIsClassFunction f)
    (C : Subgroup G) (hC : C = Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G)) :
    ({x : C | BlocksIsPPart p (x : G) u} : Set C).indicator
        (∑ᶠ χ ∈ BlocksPrincipalBlock m C, BlocksInnerProduct (fun x : C => f x) χ • χ) =
      ({x : C | BlocksIsPPart p (x : G) u} : Set C).indicator
        (fun x : C => (∑ᶠ χ ∈ BlocksPrincipalBlock m G, BlocksInnerProduct f χ • χ) x) := by
  subst hC
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨localBasis⟩ :=
    CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists
      (G := Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G))
  obtain ⟨l0, hl0⟩ := exists_label_of_mem_irr basis (trivial_mem_irr G)
  obtain ⟨l0', hl0'⟩ := exists_label_of_mem_irr localBasis (trivial_mem_irr _)
  have hprincipal : BlocksPrincipalBlock m G = BlocksBlockOf m G (basis.representation l0).character
    := by rw [hl0]; rfl
  have hprincipal' : BlocksPrincipalBlock m (Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G)) =
      BlocksBlockOf m _ (localBasis.representation l0').character := by rw [hl0']; rfl
  rw [hprincipal, hprincipal', blockProjection_eq_characterSubsetProjection m localBasis l0',
    blockProjection_eq_characterSubsetProjection m basis l0]
  funext x
  by_cases hx : x ∈ ({x : Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) |
      BlocksIsPPart p (x : G) u} : Set _)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    obtain ⟨b, hub, hbu, -, -, hbcop⟩ := hx
    have huinv : orderOf u⁻¹ ∣ p ^ n := by rw [orderOf_inv, hu]
    let uC : Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) :=
      ⟨u⁻¹, CFSG.TwoRankLowerBound.Helpers.element_mem_centralizer_zpowers u⁻¹⟩
    let ρ : Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) := uC⁻¹ * x⁻¹
    have hρval : (ρ : G) = b⁻¹ := by
      change (u⁻¹)⁻¹ * (x : G)⁻¹ = b⁻¹
      rw [inv_inv, ← hbu, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    have hρ : Nat.Coprime p (orderOf ρ.val) := by
      rw [hρval, orderOf_inv]
      exact hbcop.symm
    have hpoint : (uC * ρ)⁻¹ = x := by
      simp only [ρ, ← mul_assoc, mul_inv_cancel, one_mul, inv_inv]
    have h := CFSG.TwoRankLowerBound.Helpers.principal_local_section_projection basis m p l0 hl0
      u⁻¹ n huinv localBasis l0' hl0' ρ hρ f hf
    rw [hpoint] at h
    exact h
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem principal_local_section_projection (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    [hm : m.IsMaximal] [CharP (BlocksAlgInt ⧸ m) p] (G : Type) [Group G] [Fintype G]
    (u : G) (hu : ∃ n : ℕ, orderOf u = p ^ n) (f : G → ℂ) (hf : BlocksIsClassFunction f) :
    let C := Subgroup.centralizer (Subgroup.zpowers u : Set G)
    let Q : Set C := {x | BlocksIsPPart p (x : G) u}
    Q.indicator (∑ᶠ χ ∈ BlocksPrincipalBlock m C, BlocksInnerProduct (fun x : C => f x) χ • χ) =
      Q.indicator
        (fun x : C => (∑ᶠ χ ∈ BlocksPrincipalBlock m G, BlocksInnerProduct f χ • χ) x) := by
  intro C Q
  obtain ⟨n, hn⟩ := hu
  have hC : C = Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) := by
    change Subgroup.centralizer (Subgroup.zpowers u : Set G) = _
    rw [Subgroup.zpowers_inv]
  exact principal_local_section_projection_aux p hp m G u n hn f hf C hC

end CFSG.BlockBasics
