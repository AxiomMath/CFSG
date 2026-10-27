module

public import CFSG.CharacterTheory.KleinFourBlocks.SectionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectKleinFourExactOrder

public section

open scoped BigOperators Classical

namespace CFSG.KleinFourBlocks

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.KleinFourColumns
  CFSG.Semidihedral.Principal.KleinFourOrder CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

theorem mem_closure_pair_of_commuting_involutions {K : Type*} [Group K] {z s : K} (hz : z * z = 1)
    (hs : s * s = 1) (hzs : z * s = s * z) {x : K}
    (hx : x ∈ Subgroup.closure ({z, s} : Set K)) :
    x = 1 ∨ x = z ∨ x = s ∨ x = z * s := by
  have hz1 : ∀ y, z * (z * y) = y := fun y => by rw [← mul_assoc, hz, one_mul]
  have hs1 : ∀ y, s * (s * y) = y := fun y => by rw [← mul_assoc, hs, one_mul]
  have hszs : s * (z * s) = z := by rw [hzs, hs1]
  have hzsz : z * s * z = s := by rw [mul_assoc, ← hzs, hz1]
  have hzss : z * s * s = z := by rw [mul_assoc, hs, mul_one]
  have hzszs : z * s * (z * s) = 1 := by rw [mul_assoc, hszs, hz]
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [hz1, hszs, hzsz, hzss, hzszs, hz, hs, hzs.symm]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hz))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hs)))
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hz, inv_eq_of_mul_eq_one_right hs, hzs]

theorem eq_or_isConj_of_subgroupSubconjugate_klein {K : Type*} [Group K] {z s a : K}
    (hz : z * z = 1) (hs : s * s = 1) (hzc : ∀ g : K, g * z = z * g) (hzs : IsConj s (z * s))
    (ha : a ≠ 1)
    (hsub : subgroupSubconjugate (Subgroup.zpowers a) (Subgroup.closure ({z, s} : Set K))) :
    a = z ∨ IsConj s a := by
  obtain ⟨c, hc⟩ := hsub
  have hmem : (MulAut.conj c) a ∈ Subgroup.closure ({z, s} : Set K) :=
    hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers a))
  have hne : (MulAut.conj c) a ≠ 1 := fun h =>
    ha ((map_eq_one_iff _ (MulAut.conj c).injective).mp h)
  have hback : ∀ x, (MulAut.conj c) a = x → a = c⁻¹ * x * c := by
    intro x hx
    rw [← hx, MulAut.conj_apply]
    group
  rcases mem_closure_pair_of_commuting_involutions hz hs (hzc s).symm hmem with h | h | h | h
  · exact absurd h hne
  · left
    rw [hback _ h, hzc c⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  · right
    exact isConj_iff.mpr ⟨c⁻¹, by rw [hback _ h]; group⟩
  · right
    refine hzs.trans (isConj_iff.mpr ⟨c⁻¹, ?_⟩)
    rw [hback _ h]
    group

theorem block_involution_sum_eq {K : Type} [Group K] [Fintype K] [DecidableEq K]
    (basis : FiniteIrreducibleCharacterBasis K) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (label : basis.index)
    {z s : K} (hz : orderOf z = 2) (hs : orderOf s = 2) (hzc : ∀ g : K, g * z = z * g)
    (hzs : z ≠ s) (hzs' : IsConj s (z * s))
    (hD : coefficientBlockDefect basis ideal 2 label (Subgroup.closure ({z, s} : Set K)))
    (A : Finset K) (hA : insert z (conjClassFinset s) ⊆ A) (hA2 : ∀ a ∈ A, orderOf a = 2)
    {χ : basis.index} (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label) :
    ∑ a ∈ A, (basis.representation χ).character a =
      (basis.representation χ).character z +
        ((conjClassFinset s).card : ℂ) * (basis.representation χ).character s := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hss : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hznot : z ∉ conjClassFinset s := by
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    apply hzs
    have h1 : s = g⁻¹ * (g * s * g⁻¹) * g := by group
    rw [hg, hzc g⁻¹, mul_assoc, inv_mul_cancel, mul_one] at h1
    exact h1.symm
  rw [← Finset.sum_subset hA, Finset.sum_insert hznot, character_conjClassFinset_sum]
  intro a haA hnot
  have ha2 := hA2 a haA
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; omega
  refine (block_characters_vanish_outside_defect_primary basis ideal 2 label _ hD a a 1
    (mul_one a).symm (Commute.one_right a) ⟨1, by rw [ha2, pow_one]⟩ (by simp)).1 ?_ χ hχ
  intro hsub
  rcases eq_or_isConj_of_subgroupSubconjugate_klein hzz hss hzc hzs' ha1 hsub with h | h
  · exact hnot (Finset.mem_insert.mpr (Or.inl h))
  · refine hnot (Finset.mem_insert_of_mem ?_)
    simpa only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem defect_klein_four_three_local_blocks_exact_order_gen {G : Type} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (t : G) (ht : orderOf t = 2) (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (s : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hs : orderOf s = 2)
    (hst : (s : G) ≠ t) (hsG : IsConj t (s : G))
    (y₀ : Subgroup.centralizer (Subgroup.zpowers t : Set G))
    (hy₀ : y₀ * s * y₀⁻¹ = ⟨t, element_mem_centralizer_zpowers t⟩ * s)
    (label : basis.index) (D : Subgroup G) (hDK : IsKleinFour D)
    (htrans : ∀ u ∈ D, u ≠ 1 → IsConj t u)
    (hD : coefficientBlockDefect basis ideal 2 label D)
    (b : Fin 3 → Finset localBasis.index) (hb : Function.Injective b)
    (hfiber : brauerFiberBlocks basis ideal 2 t hgroup localBasis label = Finset.univ.image b)
    (θ : Fin 3 → Fin 4 → localBasis.index) (hθinj : ∀ j, Function.Injective (θ j))
    (hθb : ∀ j, b j = Finset.univ.image (θ j))
    (hbD : ∀ j, coefficientBlockDefect localBasis ideal 2 (θ j 0)
      (Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, s} :
        Set (Subgroup.centralizer (Subgroup.zpowers t : Set G)))))
    (f : Fin 3 → ℕ) (hf : ∀ j, 0 < f j) (w : ℕ) (hw : 0 < w)
    (hθdeg : ∀ j i, Module.finrank ℂ (localBasis.representation (θ j i)).vector = f j)
    (hθt : ∀ j,
      (localBasis.representation (θ j 0)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          f j ∧
      (localBasis.representation (θ j 1)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          f j ∧
      (localBasis.representation (θ j 2)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f j : ℂ) ∧
      (localBasis.representation (θ j 3)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f j : ℂ))
    (hθs : ∀ j,
      (localBasis.representation (θ j 0)).character s = 2 * (w : ℂ) ∧
      (localBasis.representation (θ j 1)).character s = -(2 * (w : ℂ)) ∧
      (localBasis.representation (θ j 2)).character s = 0 ∧
      (localBasis.representation (θ j 3)).character s = 0)
    (hαsupp : ∀ j x, x ∉ involutionLocalSection t →
      ((localBasis.representation (θ j 0)).character +
        (localBasis.representation (θ j 1)).character -
          (localBasis.representation (θ j 2)).character -
            (localBasis.representation (θ j 3)).character) x = 0)
    (hαspan : ∀ j, coefficientCharacterSpace localBasis (b j) ⊓
      sectionSupported (involutionLocalSection t) =
        Submodule.span ℂ {(localBasis.representation (θ j 0)).character +
          (localBasis.representation (θ j 1)).character -
            (localBasis.representation (θ j 2)).character -
              (localBasis.representation (θ j 3)).character}) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      (basis.representation χ).character ≠ 1) ∧
    ∃ (Φ : Fin 4 → basis.index) (h : ℕ),
      Function.Injective Φ ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ.image Φ ∧
      0 < h ∧ (∀ i, Module.finrank ℂ (basis.representation (Φ i)).vector = h) ∧
      (basis.representation (Φ 0)).character t = (f 0 : ℂ) + f 1 + f 2 ∧
      (basis.representation (Φ 1)).character t = -(f 0 : ℂ) - f 1 + f 2 ∧
      (basis.representation (Φ 2)).character t = -(f 0 : ℂ) + f 1 - f 2 ∧
      (basis.representation (Φ 3)).character t = (f 0 : ℂ) - f 1 - f 2 ∧
      (Nat.card G : ℚ) = (Nat.card (Subgroup.centralizer (Subgroup.zpowers t : Set G)) : ℚ) ^ 3 *
        w ^ 2 * h / ((Nat.card (Subgroup.centralizer ({s} : Set (Subgroup.centralizer
          (Subgroup.zpowers t : Set G)))) : ℚ) ^ 2 * f 0 * f 1 * f 2) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ f 0 * f 1 * f 2 →
        (padicValNat ℓ (Nat.card G) : ℤ) =
            3 * padicValNat ℓ (Nat.card (Subgroup.centralizer (Subgroup.zpowers t : Set G))) -
              2 * padicValNat ℓ (Nat.card (Subgroup.centralizer ({s} : Set (Subgroup.centralizer
                (Subgroup.zpowers t : Set G))))) + 2 * padicValNat ℓ w + padicValNat ℓ h ∧
          3 * (padicValNat ℓ (Nat.card (Subgroup.centralizer (Subgroup.zpowers t : Set G))) : ℤ) -
              2 * padicValNat ℓ (Nat.card (Subgroup.centralizer ({s} : Set (Subgroup.centralizer
                (Subgroup.zpowers t : Set G))))) ≤ padicValNat ℓ (Nat.card G) := by
  obtain ⟨α, hα⟩ : ∃ α : Fin 3 → Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ,
      ∀ j, α j = (localBasis.representation (θ j 0)).character +
        (localBasis.representation (θ j 1)).character -
          (localBasis.representation (θ j 2)).character -
            (localBasis.representation (θ j 3)).character := ⟨_, fun _ => rfl⟩
  have hθmem : ∀ j i, θ j i ∈ b j := fun j i => by
    rw [hθb j]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hαint : ∀ j, α j ∈ coefficientVirtualLattice localBasis (b j) := by
    intro j
    rw [hα j]
    have hmem : ∀ i, (localBasis.representation (θ j i)).character ∈
        coefficientVirtualLattice localBasis (b j) := fun i =>
      Submodule.subset_span ⟨θ j i, hθmem j i, rfl⟩
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (hmem 0) (hmem 1))
      (hmem 2)) (hmem 3)
  have hαsupp' : ∀ j x, x ∉ involutionLocalSection t → α j x = 0 := fun j x hx => by
    rw [hα j]
    exact hαsupp j x hx
  have hαspan' : ∀ j, coefficientCharacterSpace localBasis (b j) ⊓
      sectionSupported (involutionLocalSection t) = Submodule.span ℂ {α j} := fun j => by
    rw [hα j]
    exact hαspan j
  have hαnorm : ∀ j, BlocksInnerProduct (α j) (α j) = 4 := by
    intro j
    have hv : α j ∈ BlocksVChar (Subgroup.centralizer (Subgroup.zpowers t : Set G)) := by
      rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
      exact coefficientVirtualLattice_le_virtual localBasis (b j) (hαint j)
    rw [blocksInnerProduct_eq_characterPairing _ hv]
    have hexp : α j = fun x => ∑ i : Fin 4, ((![1, 1, -1, -1] : Fin 4 → ℂ) i) *
        (localBasis.representation (θ j i)).character x := by
      rw [hα j]
      funext x
      simp [Fin.sum_univ_four]
      ring
    rw [hexp, characterPairing_expansion_left]
    simp_rw [characterPairing_expansion_right, pairing_basis, (hθinj j).eq_iff]
    simp [Fin.sum_univ_four]
    norm_num
  have htbar : (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) ∈ involutionLocalSection t :=
    ⟨1, (mul_one _).symm, by rw [orderOf_one]; exact odd_one⟩
  have hαt : ∀ j, α j ⟨t, element_mem_centralizer_zpowers t⟩ = 4 * f j := by
    intro j
    rw [hα j]
    simp only [Pi.add_apply, Pi.sub_apply]
    obtain ⟨h0, h1, h2, h3⟩ := hθt j
    rw [h0, h1, h2, h3]
    ring
  obtain ⟨Φ, ε, h, hΦinj, hΦimage, hε, hhpos, hΦdeg, -, -, -, -, -, -, hinvol, -, hbound, -, -⟩ :=
    defect_klein_four_section_columns_four_character_family_gen basis ideal t ht hgroup
      localBasis label D hDK htrans hD b hb hfiber α hαint hαsupp' hαnorm hαspan' f hf hαt
  set c := Nat.card (Subgroup.centralizer (Subgroup.zpowers t : Set G)) with hc
  set d := Nat.card (Subgroup.centralizer ({s} : Set (Subgroup.centralizer
    (Subgroup.zpowers t : Set G)))) with hd
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer
    (Subgroup.zpowers t : Set G))).ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer
    ({s} : Set (Subgroup.centralizer (Subgroup.zpowers t : Set G))))).ne'
  have hcentEq : Subgroup.centralizer ({t} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left h k).eq
    · intro h
      exact h t (Subgroup.mem_zpowers t)
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hFG : ∀ x : G, (productCount (conjClassFinset t) (conjClassFinset t) x : ℂ) =
      ∑ χ, ((Nat.card G : ℂ) / (c : ℂ) ^ 2 * (basis.representation χ).character t ^ 2 /
        (basis.representation χ).character 1) * (basis.representation χ).character x := by
    intro x
    have h := involution_classes_product_character_formula basis t t htt htt x
    rw [hcentEq, ← hc] at h
    have h' : (productCount (conjClassFinset t) (conjClassFinset t) x : ℂ) =
        (Nat.card G : ℂ) / (c : ℂ) ^ 2 * ∑ χ, (basis.representation χ).character t *
          (basis.representation χ).character t * (basis.representation χ).character x /
            (basis.representation χ).character 1 := by
      rw [eq_comm, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hc0)]
      linear_combination -h
    rw [h', Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  set AC : Finset (Subgroup.centralizer (Subgroup.zpowers t : Set G)) :=
    Finset.univ.filter fun y => orderOf y = 2 ∧ IsConj t (y : G) with hAC
  have horderConj : ∀ {K : Type} [Group K] (y z : K), IsConj y z → orderOf y = orderOf z := by
    intro K _ y z hyz
    obtain ⟨g, rfl⟩ := isConj_iff.mp hyz
    have h := (MulAut.conj g).orderOf_eq y
    rw [MulAut.conj_apply] at h
    exact h.symm
  have htbar2 : orderOf (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hACinv : ConjInvariant AC := by
    intro g y
    simp only [hAC, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [horderConj y (g * y * g⁻¹) (isConj_iff.mpr ⟨g, rfl⟩)]
    have hconj : IsConj (y : G) ((g * y * g⁻¹ : Subgroup.centralizer
        (Subgroup.zpowers t : Set G)) : G) := isConj_iff.mpr ⟨(g : G), rfl⟩
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans hconj⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans hconj.symm⟩
  have hAC2 : ∀ a ∈ AC, orderOf a = 2 := fun a ha => (Finset.mem_filter.mp ha).2.1
  have hACinvol : ∀ a ∈ AC, a * a = 1 := by
    intro a ha
    rw [← pow_two, ← hAC2 a ha, pow_orderOf_eq_one]
  have hACsub : insert (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) (conjClassFinset s) ⊆ AC := by
    intro y hy
    simp only [hAC, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨htbar2, IsConj.refl t⟩
    · simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨by rw [← horderConj s y hy, hs], hsG.trans ?_⟩
      obtain ⟨g, hg⟩ := isConj_iff.mp hy
      exact isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩
  have hcard : ((conjClassFinset s).card : ℂ) * (d : ℂ) = c := by
    have h := card_conjClassFinset_mul s
    rw [hd, hc]
    exact h
  obtain ⟨aC, haC⟩ : ∃ aC : localBasis.index → ℂ, ∀ θ', aC θ' = (c : ℂ)⁻¹ *
      (∑ a ∈ AC, (localBasis.representation θ').character a) ^ 2 /
        (localBasis.representation θ').character 1 := ⟨_, fun _ => rfl⟩
  have hFC : ∀ x : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      (productCount AC AC x : ℂ) = ∑ θ', aC θ' * (localBasis.representation θ').character x := by
    intro x
    obtain ⟨-, h⟩ := conjugacy_invariant_product_character_formula_involutions localBasis AC AC
      hACinv hACinv hACinvol hACinvol x
    rw [← hc] at h
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ' _ => ?_
    rw [haC]
    ring
  have hloc : ∀ x ∈ involutionLocalSection t,
      productCount (conjClassFinset t) (conjClassFinset t) (x : G) = productCount AC AC x := by
    intro x hx
    have hTinvol : ∀ a ∈ conjClassFinset t, a * a = 1 := by
      intro a ha
      simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨g, rfl⟩ := isConj_iff.mp ha
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have h := (involution_product_extended_centralizer_localization (x := (x : G))
      (conjClassFinset t) (conjClassFinset t) hTinvol hTinvol).2.2.2.2.1 _
      (extendedCentralizer_le_centralizer ht x hx)
    rw [h, ← productCount_map_subtype]
    have hfilter : (conjClassFinset t).filter
        (· ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G)) =
          AC.map (Function.Embedding.subtype _) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_map, conjClassFinset, Finset.mem_univ, true_and,
        hAC, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨hg, hgC⟩
        refine ⟨⟨g, hgC⟩, ⟨?_, hg⟩, rfl⟩
        rw [← Subgroup.orderOf_coe]
        exact (horderConj t g hg) ▸ ht
      · rintro ⟨y, ⟨-, hy⟩, rfl⟩
        exact ⟨hy, y.2⟩
    rw [hfilter]
  obtain ⟨aG, haG⟩ : ∃ aG : basis.index → ℂ, ∀ χ, aG χ = (Nat.card G : ℂ) / (c : ℂ) ^ 2 *
      (basis.representation χ).character t ^ 2 / (basis.representation χ).character 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨FG, hFGdef⟩ : ∃ FG : G → ℂ,
      FG = fun x => ∑ χ, aG χ * (basis.representation χ).character x := ⟨_, rfl⟩
  obtain ⟨FC, hFCdef⟩ : ∃ FC : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ,
      FC = fun x => ∑ θ', aC θ' * (localBasis.representation θ').character x := ⟨_, rfl⟩
  have hFGcount : ∀ x, FG x = productCount (conjClassFinset t) (conjClassFinset t) x := by
    intro x
    rw [hFG x, hFGdef]
    simp only [haG]
  have hFCcount : ∀ x, FC x = productCount AC AC x := by
    intro x
    rw [hFC x, hFCdef]
  have hFGclass : ∀ x g : G, FG (g * x * g⁻¹) = FG x := by
    intro x g
    rw [hFGdef]
    simp only [Representation.char_conj]
  obtain ⟨hproj, -⟩ := brauer_fiber_involution_section_induction_decomposition basis ideal t ht
    hgroup localBasis label
  have hmaskEval : ∀ g : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ,
      characterFunctionMask (involutionLocalSection t) g ⟨t, element_mem_centralizer_zpowers t⟩ =
        g ⟨t, element_mem_centralizer_zpowers t⟩ := fun g => by
    unfold characterFunctionMask
    rw [ite_eq_left htbar]
  have hpt := congrFun (hproj FG hFGclass) ⟨t, element_mem_centralizer_zpowers t⟩
  rw [hmaskEval, hmaskEval, Finset.sum_apply] at hpt
  have hlocP : ∀ b' ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      characterSubsetProjection localBasis b' (fun h => FG h)
          ⟨t, element_mem_centralizer_zpowers t⟩ =
        characterSubsetProjection localBasis b' FC ⟨t, element_mem_centralizer_zpowers t⟩ := by
    intro b' hb'
    obtain ⟨θ₀, -, rfl⟩ := Finset.mem_image.mp hb'
    have hmask : characterFunctionMask (involutionLocalSection t) (fun h => FG h) =
        characterFunctionMask (involutionLocalSection t) FC := by
      funext x
      unfold characterFunctionMask
      split_ifs with hx
      · dsimp only
        rw [hFGcount, hFCcount, hloc x hx]
      · rfl
    have hQ := BrauerFiberSection.involutionLocalSection_primeSectionUnion ht
    calc characterSubsetProjection localBasis (coefficientBlock localBasis
          (localizedComplexIntegerRing ideal) θ₀) (fun h => FG h)
          ⟨t, element_mem_centralizer_zpowers t⟩ =
        characterFunctionMask (involutionLocalSection t) (characterSubsetProjection localBasis
          (coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₀) (fun h => FG h))
          ⟨t, element_mem_centralizer_zpowers t⟩ := (hmaskEval _).symm
      _ = characterSubsetProjection localBasis (coefficientBlock localBasis
          (localizedComplexIntegerRing ideal) θ₀)
          (characterFunctionMask (involutionLocalSection t) (fun h => FG h))
          ⟨t, element_mem_centralizer_zpowers t⟩ := by
        rw [coefficientBlock_section_mask_commute localBasis ideal 2 θ₀ _ hQ]
      _ = characterSubsetProjection localBasis (coefficientBlock localBasis
          (localizedComplexIntegerRing ideal) θ₀)
          (characterFunctionMask (involutionLocalSection t) FC)
          ⟨t, element_mem_centralizer_zpowers t⟩ := by rw [hmask]
      _ = characterFunctionMask (involutionLocalSection t) (characterSubsetProjection localBasis
          (coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₀) FC)
          ⟨t, element_mem_centralizer_zpowers t⟩ := by
        rw [coefficientBlock_section_mask_commute localBasis ideal 2 θ₀ _ hQ]
      _ = _ := hmaskEval _
  rw [Finset.sum_congr rfl hlocP] at hpt
  rw [hFGdef, characterSubsetProjection_expansion] at hpt
  simp only [hFCdef, characterSubsetProjection_expansion] at hpt
  rw [hΦimage, Finset.sum_image (fun i _ i' _ hii' => hΦinj hii'), hfiber,
    Finset.sum_image (fun j _ j' _ hjj' => hb hjj')] at hpt
  simp only [hθb, Finset.sum_image (fun i _ i' _ hii' => (hθinj _) hii')] at hpt
  have hbT : ∀ j, b j ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label := fun j => by
    rw [hfiber]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hblock : ∀ j i, θ j i ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
      (θ j 0) := by
    intro j i
    obtain ⟨θ₀, -, hθ₀⟩ := Finset.mem_image.mp (hbT j)
    have h0 : θ j 0 ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₀ := by
      rw [hθ₀]
      exact hθmem j 0
    rw [coefficientBlock_eq_of_mem localBasis _ h0, hθ₀]
    exact hθmem j i
  have hSblock : ∀ j i, ∑ a ∈ AC, (localBasis.representation (θ j i)).character a =
      (localBasis.representation (θ j i)).character ⟨t, element_mem_centralizer_zpowers t⟩ +
        ((conjClassFinset s).card : ℂ) * (localBasis.representation (θ j i)).character s :=
    fun j i => block_involution_sum_eq localBasis ideal (θ j 0) htbar2 hs
      (fun g => ((BrauerFiberSection.commute_centralizerSelf t g).symm).eq)
      (fun h => hst (congrArg Subtype.val h).symm) (isConj_iff.mpr ⟨y₀, hy₀⟩) (hbD j) AC hACsub
      hAC2 (hblock j i)
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hhpos.ne'
  have hLHS : ∑ i, aG (Φ i) * (basis.representation (Φ i)).character t =
      (Nat.card G : ℂ) / ((c : ℂ) ^ 2 * h) * (ε : ℂ) ^ 3 * (24 * f 0 * f 1 * f 2) := by
    obtain ⟨h0, h1, h2, h3⟩ := hinvol t (IsConj.refl t)
    simp only [Fin.sum_univ_four, haG]
    have hdeg1 : ∀ i, (basis.representation (Φ i)).character 1 = (h : ℂ) := fun i => by
      rw [FiniteComplexRepresentation.character, Representation.char_one, hΦdeg i]
    rw [hdeg1, hdeg1, hdeg1, hdeg1, h0, h1, h2, h3]
    field_simp
    ring
  have hRHS : ∑ j, ∑ i, aC (θ j i) * (localBasis.representation (θ j i)).character
      ⟨t, element_mem_centralizer_zpowers t⟩ = 24 * c * (w : ℂ) ^ 2 / (d : ℂ) ^ 2 := by
    have hj : ∀ j, ∑ i, aC (θ j i) * (localBasis.representation (θ j i)).character
        ⟨t, element_mem_centralizer_zpowers t⟩ = 8 * c * (w : ℂ) ^ 2 / (d : ℂ) ^ 2 := by
      intro j
      simp only [Fin.sum_univ_four, haC, hSblock]
      obtain ⟨t0, t1, t2, t3⟩ := hθt j
      obtain ⟨s0, s1, s2, s3⟩ := hθs j
      have hdeg1 : ∀ i, (localBasis.representation (θ j i)).character 1 = (f j : ℂ) := fun i => by
        rw [FiniteComplexRepresentation.character, Representation.char_one, hθdeg j i]
      rw [hdeg1, hdeg1, hdeg1, hdeg1, t0, t1, t2, t3, s0, s1, s2, s3]
      have hf0 : (f j : ℂ) ≠ 0 := by exact_mod_cast (hf j).ne'
      have hm0 : ((conjClassFinset s).card : ℂ) ≠ 0 := by
        intro h0
        apply hc0
        rw [← hcard, h0, zero_mul]
      rw [← hcard]
      field_simp
      ring
    rw [Fin.sum_univ_three, hj, hj, hj]
    ring
  rw [hLHS, hRHS] at hpt
  have hε3 : (ε : ℂ) ^ 3 = ε := by
    rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  rw [hε3] at hpt
  have hkey : (Nat.card G : ℂ) * ε * (f 0 * f 1 * f 2) * (d : ℂ) ^ 2 =
      (c : ℂ) ^ 3 * w ^ 2 * h := by
    field_simp at hpt
    linear_combination hpt
  have hkeyZ : (Nat.card G : ℤ) * ε * (f 0 * f 1 * f 2) * (d : ℤ) ^ 2 =
      (c : ℤ) ^ 3 * w ^ 2 * h := by
    exact_mod_cast hkey
  have hε1 : ε = 1 := by
    rcases hε with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hkeyZ
      have hpos1 : 0 < (Nat.card G : ℤ) * (f 0 * f 1 * f 2) * (d : ℤ) ^ 2 := by
        have := hf 0
        have := hf 1
        have := hf 2
        have : 0 < Nat.card G := Nat.card_pos
        have : 0 < d := Nat.card_pos
        positivity
      have hpos2 : 0 < (c : ℤ) ^ 3 * w ^ 2 * h := by
        have : 0 < c := Nat.card_pos
        have := hw
        positivity
      nlinarith
  rw [hε1] at hkeyZ hinvol
  have hkeyN : Nat.card G * (f 0 * f 1 * f 2) * d ^ 2 = c ^ 3 * w ^ 2 * h := by
    have h' : (Nat.card G : ℤ) * (f 0 * f 1 * f 2) * (d : ℤ) ^ 2 = (c : ℤ) ^ 3 * w ^ 2 * h := by
      linarith
    exact_mod_cast h'
  obtain ⟨ht0, ht1, ht2, ht3⟩ := hinvol t (IsConj.refl t)
  refine ⟨fun χ hχ hone => ?_, Φ, h, hΦinj, hΦimage, hhpos, hΦdeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hΦimage, Finset.mem_image] at hχ
    obtain ⟨i, -, rfl⟩ := hχ
    have h1 := congrFun hone 1
    rw [FiniteComplexRepresentation.character, Representation.char_one, hΦdeg i,
      Pi.one_apply] at h1
    have hh1 : h = 1 := by exact_mod_cast h1
    have := hf 0
    have := hf 1
    have := hf 2
    omega
  · rw [ht0]; push_cast; ring
  · rw [ht1]; push_cast; ring
  · rw [ht2]; push_cast; ring
  · rw [ht3]; push_cast; ring
  ·
    have hF : (d : ℚ) ^ 2 * f 0 * f 1 * f 2 ≠ 0 := by
      have := hf 0
      have := hf 1
      have := hf 2
      have : 0 < d := Nat.card_pos
      positivity
    rw [eq_div_iff hF]
    have : ((Nat.card G * (f 0 * f 1 * f 2) * d ^ 2 : ℕ) : ℚ) =
        ((c ^ 3 * w ^ 2 * h : ℕ) : ℚ) := by
      rw [hkeyN]
    push_cast at this
    linear_combination this
  ·
    intro ℓ hℓ hndvd
    have := Fact.mk hℓ
    have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hFne : f 0 * f 1 * f 2 ≠ 0 := by
      have := hf 0
      have := hf 1
      have := hf 2
      positivity
    have hdne : d ≠ 0 := Nat.card_pos.ne'
    have hcne : c ≠ 0 := Nat.card_pos.ne'
    have hwne : w ≠ 0 := hw.ne'
    have hval := congrArg (padicValNat ℓ) hkeyN
    rw [padicValNat.mul (by positivity) (pow_ne_zero 2 hdne), padicValNat.mul hGne hFne,
      padicValNat.pow d 2, padicValNat.mul (by positivity) hhpos.ne',
      padicValNat.mul (pow_ne_zero 3 hcne) (pow_ne_zero 2 hwne), padicValNat.pow c 3,
      padicValNat.pow w 2, padicValNat.eq_zero_of_not_dvd hndvd] at hval
    constructor
    · omega
    · omega

end CFSG.KleinFourBlocks
