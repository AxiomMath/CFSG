module

public import CFSG.CharacterTheory.Semidihedral.Principal.DefectKleinFourSectionColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ExtendedCentralizer

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace KleinFourOrder

theorem productCount_map_subtype {G : Type*} [Group G] (H : Subgroup G) (A B : Finset H)
    (x : H) :
    productCount (A.map (Function.Embedding.subtype _)) (B.map (Function.Embedding.subtype _))
      (x : G) = productCount A B x := by
  unfold productCount
  symm
  apply Finset.card_bij (fun p _ => ((p.1 : G), (p.2 : G)))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
      Function.Embedding.subtype_apply] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    exact ⟨⟨⟨p.1, ha, rfl⟩, ⟨p.2, hb, rfl⟩⟩, by rw [← Subgroup.coe_mul, hab]⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · rintro ⟨q₁, q₂⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
      Function.Embedding.subtype_apply] at hq
    obtain ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hab⟩ := hq
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ha, hb⟩, Subtype.ext (by simpa using hab)⟩

theorem extendedCentralizer_le_centralizer {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (x : Subgroup.centralizer (Subgroup.zpowers t : Set G))
    (hx : x ∈ involutionLocalSection t) :
    extendedCentralizer (x : G) ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
  obtain ⟨y, rfl, hy⟩ := hx
  have hloc := (involution_product_extended_centralizer_localization (x := t) (∅ : Finset G) ∅
    (by simp) (by simp)).2.2.2.2.2 2 t y 1 (by rw [ht, pow_one])
    (Subtype.ext_iff.mp (BrauerFiberSection.commute_centralizerSelf t y))
    (by rw [Subgroup.orderOf_coe]; exact Nat.coprime_two_left.mpr hy)
  intro g hg
  have hg' := hloc hg
  rw [mem_extendedCentralizer] at hg'
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← ht, pow_orderOf_eq_one]
  have hgt : g⁻¹ * t * g = t := by
    rcases hg' with h | h
    · exact h
    · rw [h, htinv]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hc : t * g = g * t := by
    calc t * g = g * (g⁻¹ * t * g) := by group
      _ = g * t := by rw [hgt]
  exact (Commute.zpow_left hc k).eq

theorem characterSubsetProjection_expansion {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (S : Finset basis.index) (a : basis.index → ℂ) :
    characterSubsetProjection basis S
        (fun x => ∑ χ, a χ * (basis.representation χ).character x) =
      fun x => ∑ χ ∈ S, a χ * (basis.representation χ).character x := by
  funext x
  rw [BrauerSecondMain.characterSubsetProjection_apply_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  congr 1
  rw [characterPairing_expansion_left]
  simp only [KleinFourColumns.pairing_basis, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

end KleinFourOrder

open KleinFourOrder KleinFourColumns

theorem defect_klein_four_three_local_blocks_exact_nonprincipal_order {G : Type} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (t : G) (ht : orderOf t = 2) (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (s : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hs : orderOf s = 2)
    (hst : (s : G) ≠ t)
    (hclasses : ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), orderOf y = 2 →
      IsConj y ⟨t, element_mem_centralizer_zpowers t⟩ ∨ IsConj y s)
    (label : basis.index) (D : Subgroup G) (hDK : IsKleinFour D)
    (hD : coefficientBlockDefect basis ideal 2 label D)
    (b : Fin 3 → Finset localBasis.index) (hb : Function.Injective b)
    (hfiber : brauerFiberBlocks basis ideal 2 t hgroup localBasis label = Finset.univ.image b)
    (θ : Fin 3 → Fin 4 → localBasis.index) (hθinj : ∀ j, Function.Injective (θ j))
    (hθb : ∀ j, b j = Finset.univ.image (θ j)) (f : Fin 3 → ℕ) (hf : ∀ j, 0 < f j)
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
      (localBasis.representation (θ j 0)).character s = 2 ∧
      (localBasis.representation (θ j 1)).character s = -2 ∧
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
        h / ((Nat.card (Subgroup.centralizer ({s} : Set (Subgroup.centralizer
          (Subgroup.zpowers t : Set G)))) : ℚ) ^ 2 * f 0 * f 1 * f 2) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ f 0 * f 1 * f 2 →
        (padicValNat ℓ (Nat.card G) : ℤ) =
            3 * padicValNat ℓ (Nat.card (Subgroup.centralizer (Subgroup.zpowers t : Set G))) -
              2 * padicValNat ℓ (Nat.card (Subgroup.centralizer ({s} : Set (Subgroup.centralizer
                (Subgroup.zpowers t : Set G))))) + padicValNat ℓ h ∧
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
  obtain ⟨Φ, ε, h, hΦinj, hΦimage, hε, hhpos, hΦdeg, -, -, -, -, -, -, hinvol, hbound, -, -⟩ :=
    defect_klein_four_section_columns_four_character_family basis ideal hinv t ht hgroup
      localBasis label D hDK hD b hb hfiber α hαint hαsupp' hαnorm hαspan' f hf hαt
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
    Finset.univ.filter fun y => orderOf y = 2 with hAC
  have hcentral : ∀ g : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      g * ⟨t, element_mem_centralizer_zpowers t⟩ * g⁻¹ = ⟨t, element_mem_centralizer_zpowers t⟩ :=
    fun g => by rw [((BrauerFiberSection.commute_centralizerSelf t g).symm).eq,
      mul_inv_cancel_right]
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
  have hACeq : AC = insert ⟨t, element_mem_centralizer_zpowers t⟩ (conjClassFinset s) := by
    ext y
    simp only [hAC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      conjClassFinset]
    constructor
    · intro hy
      rcases hclasses y hy with h1 | h1
      · left
        obtain ⟨g, hg⟩ := isConj_iff.mp h1
        have := hcentral g⁻¹
        rw [inv_inv] at this
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = _ := by rw [hg, this]
      · right
        exact h1.symm
    · rintro (rfl | h1)
      · exact htbar2
      · rw [← horderConj s y h1, hs]
  have htnot : (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) ∉ conjClassFinset s := by
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    apply hst
    have := hcentral g⁻¹
    rw [inv_inv] at this
    have hs' : s = g⁻¹ * (g * s * g⁻¹) * g := by group
    rw [hg, this] at hs'
    exact congrArg Subtype.val hs'
  have hACinv : ConjInvariant AC := by
    intro g y
    simp only [hAC, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [horderConj y (g * y * g⁻¹) (isConj_iff.mpr ⟨g, rfl⟩)]
  have hACinvol : ∀ a ∈ AC, a * a = 1 := by
    intro a ha
    simp only [hAC, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hcard : ((conjClassFinset s).card : ℂ) * (d : ℂ) = c := by
    have h := card_conjClassFinset_mul s
    rw [hd, hc]
    exact h
  have hFC : ∀ x : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      (productCount AC AC x : ℂ) = ∑ θ', ((c : ℂ) *
        ((localBasis.representation θ').character ⟨t, element_mem_centralizer_zpowers t⟩ / c +
          (localBasis.representation θ').character s / d) ^ 2 /
            (localBasis.representation θ').character 1) *
              (localBasis.representation θ').character x := by
    intro x
    obtain ⟨-, h⟩ := conjugacy_invariant_product_character_formula_involutions localBasis AC AC
      hACinv hACinv hACinvol hACinvol x
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ' _ => ?_
    have hsum : ∑ a ∈ AC, (localBasis.representation θ').character a =
        (c : ℂ) * ((localBasis.representation θ').character ⟨t, element_mem_centralizer_zpowers t⟩ /
          c + (localBasis.representation θ').character s / d) := by
      have hcard0 : ((conjClassFinset s).card : ℂ) ≠ 0 := by
        have : s ∈ conjClassFinset s := by
          simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact IsConj.refl s
        exact_mod_cast (Finset.card_pos.mpr ⟨s, this⟩).ne'
      rw [hACeq, Finset.sum_insert htnot, character_conjClassFinset_sum]
      rw [← hcard]
      field_simp
    rw [hsum, ← hc]
    field_simp
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
        refine ⟨⟨g, hgC⟩, ?_, rfl⟩
        rw [← Subgroup.orderOf_coe]
        exact (horderConj t g hg) ▸ ht
      · rintro ⟨y, hy, rfl⟩
        refine ⟨hinv t y ht (by rw [Subgroup.orderOf_coe]; exact hy), y.2⟩
    rw [hfilter]
  obtain ⟨aG, haG⟩ : ∃ aG : basis.index → ℂ, ∀ χ, aG χ = (Nat.card G : ℂ) / (c : ℂ) ^ 2 *
      (basis.representation χ).character t ^ 2 / (basis.representation χ).character 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨aC, haC⟩ : ∃ aC : localBasis.index → ℂ, ∀ θ', aC θ' = (c : ℂ) *
      ((localBasis.representation θ').character ⟨t, element_mem_centralizer_zpowers t⟩ / c +
        (localBasis.representation θ').character s / d) ^ 2 /
          (localBasis.representation θ').character 1 := ⟨_, fun _ => rfl⟩
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
    simp only [haC]
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
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hhpos.ne'
  have hLHS : ∑ i, aG (Φ i) * (basis.representation (Φ i)).character t =
      (Nat.card G : ℂ) / ((c : ℂ) ^ 2 * h) * (ε : ℂ) ^ 3 * (24 * f 0 * f 1 * f 2) := by
    obtain ⟨h0, h1, h2, h3⟩ := hinvol t ht
    simp only [Fin.sum_univ_four, haG]
    have hdeg1 : ∀ i, (basis.representation (Φ i)).character 1 = (h : ℂ) := fun i => by
      rw [FiniteComplexRepresentation.character, Representation.char_one, hΦdeg i]
    rw [hdeg1, hdeg1, hdeg1, hdeg1, h0, h1, h2, h3]
    field_simp
    ring
  have hRHS : ∑ j, ∑ i, aC (θ j i) * (localBasis.representation (θ j i)).character
      ⟨t, element_mem_centralizer_zpowers t⟩ = 24 * c / (d : ℂ) ^ 2 := by
    have hj : ∀ j, ∑ i, aC (θ j i) * (localBasis.representation (θ j i)).character
        ⟨t, element_mem_centralizer_zpowers t⟩ = 8 * c / (d : ℂ) ^ 2 := by
      intro j
      simp only [Fin.sum_univ_four, haC]
      obtain ⟨t0, t1, t2, t3⟩ := hθt j
      obtain ⟨s0, s1, s2, s3⟩ := hθs j
      have hdeg1 : ∀ i, (localBasis.representation (θ j i)).character 1 = (f j : ℂ) := fun i => by
        rw [FiniteComplexRepresentation.character, Representation.char_one, hθdeg j i]
      rw [hdeg1, hdeg1, hdeg1, hdeg1, t0, t1, t2, t3, s0, s1, s2, s3]
      have hf0 : (f j : ℂ) ≠ 0 := by exact_mod_cast (hf j).ne'
      field_simp
      ring
    rw [Fin.sum_univ_three, hj, hj, hj]
    ring
  rw [hLHS, hRHS] at hpt
  have hε3 : (ε : ℂ) ^ 3 = ε := by
    rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  rw [hε3] at hpt
  have hkey : (Nat.card G : ℂ) * ε * (f 0 * f 1 * f 2) * (d : ℂ) ^ 2 = (c : ℂ) ^ 3 * h := by
    field_simp at hpt
    linear_combination hpt
  have hkeyZ : (Nat.card G : ℤ) * ε * (f 0 * f 1 * f 2) * (d : ℤ) ^ 2 = (c : ℤ) ^ 3 * h := by
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
      have hpos2 : 0 < (c : ℤ) ^ 3 * h := by
        have : 0 < c := Nat.card_pos
        positivity
      nlinarith
  rw [hε1] at hkeyZ hinvol
  have hkeyN : Nat.card G * (f 0 * f 1 * f 2) * d ^ 2 = c ^ 3 * h := by
    have h' : (Nat.card G : ℤ) * (f 0 * f 1 * f 2) * (d : ℤ) ^ 2 = (c : ℤ) ^ 3 * h := by
      linarith
    exact_mod_cast h'
  obtain ⟨ht0, ht1, ht2, ht3⟩ := hinvol t ht
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
    have : ((Nat.card G * (f 0 * f 1 * f 2) * d ^ 2 : ℕ) : ℚ) = ((c ^ 3 * h : ℕ) : ℚ) := by
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
    have hval := congrArg (padicValNat ℓ) hkeyN
    rw [padicValNat.mul (by positivity) (pow_ne_zero 2 hdne), padicValNat.mul hGne hFne,
      padicValNat.pow d 2, padicValNat.mul (pow_ne_zero 3 hcne) hhpos.ne',
      padicValNat.pow c 3, padicValNat.eq_zero_of_not_dvd hndvd] at hval
    constructor
    · omega
    · omega

end CFSG.Semidihedral.Principal
