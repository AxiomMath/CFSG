module

public import CFSG.CharacterTheory.SmallDefect.Basic
public import CFSG.CharacterTheory.OddOrderBasics.Schur
public import CFSG.CharacterTheory.Blocks.NormTwo

public section

open scoped BigOperators Classical

namespace CFSG.SmallDefect

open CFSG.BlockSectionOrthogonality.Helpers

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem sum_conj_of_invariant {M : Type*} [AddCommMonoid M] (X : Finset G)
    (hX : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X) (g : G) (F : G → M) :
    ∑ x ∈ X, F (g * x * g⁻¹) = ∑ x ∈ X, F x := by
  refine Finset.sum_nbij' (fun x => g * x * g⁻¹) (fun x => g⁻¹ * x * g) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact hX x hx g
  · intro x hx
    simpa only [inv_inv] using hX x hx g⁻¹
  · intro x _
    group
  · intro x _
    group
  · intro x _
    rfl

omit [Fintype G] in
theorem sum_character_mul_of_invariant {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (X : Finset G)
    (hX : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X) (z : G) :
    ∑ x ∈ X, χ (x * z) = (∑ x ∈ X, χ x) * χ z / χ 1 := by
  have hχ1 : χ 1 ≠ 0 := by
    intro h
    have := blocksIrr_identity_re_pos ⟨χ, hχ⟩
    simp only [h, Complex.zero_re, lt_self_iff_false] at this
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  set T : Module.End ℂ V := ∑ x ∈ X, ρ x with hT
  have hcomm : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T := by
    intro g
    apply LinearMap.ext
    intro v
    simp only [hT, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    have h1 : ∀ x, ρ x (ρ g v) = ρ (x * g) v := fun x => by rw [map_mul]; rfl
    have h2 : ∀ x, ρ g (ρ x v) = ρ ((g * x * g⁻¹) * g) v := fun x => by
      rw [show g * x * g⁻¹ * g = g * x by group, map_mul]; rfl
    simp_rw [h1, h2]
    exact (sum_conj_of_invariant X hX g (fun x => ρ (x * g) v)).symm
  obtain ⟨c, hc⟩ := CFSG.OddOrderBasics.complex_irreducible_commuting_scalar ρ hirr T hcomm
  have hdim : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    rwa [Representation.char_one] at hχ1
  have hz : ∑ x ∈ X, ρ.character (x * z) = c * ρ.character z := by
    have hTz : T ∘ₗ ρ z = ∑ x ∈ X, ρ (x * z) := by
      apply LinearMap.ext
      intro v
      simp only [hT, LinearMap.comp_apply, LinearMap.sum_apply, map_mul, Module.End.mul_apply]
    have : ∑ x ∈ X, ρ.character (x * z) = LinearMap.trace ℂ V (T ∘ₗ ρ z) := by
      rw [hTz, map_sum]
      rfl
    rw [this, hc, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul]
    rfl
  have h1 : ∑ x ∈ X, ρ.character x = c * ρ.character 1 := by
    have : ∑ x ∈ X, ρ.character x = LinearMap.trace ℂ V T := by
      rw [hT, map_sum]
      rfl
    rw [this, hc, map_smul, LinearMap.trace_id, Representation.char_one, smul_eq_mul]
  rw [hz, h1, Representation.char_one]
  field_simp

theorem card_mul_eq (X₁ X₂ : Finset G) (h₁ : ∀ x ∈ X₁, ∀ g : G, g * x * g⁻¹ ∈ X₁)
    (h₂ : ∀ x ∈ X₂, ∀ g : G, g * x * g⁻¹ ∈ X₂) (y : G) :
    ((((X₁ ×ˢ X₂).filter fun p => p.1 * p.2 = y).card : ℕ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ χ ∈ (irreducibles_finite G).toFinset,
        (∑ x ∈ X₁, χ x) * (∑ x ∈ X₂, χ x) * starRingEnd ℂ (χ y) / χ 1 := by
  set F : G → ℂ := fun y => ((((X₁ ×ˢ X₂).filter fun p => p.1 * p.2 = y).card : ℕ) : ℂ)
    with hF
  have hFclass : BlocksIsClassFunction F := by
    intro z g
    simp only [hF]
    congr 1
    refine Finset.card_nbij' (fun p => (g⁻¹ * p.1 * g, g⁻¹ * p.2 * g))
      (fun p => (g * p.1 * g⁻¹, g * p.2 * g⁻¹)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hp ⊢
      refine ⟨⟨by simpa using h₁ _ hp.1.1 g⁻¹, by simpa using h₂ _ hp.1.2 g⁻¹⟩, ?_⟩
      rw [show g⁻¹ * p.1 * g * (g⁻¹ * p.2 * g) = g⁻¹ * (p.1 * p.2) * g by group, hp.2]
      group
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hp ⊢
      refine ⟨⟨h₁ _ hp.1.1 g, h₂ _ hp.1.2 g⟩, ?_⟩
      rw [show g * p.1 * g⁻¹ * (g * p.2 * g⁻¹) = g * (p.1 * p.2) * g⁻¹ by group, hp.2]
    · intro p _
      ext <;> simp only <;> group
    · intro p _
      ext <;> simp only <;> group
  have hexp := congrFun ((irreducible_character_basis G).2.2.2 F hFclass) y
  rw [Finset.sum_apply] at hexp
  simp only [Pi.smul_apply, smul_eq_mul] at hexp
  have hcoef : ∀ χ ∈ (irreducibles_finite G).toFinset, BlocksInnerProduct F χ =
      (Nat.card G : ℂ)⁻¹ * starRingEnd ℂ ((∑ x ∈ X₁, χ x) * (∑ x ∈ X₂, χ x) / χ 1) := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    unfold BlocksInnerProduct
    congr 1
    have hsum : ∑ z : G, F z * starRingEnd ℂ (χ z) =
        ∑ p ∈ X₁ ×ˢ X₂, starRingEnd ℂ (χ (p.1 * p.2)) := by
      simp only [hF]
      rw [← Finset.sum_fiberwise_of_maps_to (s := X₁ ×ˢ X₂) (t := Finset.univ)
        (g := fun p => p.1 * p.2) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2],
        Finset.sum_const, nsmul_eq_mul]
    rw [hsum, ← map_sum, Finset.sum_product]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [sum_character_mul_of_invariant hχ X₁ h₁]
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hcoef χ hχ]] at hexp
  have hreal : F y = starRingEnd ℂ (F y) := by
    simp only [hF, Complex.conj_natCast]
  change F y = _
  rw [hreal, hexp, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Set.Finite.mem_toFinset] at hχ
  have h1 : starRingEnd ℂ (χ 1) = χ 1 := by
    have h := blocksVChar_conjugate_inverse (AddSubgroup.subset_closure hχ) 1
    rwa [inv_one] at h
  simp only [map_mul, map_div₀, map_inv₀, Complex.conj_natCast, Complex.conj_conj, h1]
  ring

omit [Fintype G] in
theorem mem_centralizer_of_mul_eq {J y a b : G} (hJ : J * J = 1)
    (hy : J ∈ Subgroup.zpowers y) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = y) :
    a ∈ Subgroup.centralizer ({J} : Set G) ∧ b ∈ Subgroup.centralizer ({J} : Set G) := by
  have hinv : ∀ k : ℤ, a * y ^ k * a⁻¹ = y⁻¹ ^ k := by
    have hay : a * y * a⁻¹ = y⁻¹ := by
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
      rw [← hab, mul_inv_rev, hbinv, hainv]
      calc a * (a * b) * a = (a * a) * b * a := by group
        _ = b * a := by rw [ha, one_mul]
    intro k
    rw [← hay, ← conj_zpow]
  obtain ⟨k, rfl⟩ := hy
  have hJinv : (y ^ k)⁻¹ = y ^ k := inv_eq_of_mul_eq_one_right hJ
  have hacomm : a * y ^ k = y ^ k * a := by
    have h := hinv k
    rw [inv_zpow, hJinv] at h
    calc a * y ^ k = a * y ^ k * a⁻¹ * a := by group
      _ = y ^ k * a := by rw [h]
  have haC : a ∈ Subgroup.centralizer ({y ^ k} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hacomm
  refine ⟨haC, ?_⟩
  have hyC : y ∈ Subgroup.centralizer ({y ^ k} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.zpow_right (Commute.refl y) k).eq
  have hb' : b = a⁻¹ * y := by rw [← hab]; group
  rw [hb']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hyC

theorem involution_pair_formula {J y : G} (hJ : J * J = 1) (hy : J ∈ Subgroup.zpowers y)
    (hyC : y ∈ Subgroup.centralizer ({J} : Set G)) :
    (Nat.card (ConjClasses.mk J).carrier : ℂ) ^ 2 / Nat.card G *
        ∑ χ ∈ (irreducibles_finite G).toFinset, χ J ^ 2 * starRingEnd ℂ (χ y) / χ 1 =
      (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℂ)⁻¹ *
        ∑ ψ ∈ (irreducibles_finite (Subgroup.centralizer ({J} : Set G))).toFinset,
          (∑ c ∈ Finset.univ.filter fun c : Subgroup.centralizer ({J} : Set G) =>
            IsConj (c : G) J, ψ c) ^ 2 * starRingEnd ℂ (ψ ⟨y, hyC⟩) / ψ 1 := by
  set K : Finset G := Finset.univ.filter fun g : G => IsConj g J with hK
  have hKinv : ∀ x ∈ K, ∀ g : G, g * x * g⁻¹ ∈ K := by
    intro x hx g
    simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (isConj_iff.mpr ⟨g, rfl⟩).symm.trans hx
  set KC : Finset (Subgroup.centralizer ({J} : Set G)) :=
    Finset.univ.filter fun c => IsConj (c : G) J with hKC
  have hKCinv : ∀ x ∈ KC, ∀ g : Subgroup.centralizer ({J} : Set G), g * x * g⁻¹ ∈ KC := by
    intro x hx g
    simp only [hKC, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (isConj_iff.mpr ⟨(g : G), by simp⟩).symm.trans hx
  have hG := card_mul_eq K K hKinv hKinv y
  have hsumK : ∀ χ ∈ (irreducibles_finite G).toFinset, ∑ x ∈ K, χ x =
      (Nat.card (ConjClasses.mk J).carrier : ℂ) * χ J := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    have h := sum_isConj_mul (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)) J
    rw [← h, hK, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have hCcount := card_mul_eq KC KC hKCinv hKCinv ⟨y, hyC⟩
  have hcount : (((K ×ˢ K).filter fun p => p.1 * p.2 = y).card : ℕ) =
      (((KC ×ˢ KC).filter fun p => p.1 * p.2 = ⟨y, hyC⟩).card : ℕ) := by
    symm
    refine Finset.card_nbij' (fun p => ((p.1 : G), (p.2 : G))) (fun p =>
      if h : p.1 ∈ Subgroup.centralizer ({J} : Set G) ∧
          p.2 ∈ Subgroup.centralizer ({J} : Set G) then (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else (1, 1))
          ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, hKC, hK,
        Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨⟨hp.1.1, hp.1.2⟩, ?_⟩
      have := congrArg Subtype.val hp.2
      simpa using this
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, hK,
        Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hsq : ∀ x : G, IsConj x J → x * x = 1 := by
        intro x hx
        obtain ⟨c, hc⟩ := isConj_iff.mp hx.symm
        rw [← hc]
        calc c * J * c⁻¹ * (c * J * c⁻¹) = c * (J * J) * c⁻¹ := by group
          _ = 1 := by rw [hJ]; group
      obtain ⟨h1, h2⟩ := mem_centralizer_of_mul_eq hJ hy (hsq _ hp.1.1) (hsq _ hp.1.2) hp.2
      have hmem : p.1 ∈ Subgroup.centralizer ({J} : Set G) ∧
          p.2 ∈ Subgroup.centralizer ({J} : Set G) := ⟨h1, h2⟩
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, hKC,
        Finset.mem_filter, Finset.mem_univ, true_and, hmem, and_self, ↓reduceDIte]
      refine ⟨⟨hp.1.1, hp.1.2⟩, ?_⟩
      apply Subtype.ext
      simpa using hp.2
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
      simp
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, hK,
        Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hsq : ∀ x : G, IsConj x J → x * x = 1 := by
        intro x hx
        obtain ⟨c, hc⟩ := isConj_iff.mp hx.symm
        rw [← hc]
        calc c * J * c⁻¹ * (c * J * c⁻¹) = c * (J * J) * c⁻¹ := by group
          _ = 1 := by rw [hJ]; group
      obtain ⟨h1, h2⟩ := mem_centralizer_of_mul_eq hJ hy (hsq _ hp.1.1) (hsq _ hp.1.2) hp.2
      have hmem : p.1 ∈ Subgroup.centralizer ({J} : Set G) ∧
          p.2 ∈ Subgroup.centralizer ({J} : Set G) := ⟨h1, h2⟩
      simp [hmem]
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hsumK χ hχ]] at hG
  have hfin : (Nat.card G : ℂ)⁻¹ * ∑ χ ∈ (irreducibles_finite G).toFinset,
      ((Nat.card (ConjClasses.mk J).carrier : ℂ) * χ J) *
        ((Nat.card (ConjClasses.mk J).carrier : ℂ) * χ J) * starRingEnd ℂ (χ y) / χ 1 =
      (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℂ)⁻¹ *
        ∑ ψ ∈ (irreducibles_finite (Subgroup.centralizer ({J} : Set G))).toFinset,
          (∑ c ∈ KC, ψ c) * (∑ c ∈ KC, ψ c) * starRingEnd ℂ (ψ ⟨y, hyC⟩) / ψ 1 := by
    rw [← hG, ← hCcount]
    convert congrArg (Nat.cast : ℕ → ℂ) hcount using 3
    ext p
    simp
  calc _ = (Nat.card G : ℂ)⁻¹ * ∑ χ ∈ (irreducibles_finite G).toFinset,
        ((Nat.card (ConjClasses.mk J).carrier : ℂ) * χ J) *
          ((Nat.card (ConjClasses.mk J).carrier : ℂ) * χ J) * starRingEnd ℂ (χ y) / χ 1 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        ring
    _ = _ := hfin
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun ψ _ => ?_
        ring

end CFSG.SmallDefect
