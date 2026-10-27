module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyExhaustive

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Sizes

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem card_centralExtension_eq :
    Nat.card (CentralExtension F b m hm heven) = m * Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [card_centralExtension F b m hm heven, card_SL_two F, mul_assoc]

theorem card_isConj_eq {g : CentralExtension F b m hm heven} {c k : ℕ} (hc0 : 0 < c)
    (hc : Nat.card (Subgroup.centralizer {g}) = c)
    (hk : Nat.card (CentralExtension F b m hm heven) = k * c) :
    Nat.card {h : CentralExtension F b m hm heven // IsConj g h} = k := by
  have h := card_isConj_mul_card_centralizer g
  rw [hc, hk] at h
  exact Nat.eq_of_mul_eq_mul_right hc0 h

theorem ncard_diff_zpowers {H : Subgroup (CentralExtension F b m hm heven)}
    (hle : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ≤ H) :
    Set.ncard ((H : Set (CentralExtension F b m hm heven)) \
      (Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) :
        Set (CentralExtension F b m hm heven))) =
      Nat.card H - Nat.card (Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) := by
  rw [Set.ncard_sdiff hle, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  rfl

end Sizes

theorem base_conjugacy_classes_and_centralizers {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (_hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)
    (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) :
    let h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
    let G := CentralExtension F b m hm heven
    let u := cyclicGenerator F b m hm heven
    let a := u ^ 2
    let x := u ^ m
    let A := Subgroup.zpowers a
    let q := Nat.card F
    let κ := projectiveMap F b m hm heven
    let U := unipotentElement F b m hm heven
    let Tplus := (projectiveDiagonal F).comap κ
    let Tminus := nonsplitTorus F b m hm heven E basis
    let wplus := weylElement F b m hm heven
    let wminus := nonsplitWeyl F b m hm heven E basis h2 y hy
    let C : E → Matrix (Fin 2) (Fin 2) F := fun t => Algebra.leftMulMatrix basis t
    let S₀ := LinearMap.toMatrix basis basis (FiniteField.frobeniusAlgHom F E).toLinearMap
    let type2 : G → Prop := fun g => ∃ α ∈ A, IsConj g (α * U 1)
    let type3 : G → Prop := fun g => ∃ t ∈ Tplus, t ∉ A ∧ IsConj g t
    let type4 : G → Prop := fun g => ∃ t ∈ Tminus, t ∉ A ∧ IsConj g t
    x = specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
      κ (quotientClass F b m hm heven X j) =
        ProjGenLinGroup.mk (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) ∧
    (∀ t : F, U t = specialInclusion F b m hm heven (upperSL F t) ∧
      (upperSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) ∧
    (∀ c d : Fˣ, ((diagGL F (c, d) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      diagonal ![(c : F), (d : F)]) ∧
    (∀ g : G, g ∈ Tplus ↔ ∃ c d : Fˣ, ProjGenLinGroup.mk (diagGL F (c, d)) = κ g) ∧
    (∀ t : E, FiniteField.frobeniusAlgHom F E t = t ^ q) ∧
    (∀ s : Eˣ, ((mulGL F E basis s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = C s) ∧
    (∀ g : G, g ∈ Tminus ↔ ∃ s : Eˣ, ProjGenLinGroup.mk (mulGL F E basis s) = κ g) ∧
    wplus = specialInclusion F b m hm heven (weyl F) ∧
    (weyl F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧
    wminus = specialInclusion F b m hm heven (wMatrix F E basis h2 y hy) ∧
    ((wMatrix F E basis h2 y hy : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = C y * S₀ ∧
    Subgroup.center G = A ∧ Nat.card A = m ∧ Nat.card G = m * q * (q ^ 2 - 1) ∧
    (∀ g : G, g ∈ A ∨ type2 g ∨ type3 g ∨ type4 g) ∧
    (∀ g : G, ¬ (g ∈ A ∧ type2 g) ∧ ¬ (g ∈ A ∧ type3 g) ∧ ¬ (g ∈ A ∧ type4 g) ∧
      ¬ (type2 g ∧ type3 g) ∧ ¬ (type2 g ∧ type4 g) ∧ ¬ (type3 g ∧ type4 g)) ∧
    (∀ α ∈ A, ∀ g : G, IsConj α g ↔ g = α) ∧
    (∀ α ∈ A, ∀ α' ∈ A, ∀ t : F, IsConj (α * U 1) (α' * U t) ↔ α' = α ∧ t ≠ 0) ∧
    (∀ t : F, t ≠ 0 → IsConj (U 1) (U t)) ∧
    (∀ α ∈ A, ∀ g : G, g ∈ Subgroup.centralizer {α * U 1} ↔ ∃ α' ∈ A, ∃ t : F, g = α' * U t) ∧
    (∀ α ∈ A, Nat.card (Subgroup.centralizer {α * U 1}) = m * q) ∧
    A ⊓ unipotentSubgroup F b m hm heven = ⊥ ∧ (∀ α ∈ A, ∀ t : F, α * U t = U t * α) ∧
    (∀ α ∈ A, Nat.card {g : G // IsConj (α * U 1) g} = q ^ 2 - 1) ∧
    Set.ncard ((fun α => ConjClasses.mk (α * U 1)) '' (A : Set G)) = m ∧
    (∀ t ∈ Tplus, t ∉ A →
      (∀ t' ∈ Tplus, IsConj t t' ↔ t' = t ∨ t' = wplus * t * wplus⁻¹) ∧
      wplus * t * wplus⁻¹ ≠ t ∧ Subgroup.centralizer {t} = Tplus ∧
      Nat.card {g : G // IsConj t g} = q * (q + 1)) ∧
    Nat.card Tplus = m * (q - 1) ∧
    Set.ncard (ConjClasses.mk '' ((Tplus : Set G) \ (A : Set G))) = m * (q - 2) / 2 ∧
    (∀ t ∈ Tminus, t ∉ A →
      (∀ t' ∈ Tminus, IsConj t t' ↔ t' = t ∨ t' = wminus * t * wminus⁻¹) ∧
      wminus * t * wminus⁻¹ ≠ t ∧ Subgroup.centralizer {t} = Tminus ∧
      Nat.card {g : G // IsConj t g} = q * (q - 1)) ∧
    Nat.card Tminus = m * (q + 1) ∧
    Set.ncard (ConjClasses.mk '' ((Tminus : Set G) \ (A : Set G))) = m * q / 2 ∧
    (∀ g : G, g ∈ Subgroup.normalizer (Tplus : Set G) ↔ g ∈ Tplus ∨ wplus⁻¹ * g ∈ Tplus) ∧
    (∀ g : G, g ∈ Subgroup.normalizer (Tminus : Set G) ↔ g ∈ Tminus ∨ wminus⁻¹ * g ∈ Tminus) ∧
    (∀ g ∈ Tminus, ¬ type2 g ∧ ¬ type3 g) := by
  intro h2 G u a x A q κ U Tplus Tminus wplus wminus C S₀ type2 type3 type4
  have hchar : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hq2 : 2 ≤ q := two_le_card F
  have hTplus : Tplus = splitTorus F b m hm heven := (splitTorus_eq_comap).symm
  have hAcard : Nat.card A = m := by
    rw [Nat.card_zpowers, orderOf_cyclicGenerator_sq F b m hm heven h2]
  have hG : Nat.card G = m * q * (q ^ 2 - 1) := card_centralExtension_eq
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := card_sq_sub_one F
  have hTcard : Nat.card Tplus = m * (q - 1) := by rw [hTplus]; exact card_splitTorus F b m hm heven
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  have hTmcard : Nat.card Tminus = m * (q + 1) := card_nonsplitTorus z hz
  have hfix1 : ∀ g : G, g ∈ A → Nat.card {p : Omega F // g • p = p} = q + 1 :=
    fun g hg => card_fixed_of_mem_zpowers hg
  have hfix2 : ∀ g : G, type2 g → Nat.card {p : Omega F // g • p = p} = 1 := by
    rintro g ⟨α, hα, hg⟩
    rw [card_fixed_of_isConj hg.symm]
    exact card_fixed_unipotent hα one_ne_zero
  have hfix3 : ∀ g : G, type3 g → Nat.card {p : Omega F // g • p = p} = 2 := by
    rintro g ⟨t, ht, htA, hg⟩
    rw [card_fixed_of_isConj hg.symm]
    rw [hTplus] at ht
    exact card_fixed_splitTorus hb ht htA
  have hfix4 : ∀ g : G, type4 g → Nat.card {p : Omega F // g • p = p} = 0 := by
    rintro g ⟨t, ht, htA, hg⟩
    rw [card_fixed_of_isConj hg.symm]
    exact card_fixed_nonsplitTorus hb ht htA
  refine ⟨cyclicGenerator_pow_m F b m hm heven, projectiveMap_quotientClass F b m hm heven,
    fun t => ⟨rfl, rfl⟩, fun c d => rfl, ?_, frobeniusAlgHom_apply' F E, fun s => rfl,
    mem_nonsplitTorus_iff, rfl, rfl, rfl, rfl, center_eq_zpowers hb, hAcard, hG, ?_, ?_, ?_,
    fun α hα α' hα' t => isConj_alpha_unipotent_iff hpodd hb hα hα' t,
    fun t ht => isConj_unipotent hb ht, ?_, ?_, zpowers_inf_unipotentSubgroup,
    fun α hα t => cyclicGenerator_sq_zpowers_comm hα _, ?_, ?_, ?_, hTcard, ?_, ?_,
    hTmcard, ?_, ?_, mem_normalizer_nonsplitTorus_iff y hy h2 hb, ?_⟩
  · intro g
    show g ∈ (projectiveDiagonal F).comap κ ↔ _
    rw [Subgroup.mem_comap, projectiveDiagonal, MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨c, d⟩, h⟩
      exact ⟨c, d, h⟩
    · rintro ⟨c, d, h⟩
      exact ⟨(c, d), h⟩
  · intro g
    have h := conjugacy_type_exists basis hb g
    rw [← hTplus] at h
    exact h
  · intro g
    have hq3 : q + 1 ≠ 1 ∧ q + 1 ≠ 2 ∧ q + 1 ≠ 0 := by omega
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact hq3.1 ((hfix1 g h.1).symm.trans (hfix2 g h.2))
    · exact hq3.2.1 ((hfix1 g h.1).symm.trans (hfix3 g h.2))
    · exact hq3.2.2 ((hfix1 g h.1).symm.trans (hfix4 g h.2))
    · have := (hfix2 g h.1).symm.trans (hfix3 g h.2)
      omega
    · have := (hfix2 g h.1).symm.trans (hfix4 g h.2)
      omega
    · have := (hfix3 g h.1).symm.trans (hfix4 g h.2)
      omega
  · intro α hα g
    constructor
    · intro h
      obtain ⟨k, rfl⟩ := isConj_iff.mp h
      rw [← cyclicGenerator_sq_zpowers_comm hα k, mul_inv_cancel_right]
    · rintro rfl
      exact IsConj.refl _
  · intro α hα g
    rw [centralizer_alpha_unipotent hα]
    exact mem_centralizer_unipotent_iff hb g
  · intro α hα
    rw [centralizer_alpha_unipotent hα]
    exact card_centralizer_unipotent hb
  · intro α hα
    refine card_isConj_eq (c := m * q) (Nat.mul_pos hm (by omega)) ?_ ?_
    · rw [centralizer_alpha_unipotent hα]
      exact card_centralizer_unipotent hb
    · rw [hG]
      ring
  · rw [Set.InjOn.ncard_image, ← Nat.card_coe_set_eq]
    · exact hAcard
    · intro α hα α' hα' h
      exact alpha_eq_of_isConj hpodd h2 hα hα' (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  · intro t ht htA
    rw [hTplus] at ht ⊢
    have hC := centralizer_splitTorus hb ht htA
    refine ⟨fun t' ht' => isConj_splitTorus_iff hb ht htA ht', weylElement_conj_ne hb ht htA,
      hC, ?_⟩
    refine card_isConj_eq (c := m * (q - 1)) (Nat.mul_pos hm (by omega)) ?_ ?_
    · rw [hC]
      exact card_splitTorus F b m hm heven
    · rw [hG, hsq]
      ring
  ·
    have hle : A ≤ Tplus := by
      rw [hTplus, Subgroup.zpowers_le]
      exact cyclicGenerator_sq_mem_splitTorus F b m hm heven
    have hS := ncard_diff_zpowers hle
    rw [hTcard, hAcard] at hS
    have h2m := two_mul_ncard_image_of_pairs (ConjClasses.mk)
      (fun t => wplus * t * wplus⁻¹) ((Tplus : Set G) \ (A : Set G)) ?_ ?_
    · rw [hS] at h2m
      have : m * (q - 1) - m = m * (q - 2) := by
        rw [show q - 1 = (q - 2) + 1 by omega, mul_add, mul_one, Nat.add_sub_cancel]
      rw [this] at h2m
      omega
    · rintro t ⟨ht, htA⟩
      rw [SetLike.mem_coe, hTplus] at ht
      refine ⟨⟨?_, ?_⟩, weylElement_conj_ne hb ht htA⟩
      · rw [SetLike.mem_coe, hTplus]
        exact weylElement_conj_mem_splitTorus ht
      · exact conj_not_mem_zpowers htA _
    · rintro t ⟨ht, htA⟩ t' ⟨ht', -⟩
      rw [SetLike.mem_coe, hTplus] at ht ht'
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      exact isConj_splitTorus_iff hb ht htA ht'
  · intro t ht htA
    have hC := centralizer_nonsplitTorus y hy h2 hb ht htA
    refine ⟨fun t' ht' => isConj_nonsplitTorus_iff y hy h2 hb ht htA ht',
      nonsplitWeyl_conj_ne y hy h2 hb ht htA, hC, ?_⟩
    refine card_isConj_eq (c := m * (q + 1)) (Nat.mul_pos hm (by omega)) ?_ ?_
    · rw [hC]
      exact hTmcard
    · rw [hG, hsq]
      rw [show q * (q - 1) * (m * (q + 1)) = m * q * ((q - 1) * (q + 1)) by ring]
  ·
    have hle : A ≤ Tminus := zpowers_le_nonsplitTorus hb
    have hS := ncard_diff_zpowers hle
    rw [hTmcard, hAcard] at hS
    have h2m := two_mul_ncard_image_of_pairs (ConjClasses.mk)
      (fun t => wminus * t * wminus⁻¹) ((Tminus : Set G) \ (A : Set G)) ?_ ?_
    · rw [hS] at h2m
      have : m * (q + 1) - m = m * q := by rw [mul_add, mul_one, Nat.add_sub_cancel]
      rw [this] at h2m
      omega
    · rintro t ⟨ht, htA⟩
      refine ⟨⟨nonsplitWeyl_conj_mem z hz y hy h2 ht, conj_not_mem_zpowers htA _⟩,
        nonsplitWeyl_conj_ne y hy h2 hb ht htA⟩
    · rintro t ⟨ht, htA⟩ t' ⟨ht', -⟩
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      exact isConj_nonsplitTorus_iff y hy h2 hb ht htA ht'
  · intro g
    rw [hTplus]
    exact mem_normalizer_splitTorus_iff hb g
  · intro g hg
    by_cases hgA : g ∈ A
    · have h1 := hfix1 g hgA
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := h1.symm.trans (hfix2 g h)
        omega
      · have := h1.symm.trans (hfix3 g h)
        omega
    · have h0 := card_fixed_nonsplitTorus hb hg hgA
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := h0.symm.trans (hfix2 g h)
        omega
      · have := h0.symm.trans (hfix3 g h)
        omega

end CFSG.Wreathed.CentralSL2
