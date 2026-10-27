module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

abbrev Elem2 (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

@[expose] def IsExtensionShape (X : Type*) [Group X] (A B : Type*) [Group A] [Group B] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), Nonempty (N ≃* A) ∧ Nonempty (X ⧸ N ≃* B)

@[expose] def IsShapeTwoTwoSixS5 (X : Type*) [Group X] : Prop :=
  ∃ (V N : Subgroup X) (_ : V.Normal) (_ : N.Normal), V ≤ N ∧ Nonempty (V ≃* Elem2 2) ∧
    Nonempty (N ⧸ V.subgroupOf N ≃* Elem2 6) ∧ Nonempty (X ⧸ N ≃* Equiv.Perm (Fin 5))

@[expose] def IsShapeTwoTwoTimesA8 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 × alternatingGroup (Fin 8))

@[expose] def IsShapeTwoTwoTimesTwoFourA5 (X : Type*) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y), IsExtensionShape Y (Elem2 4) (alternatingGroup (Fin 5)) ∧
    Nonempty (X ≃* Elem2 2 × Y)

@[expose] def IsNonsplitDoubleCoverOfS5 (Y : Type*) [Group Y] : Prop :=
  ∃ (Z : Subgroup Y) (_ : Z.Normal), Nat.card Z = 2 ∧ Nonempty (Y ⧸ Z ≃* Equiv.Perm (Fin 5)) ∧
    Z ≤ commutator Y

private lemma commutator_mul_left_of_central {G : Type*} [Group G] {z s t : G}
    (hz : ∀ x : G, z * x = x * z) : ⁅z * s, t⁆ = ⁅s, t⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr (hz t), mul_one]
  rw [hz ⁅s, t⁆, mul_assoc, mul_inv_cancel, mul_one]

private lemma commutator_mul_right_of_central {G : Type*} [Group G] {t z s : G}
    (hz : ∀ x : G, z * x = x * z) : ⁅t, z * s⁆ = ⁅t, s⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_mul_comm.mpr (hz t).symm, one_mul]
  rw [hz ⁅t, s⁆, mul_assoc, mul_inv_cancel, mul_one]

theorem IsNonsplitDoubleCoverOfS5.no_complement_of_le_commutator {Y : Type*} [Group Y]
    {Z : Subgroup Y} (hZ : Z.Normal) (hcard : Nat.card Z = 2) (hc : Z ≤ commutator Y) :
    ¬ ∃ S : Subgroup Y, Z.IsComplement' S := by
  rintro ⟨S, hS⟩
  have hcen : ∀ z ∈ Z, ∀ y : Y, z * y = y * z := by
    intro z hz y
    by_cases h1 : z = 1
    · simp [h1]
    · obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hcard
      have h2 : y * z * y⁻¹ ∈ Z := hZ.conj_mem z hz y
      have h3 : y * z * y⁻¹ ≠ 1 := by
        intro h
        rw [mul_inv_eq_one] at h
        exact h1 (by simpa using h)
      have e1 := hw ⟨z, hz⟩ (fun h => h1 (congrArg Subtype.val h))
      have e2 := hw ⟨y * z * y⁻¹, h2⟩ (fun h => h3 (congrArg Subtype.val h))
      have e3 : y * z * y⁻¹ = z := congrArg Subtype.val (e2.trans e1.symm)
      calc z * y = (y * z * y⁻¹) * y := by rw [e3]
        _ = y * z := by group
  have hcomm_le : commutator Y ≤ S := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro y1 _ y2 _
    obtain ⟨⟨⟨z1, hz1⟩, ⟨s1, hs1⟩⟩, h1⟩ := hS.2 y1
    obtain ⟨⟨⟨z2, hz2⟩, ⟨s2, hs2⟩⟩, h2⟩ := hS.2 y2
    rw [← h1, ← h2]
    rw [commutator_mul_left_of_central (z := z1) (s := s1) (t := z2 * s2) (hcen z1 hz1),
      commutator_mul_right_of_central (z := z2) (s := s2) (t := s1) (hcen z2 hz2)]
    exact mul_mem (mul_mem (mul_mem hs1 hs2) (inv_mem hs1)) (inv_mem hs2)
  have hdisj : Disjoint Z S := hS.disjoint
  have hbot : Z = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall Z).mpr fun z hz => ?_
    simpa using hdisj.le_bot ⟨hz, hcomm_le (hc hz)⟩
  rw [hbot, Subgroup.card_bot] at hcard
  omega

theorem IsNonsplitDoubleCoverOfS5.not_complement {Y : Type*} [Group Y]
    (h : IsNonsplitDoubleCoverOfS5 Y) :
    ∃ (Z : Subgroup Y) (_ : Z.Normal), Nat.card Z = 2 ∧ Nonempty (Y ⧸ Z ≃* Equiv.Perm (Fin 5)) ∧
      ¬ ∃ S : Subgroup Y, Z.IsComplement' S := by
  obtain ⟨Z, hZ, hcard, hiso, hc⟩ := h
  exact ⟨Z, hZ, hcard, hiso,
    IsNonsplitDoubleCoverOfS5.no_complement_of_le_commutator hZ hcard hc⟩

@[expose] def IsShapeCentralizerThree (X : Type*) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y),
    IsExtensionShape Y (Elem2 2 × alternatingGroup (Fin 5)) (Multiplicative (ZMod 2)) ∧
      Nonempty (X ≃* Multiplicative (ZMod 3) × Y)

@[expose] def IsShapeCentralizerFiveA (X : Type*) [Group X] : Prop :=
  ∃ (N S : Subgroup X) (_ : N.Normal), CFSG.IsExtraspecial 5 ↥N ∧ Nat.card N = 5 ^ 3 ∧
    (∀ x : N, x ^ 5 = 1) ∧ Nonempty (S ≃* Multiplicative (ZMod 2) × QuaternionGroup 2) ∧
      N.IsComplement' S

@[expose] def IsShapeCentralizerFiveB (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 2) × DihedralGroup 5)

@[expose] def IsShapeCentralizerFiveC (X : Type*) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y), IsNonsplitDoubleCoverOfS5 Y ∧
    Nonempty (X ≃* Multiplicative (ZMod 5) × Y)

@[expose] def IsShapeCentralizerSeven (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 7) × Elem2 2)

@[expose] def IsShapeCentralizerEleven (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 11) × Multiplicative (ZMod 2))

@[expose] def IsShapeK (K : Type*) [Group K] : Prop :=
  ∃ (N : Subgroup K) (_ : N.Normal), IsPGroup 2 N ∧ Nat.card N = 2 ^ 7 ∧
    Nonempty (K ⧸ N ≃* Equiv.Perm (Fin 5)) ∧
    Nonempty (center N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) ∧
    ∃ Q : Subgroup N, IsPlusExtraspecial 2 Q ∧ center N ⊔ Q = ⊤ ∧
      Nat.card (center N ⊓ Q : Subgroup N) = 2

structure TwoHSFacts (H : Type) [Group H] (a z b z₁ : H) : Prop where
  center_eq : center H = zpowers a
  orderOf_a : orderOf a = 2
  orderOf_z : orderOf z = 2
  orderOf_b : orderOf b = 2
  orderOf_z₁ : orderOf z₁ = 2
  not_isConj : ∀ i j : Fin 5, i ≠ j →
    ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j)
  involution_cover : ∀ x : H, orderOf x = 2 → ∃ i : Fin 5, IsConj (![a, z, a * z, b, z₁] i) x
  cent_z : IsShapeTwoTwoSixS5 (centralizer ({z} : Set H))
  cent_az : IsShapeTwoTwoSixS5 (centralizer ({a * z} : Set H))
  cent_b : IsShapeTwoTwoTimesA8 (centralizer ({b} : Set H))
  cent_z₁ : IsShapeTwoTwoTimesTwoFourA5 (centralizer ({z₁} : Set H))
  mem_commutator : a ∈ commutator H ∧ z ∈ commutator H ∧ a * z ∈ commutator H
  not_mem_commutator : b ∉ commutator H ∧ z₁ ∉ commutator H
  K_shape : IsShapeK ↥(commutator H ⊓ centralizer ({z} : Set H))
  center_K : ∀ g : ↥(commutator H ⊓ centralizer ({z} : Set H)),
    g ∈ center ↥(commutator H ⊓ centralizer ({z} : Set H)) ↔ (g : H) ∈ zpowers a ⊔ zpowers z
  exists_sq_eq : ∃ g : H, g ^ 2 = a
  isConj_of_sq_eq : ∀ g g' : H, g ^ 2 = a → g' ^ 2 = a → IsConj g g'
  not_isSectionOf_A8 : ∀ g : H, g ^ 2 = a →
    ¬ CFSG.SignalizerFunctorTheorem.IsSectionOf (alternatingGroup (Fin 8))
      (centralizer ({g} : Set H))
  card_eq : Nat.card H = 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11
  table_three : ∀ x : H, orderOf x = 3 → IsShapeCentralizerThree (centralizer ({x} : Set H))
  table_five : ∀ x : H, orderOf x = 5 →
    IsShapeCentralizerFiveA (centralizer ({x} : Set H)) ∨
      IsShapeCentralizerFiveB (centralizer ({x} : Set H)) ∨
        IsShapeCentralizerFiveC (centralizer ({x} : Set H))
  table_seven : ∀ x : H, orderOf x = 7 → IsShapeCentralizerSeven (centralizer ({x} : Set H))
  table_eleven : ∀ x : H, orderOf x = 11 → IsShapeCentralizerEleven (centralizer ({x} : Set H))
  sl25_le_centralizer : ∀ ρ : H, orderOf ρ = 5 →
    IsShapeCentralizerFiveC (centralizer ({ρ} : Set H)) →
      ∃ S : Subgroup ↥(centralizer ({ρ} : Set H)),
        Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  sylow_two_five : ∀ ρ : H, orderOf ρ = 5 → IsShapeCentralizerFiveB (centralizer ({ρ} : Set H)) →
    ∀ T : Sylow 2 ↥(centralizer ({ρ} : Set H)), ∃ u : H, IsConj z₁ u ∧
      (T : Subgroup ↥(centralizer ({ρ} : Set H))).map (centralizer ({ρ} : Set H)).subtype =
        closure {a, u}
  m11_unique_class : (∃ M : Subgroup H, IsSporadic ↥M .M11) ∧
    ∀ M M' : Subgroup H, IsSporadic ↥M .M11 → IsSporadic ↥M' .M11 →
      ∃ g : H, M' = M.map (MulAut.conj g).toMonoidHom
  m11_centralizer_five : ∀ M : Subgroup H, IsSporadic ↥M .M11 → ∀ ρ ∈ M, orderOf ρ = 5 →
    IsShapeCentralizerFiveB (centralizer ({ρ} : Set H))
  centralizer_five_of_A8 : ∀ c : H, orderOf c = 2 →
    IsShapeTwoTwoTimesA8 (centralizer ({c} : Set H)) →
      ∀ ρ : H, orderOf ρ = 5 → ρ * c = c * ρ → IsShapeCentralizerFiveC (centralizer ({ρ} : Set H))

structure TwoHSInterface : Prop where
  nonempty_mulEquiv : ∀ (H H' : Type) [Group H] [Group H'] (E : Subgroup H) (E' : Subgroup H'),
    TwoHS.IsF5Centralizer H E → TwoHS.IsF5Centralizer H' E' → Nonempty (H ≃* H')
  facts : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∃ a z b z₁ : H, TwoHSFacts H a z b z₁

@[expose] def centerOf {C : Type*} [Group C] (Q : Subgroup C) : Subgroup C :=
  Q ⊓ centralizer (Q : Set C)

structure AschbacherHyp (C : Type) [Group C] (Q : Subgroup C) [Q.Normal] : Prop
    extends IsExtraspecialPlusByA5WrTwoWith C Q where
  irreducible : ∀ W : Subgroup C, centerOf Q ≤ W → W ≤ Q →
    (∀ g ∈ commutator C, ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = centerOf Q ∨ W = Q
  no_involution : ∀ t ∈ commutator C, t ^ 2 = 1 →
    ¬ Nonempty (↥(centralizer ({(t : C ⧸ Q)} : Set (C ⧸ Q)) ⊓
      (commutator C).map (QuotientGroup.mk' Q)) ≃* Elem2 2 × alternatingGroup (Fin 5))
  exists_involution : ∃ t : C, t ∉ commutator C ∧ t ^ 2 = 1 ∧ ∀ T : Sylow 2 C, t ∈ T →
    ∃ x ∈ Q, (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧
      ⁅t, x⁆ ∉ centerOf Q

@[expose] def AschbacherDichotomy : Prop :=
  ∀ (L : Type) [Group L] (Q : Subgroup L) [Q.Normal], IsPlusExtraspecial 4 Q →
    centralizer (Q : Set L) ≤ Q →
    Nonempty (L ⧸ Q ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) →
      ((∀ W : Subgroup L, centerOf Q ≤ W → W ≤ Q → (∀ g : L, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
          W = centerOf Q ∨ W = Q) ↔
        ∃ q ∈ Q, q ∉ centerOf Q ∧ ∃ S : Subgroup (L ⧸ Q),
          (∀ x : L ⧸ Q, x ∈ S ↔ ∃ g : L, (g : L ⧸ Q) = x ∧ ⁅g, q⁆ ∈ centerOf Q) ∧
            Nonempty (S ≃* alternatingGroup (Fin 5)))

@[expose] def HaradaHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ t : G, orderOf t = 2 →
      ∀ E : Subgroup (centralizer ({t} : Set G)),
        TwoHS.IsF5Centralizer (centralizer ({t} : Set G)) E →
          ∃ z : G, orderOf z = 2 ∧ IsExtraspecialPlusByA5WrTwo (centralizer ({z} : Set G))

structure HNSideFacts : Prop where
  finite : Finite (Carrier .HN)
  isSimpleGroup : IsSimpleGroup (Carrier .HN)
  isF5Type : ∃ a z : Carrier .HN, IsF5Type a z
  isF5Centralizer_of_component : ∀ z₀ : Carrier .HN, orderOf z₀ = 2 →
    (∃ K : Subgroup (centralizer ({z₀} : Set (Carrier .HN))), CFSG.IsComponent K) →
      ∃ E : Subgroup (centralizer ({z₀} : Set (Carrier .HN))),
        TwoHS.IsF5Centralizer (centralizer ({z₀} : Set (Carrier .HN))) E

end CFSG.EvenSporadicStandard.HNRecog
