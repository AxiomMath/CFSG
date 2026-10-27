module

public import CFSG.HardMathSupport.Solomon.Proving.L2OrderUnique
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open scoped commutatorElement

theorem t6psph_not_isTypeL2_of_card_lt {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : 10 ≤ q)
    (hc : Nat.card Y < 495) : ¬ IsTypeL2 q Y := by
  intro hT
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card Y hT
  have hM : Nat.card (Y ⧸ Subgroup.center Y) ≤ Nat.card Y :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h3 : 100 * q ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul hq hq]
  rcases Nat.even_or_odd q with he | ho
  · have := (heven he).1
    omega
  · have := hodd ho
    omega

@[expose] def t6psph_SqOK (q : ℕ) (G : Type) [Group G] : Prop :=
  CFSG.IsQuasisimple ↥(commutator G) → IsTypeL2 q ↥(commutator G) →
    ∀ g : G, ∃ n ∈ commutator G, ∃ z ∈ Subgroup.center G, g ^ 2 = n * z

theorem t6psph_sqOK_of_mulEquiv {q : ℕ} {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : t6psph_SqOK q G') : t6psph_SqOK q G := by
  intro hQ hT g
  have hmap : (commutator G).map e.toMonoidHom = commutator G' := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
  let ec : ↥(commutator G) ≃* ↥(commutator G') :=
    ((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨n', hn', z', hz', hgz⟩ := h (CFSG.LocalCores.isQuasisimple_of_mulEquiv ec hQ)
    (p6_isTypeL2_of_equiv ec hT) (e g)
  refine ⟨e.symm n', ?_, e.symm z', ?_, ?_⟩
  · have : e.symm n' ∈ (commutator G').map e.symm.toMonoidHom := ⟨n', hn', rfl⟩
    rwa [← hmap, Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from
      by ext; simp, Subgroup.map_id] at this
  · rw [Subgroup.mem_center_iff] at hz' ⊢
    intro y
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hz' (e y)
  · apply e.injective
    simp only [map_pow, map_mul, MulEquiv.apply_symm_apply]
    exact hgz

@[expose] def t6psph_HsqProp (q : ℕ) {X : Type} [Group X] (F : Subgroup X) : Prop :=
  CFSG.IsQuasisimple ↥⁅F, F⁆ → IsTypeL2 q ↥⁅F, F⁆ →
    ∀ g ∈ F, ∃ n ∈ ⁅F, F⁆, ∃ z ∈ F, (∀ m ∈ F, z * m = m * z) ∧ g ^ 2 = n * z

theorem t6psph_hsqProp_of_sqOK {q : ℕ} {X : Type} [Group X] (F : Subgroup X)
    (h : t6psph_SqOK q ↥F) : t6psph_HsqProp q F := by
  intro hQ hT g hg
  let e : ↥(commutator ↥F) ≃* ↥⁅F, F⁆ :=
    ((commutator ↥F).equivMapOfInjective F.subtype F.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator F))
  obtain ⟨n, hn, z, hz, hgz⟩ := h (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ)
    (p6_isTypeL2_of_equiv e.symm hT) ⟨g, hg⟩
  refine ⟨(n : X), ?_, (z : X), z.2, fun m hm => ?_, congrArg Subtype.val hgz⟩
  · rw [← Subgroup.map_subtype_commutator F]
    exact ⟨n, hn, rfl⟩
  · exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨m, hm⟩).symm

theorem t6psph_hsqProp_of_equiv {q : ℕ} {X G : Type} [Group X] [Group G] (F : Subgroup X)
    (e : ↥F ≃* G) (h : t6psph_SqOK q G) : t6psph_HsqProp q F :=
  t6psph_hsqProp_of_sqOK F (t6psph_sqOK_of_mulEquiv e h)

theorem t6psph_sqOK_of_commutator_eq_top {q : ℕ} {G : Type} [Group G] (h : commutator G = ⊤) :
    t6psph_SqOK q G := fun _ _ g =>
  ⟨g ^ 2, by rw [h]; exact Subgroup.mem_top _, 1, Subgroup.one_mem _, by simp⟩

theorem t6psph_sqOK_of_card_lt {q : ℕ} {G : Type} [Group G] [Finite G] (hq : 10 ≤ q)
    (h : Nat.card ↥(commutator G) < 495) : t6psph_SqOK q G := fun _ hT _ =>
  absurd hT (t6psph_not_isTypeL2_of_card_lt hq h)

theorem t6psph_sqOK_of_commutative {q : ℕ} {G : Type} [Group G] [Finite G] (hq : 10 ≤ q)
    (h : ∀ a b : G, a * b = b * a) : t6psph_SqOK q G := by
  refine t6psph_sqOK_of_card_lt hq ?_
  have hbot : commutator G = ⊥ := by
    rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, h a b, mul_inv_cancel_right, mul_inv_cancel]
  rw [hbot]
  simp

theorem t6psph_sq_of_scalar {G A : Type*} [Group G] [CommGroup A] (D : G →* A)
    (hz : ∀ g : G, ∃ z ∈ Subgroup.center G, D z = D g ^ 2) (g : G) :
    ∃ n ∈ D.ker, ∃ z ∈ Subgroup.center G, g ^ 2 = n * z := by
  obtain ⟨z, hzc, hDz⟩ := hz g
  refine ⟨g ^ 2 * z⁻¹, ?_, z, hzc, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hDz, map_pow, mul_inv_cancel]

theorem t6psph_commutator_eq_ker {G A : Type*} [Group G] [CommGroup A] (D : G →* A)
    (hq : Group.IsPerfect ↥D.ker) : commutator G = D.ker := by
  have hle : commutator G ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator G := by
    have h1 := Subgroup.isPerfect_iff.mp hq
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (_root_.commutator_def G).symm
  exact le_antisymm hle hge

end CFSG.HardMathSupport.Dickson.Sec6.I1431
