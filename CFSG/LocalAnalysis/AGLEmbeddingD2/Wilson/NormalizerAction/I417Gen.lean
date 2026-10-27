module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3KFacts
public import CFSG.RankThree.Asc83Table.E27
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofJ3
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofFour

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4 Subgroup

theorem isElemAbelian_iff {p : ℕ} {G : Type*} [Group G] {E : Subgroup G} :
    CFSG.Assembly.IsElemAbelian p E ↔
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ p = 1 := by
  rw [isElemAbelian_iff_isElementaryAbelian, isElementaryAbelian_iff]

theorem isElemAbelian_map_hom {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (h : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.map f) := by
  rw [isElemAbelian_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.2 x hx, map_one]

theorem isElemAbelian_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : CFSG.Assembly.IsElemAbelian 3 (A ⊔ B) := by
  rw [isElemAbelian_iff] at hA hB ⊢
  have hcomm : ∀ x ∈ (A : Set G) ∪ (B : Set G), ∀ y ∈ (A : Set G) ∪ (B : Set G),
      x * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA.1 x hx y hy
    · exact h x hx y hy
    · exact (h y hy x hx).symm
    · exact hB.1 x hx y hy
  have hc : IsMulCommutative (Subgroup.closure ((A : Set G) ∪ (B : Set G))) :=
    isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  rw [Subgroup.sup_eq_closure]
  have hab : ∀ a ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)),
      ∀ b ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : Subgroup.closure ((A : Set G) ∪ (B : Set G))) ⟨b, hb⟩)
  refine ⟨hab, fun a ha => ?_⟩
  induction ha using closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA.2 x hx
    · exact hB.2 x hx
  | one => exact one_pow 3
  | mul a b ha hb h₁ h₂ => rw [(show Commute a b from hab a ha b hb).mul_pow, h₁, h₂, one_mul]
  | inv a _ h => rw [inv_pow, h, inv_one]

theorem IsExtOf.of_mulEquiv {X X' A B : Type*} [Group X] [Group X'] [Group A] [Group B]
    (f : X ≃* X') (h : IsExtOf X A B) : IsExtOf X' A B := by
  obtain ⟨K, hK, ⟨eB⟩, ⟨eA⟩⟩ := h
  refine ⟨K.map f.toMonoidHom, hK.map _ f.surjective, ⟨?_⟩, ⟨?_⟩⟩
  · exact (MulEquiv.subgroupMap f K).symm.trans eB
  · refine (QuotientGroup.congr K (K.map f.toMonoidHom) f rfl).symm.trans eA

theorem card_eq_pow_of_isElemAbelian_of_equiv_J3
    {Q : Type} [Group Q]
    (e : Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .J3)
    {D : Subgroup Q} (hD : CFSG.Assembly.IsElemAbelian 3 D) : ∃ k ≤ 3, Nat.card D = 3 ^ k := by
  have hmap := isElemAbelian_map_hom e.toMonoidHom hD
  obtain ⟨k, hk3, hk⟩ := Res417Four.exists_card_eq_of_isElemAbelian_J3
    (D := D.map e.toMonoidHom) hmap
  have hc := Subgroup.card_map_of_injective (f := e.toMonoidHom) (K := D) e.injective
  exact ⟨k, hk3, by rw [← hc]; exact hk⟩

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
