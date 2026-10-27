module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreShape
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open CFSG Subgroup CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.CoreAux

variable {G : Type} [Group G]

abbrev four (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) : Subgroup G :=
  CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab

theorem mem_four {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : Commute a b} {x : G} :
    x ∈ four a b ha hb hab ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 :=
  Iff.rfl

theorem four_le {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : Commute a b} {H : Subgroup G}
    (haH : a ∈ H) (hbH : b ∈ H) : four a b ha hb hab ≤ H := by
  intro x hx
  rcases mem_four.mp hx with h | h | h | h <;> rw [h]
  · exact mul_mem haH hbH
  · exact haH
  · exact hbH
  · exact one_mem _

theorem left_mem_four {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : Commute a b} :
    a ∈ four a b ha hb hab :=
  mem_four.mpr (Or.inr (Or.inl rfl))

theorem right_mem_four {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : Commute a b} :
    b ∈ four a b ha hb hab :=
  mem_four.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem commute_of_mem_four {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : Commute a b}
    {c : G} (hca : Commute c a) (hcb : Commute c b) {x : G} (hx : x ∈ four a b ha hb hab) :
    Commute c x := by
  rcases mem_four.mp hx with h | h | h | h <;> rw [h]
  · exact hca.mul_right hcb
  · exact hca
  · exact hcb
  · exact Commute.one_right c

theorem isElemAbelian_four (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    Open.IsElemAbelian 2 (four a b ha hb hab) := by
  have hc : ∀ x ∈ four a b ha hb hab, Commute x a ∧ Commute x b := by
    intro x hx
    rcases mem_four.mp hx with h | h | h | h <;> rw [h]
    · exact ⟨(Commute.refl a).mul_left hab.symm, hab.mul_left (Commute.refl b)⟩
    · exact ⟨Commute.refl a, hab⟩
    · exact ⟨hab.symm, Commute.refl b⟩
    · exact ⟨Commute.one_left a, Commute.one_left b⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨hxa, hxb⟩ := hc x x.2
    exact (commute_of_mem_four hxa hxb y.2).eq
  · rw [pow_two]
    rcases mem_four.mp hx with h | h | h | h <;> rw [h]
    · rw [hab.symm.mul_mul_mul_comm, ha, hb, one_mul]
    · exact ha
    · exact hb
    · exact mul_one 1

theorem card_four {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (four a b ha hb hab) = 4 :=
  (CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hne
    hab).card_four

theorem mul_self_eq_one_of_isElemAbelian {U : Subgroup G} (hU : Open.IsElemAbelian 2 U) {x : G}
    (hx : x ∈ U) : x * x = 1 := by
  rw [← pow_two]
  exact hU.2 x hx

theorem commute_of_isElemAbelian {U : Subgroup G} (hU : Open.IsElemAbelian 2 U) {x y : G}
    (hx : x ∈ U) (hy : y ∈ U) : Commute x y := by
  have h := hU.1.is_comm.comm (⟨x, hx⟩ : U) ⟨y, hy⟩
  exact congrArg Subtype.val h

theorem eq_four [Finite G] {U : Subgroup G} (hU : Open.IsElemAbelian 2 U) (hU4 : Nat.card U = 4)
    {a b : G} (haU : a ∈ U) (hbU : b ∈ U) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    U = four a b (mul_self_eq_one_of_isElemAbelian hU haU)
      (mul_self_eq_one_of_isElemAbelian hU hbU) (commute_of_isElemAbelian hU haU hbU) := by
  symm
  refine eq_of_le_of_card_ge (four_le haU hbU) ?_
  rw [hU4, card_four _ _ _ ha1 hb1 hne]

theorem isElemAbelian_sup_zpowers [Finite G] {V : Subgroup G} (hV : Open.IsElemAbelian 2 V)
    {c : G} (hc : c * c = 1) (hcV : c ∉ V) (hcomm : ∀ v ∈ V, Commute v c) :
    Open.IsElemAbelian 2 (V ⊔ zpowers c) ∧ Nat.card ↥(V ⊔ zpowers c) = Nat.card V * 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers (p := 2)
    (A := V) ⟨hV.1, hV.2⟩ hcV (by rw [pow_two]; exact hc) fun v hv => (hcomm v hv).eq
  exact ⟨⟨h1, h2⟩, h3⟩

theorem le_pRank_of_le [Finite G] {H E : Subgroup G} (hEH : E ≤ H) (hE : Open.IsElemAbelian 2 E)
    {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ Open.pRank 2 H :=
  CFSG.SectionRank.le_pRank (by norm_num) hEH hE hk

theorem fourAdj_symm {S : Subgroup G} {U V : FourSub S} (h : FourAdj S U V) : FourAdj S V U := by
  obtain ⟨E, hES, hEab, hE8, hUE, hVE⟩ := h
  exact ⟨E, hES, hEab, hE8, hVE, hUE⟩

theorem reflTransGen_fourAdj_symm {S : Subgroup G} {U V : FourSub S}
    (h : Relation.ReflTransGen (FourAdj S) U V) : Relation.ReflTransGen (FourAdj S) V U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (fourAdj_symm hbc) ih

theorem connected_of_hub {S : Subgroup G} (H : FourSub S)
    (h : ∀ U : FourSub S, Relation.ReflTransGen (FourAdj S) U H) :
    ∀ U V : FourSub S, Relation.ReflTransGen (FourAdj S) U V :=
  fun U V => (h U).trans (reflTransGen_fourAdj_symm (h V))

theorem connected_of_mulEquiv {K K' : Type} [Group K] [Group K'] {S : Subgroup K}
    {S' : Subgroup K'} (e : ↥S ≃* ↥S')
    (h : ∀ U V : FourSub S, Relation.ReflTransGen (FourAdj S) U V) :
    ∀ U V : FourSub S', Relation.ReflTransGen (FourAdj S') U V := by
  let ι : FourSub S' → FourSub S := fun V =>
    ⟨shapeMap e.symm V.1, shapeMap_le e.symm _, isElemAbelian_shapeMap e.symm V.2.2.1,
      by rw [card_shapeMap e.symm V.2.1, V.2.2.2]⟩
  let κ : FourSub S → FourSub S' := fun V =>
    ⟨shapeMap e V.1, shapeMap_le e _, isElemAbelian_shapeMap e V.2.2.1,
      by rw [card_shapeMap e V.2.1, V.2.2.2]⟩
  have hκι : ∀ V : FourSub S', κ (ι V) = V := fun V =>
    Subtype.ext (shapeMap_shapeMap_symm e V.2.1)
  have hκ : ∀ U V : FourSub S, FourAdj S U V → FourAdj S' (κ U) (κ V) := by
    rintro U V ⟨E, hES, hEab, hE8, hUE, hVE⟩
    exact ⟨shapeMap e E, shapeMap_le e E, isElemAbelian_shapeMap e hEab,
      by rw [card_shapeMap e hES]; exact hE8, shapeMap_mono e hUE, shapeMap_mono e hVE⟩
  intro V W
  have : Relation.ReflTransGen (FourAdj S') (κ (ι V)) (κ (ι W)) :=
    Relation.ReflTransGen.lift κ hκ _ _ (h (ι V) (ι W))
  rwa [hκι, hκι] at this

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
