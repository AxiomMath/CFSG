module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Swap
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G]

@[expose] def DihedralCase (S A₁ A₂ : Subgroup G) : Prop :=
  (∃ a ∈ A₁, ∃ g : G, g⁻¹ * a * g ∈ S ∧ rightConjugate A₁ (g⁻¹ * a * g) = A₂) ∧
    (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ∧ Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2

@[expose] def Concl (S A₁ A₂ : Subgroup G) : Prop :=
  overlapClosure A₁ A₂ = ⊤ ∨ A₁ ≤ A₂ ∨ A₂ ≤ A₁ ∨ DihedralCase S A₁ A₂

@[expose] def Statement (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X ≤ n →
    ∀ (S : Sylow 2 X) (A₁ A₂ : Subgroup X), Hyp S A₁ A₂ → Concl (S : Subgroup X) A₁ A₂

theorem pRank_subgroupOf_eq [Finite G] (K A : Subgroup G) :
    pRank 2 (A.subgroupOf K) = pRank 2 (A ⊓ K) := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) K.subtype
      K.subtype_injective (A.subgroupOf K)
    rwa [Subgroup.subgroupOf_map_subtype] at h
  · obtain ⟨E, hE, ⟨hcomm, hpow⟩, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (A ⊓ K)
    have hEK : E ≤ K := hE.trans inf_le_right
    refine CFSG.SectionRank.le_pRank (by norm_num) (E := E.subgroupOf K) ?_ ?_ ?_
    · exact fun x hx => (hE hx).1
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => Subtype.ext (hpow _ hx)⟩
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val
        (hcomm.is_comm.comm (⟨((a : K) : G), a.property⟩ : E) ⟨((b : K) : G), b.property⟩)
      simpa only [Subgroup.coe_mul] using this
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hEcard]

theorem commutator_subgroupOf_eq_bot {A₁ A₂ : Subgroup G} (hc : ⁅A₁, A₂⁆ = ⊥) (K : Subgroup G) :
    ⁅A₁.subgroupOf K, A₂.subgroupOf K⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subtype.ext (commute_of_comm hc hx hy).symm.eq

theorem overlapClosure_subgroupOf_map_le (A₁ A₂ K : Subgroup G) :
    (overlapClosure (A₁.subgroupOf K) (A₂.subgroupOf K)).map K.subtype ≤
      overlapClosure A₁ A₂ := by
  rw [overlapClosure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨k, ⟨X, hX, Y, hY, hk⟩, rfl⟩
  obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hk
  have hxX : x ∈ rightConjugate X k := hx.1
  have hxY : x ∈ Y := hx.2
  rw [mem_rightConjugate_iff] at hxX
  have hX' : ∀ {B : Subgroup G}, X = B.subgroupOf K →
      (k : G) * x * (k : G)⁻¹ ∈ B := by
    rintro B rfl
    exact hxX
  have hY' : ∀ {B : Subgroup G}, Y = B.subgroupOf K → (x : G) ∈ B := by
    rintro B rfl
    exact hxY
  have hx1' : (k : G) * x * (k : G)⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    apply Subtype.ext
    calc (x : G) = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have heq : (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * k = x := by group
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  change (k : G) ∈ overlapClosure A₁ A₂
  rcases hX with hX | hX <;> rcases hY with hY | hY
  · exact mem_overlapClosure_of_conj (Or.inl rfl) (Or.inl rfl) (hX' hX) hx1'
      (by rw [heq]; exact hY' hY)
  · exact mem_overlapClosure_of_conj (Or.inl rfl) (Or.inr rfl) (hX' hX) hx1'
      (by rw [heq]; exact hY' hY)
  · exact mem_overlapClosure_of_conj (Or.inr rfl) (Or.inl rfl) (hX' hX) hx1'
      (by rw [heq]; exact hY' hY)
  · exact mem_overlapClosure_of_conj (Or.inr rfl) (Or.inr rfl) (hX' hX) hx1'
      (by rw [heq]; exact hY' hY)

theorem card_inf_subgroupOf (A₁ A₂ K : Subgroup G) :
    Nat.card (A₁.subgroupOf K ⊓ A₂.subgroupOf K : Subgroup K) =
      Nat.card (A₁ ⊓ A₂ ⊓ K : Subgroup G) := by
  have h : A₁.subgroupOf K ⊓ A₂.subgroupOf K = (A₁ ⊓ A₂).subgroupOf K := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [h, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]

theorem not_dihedralCase_of_card {A₁ A₂ K : Subgroup G} (P : Subgroup K)
    (h : Nat.card (A₁ ⊓ A₂ ⊓ K : Subgroup G) ≠ 2) :
    ¬ DihedralCase P (A₁.subgroupOf K) (A₂.subgroupOf K) := by
  rintro ⟨-, -, hcard⟩
  rw [card_inf_subgroupOf] at hcard
  exact h hcard

variable [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

theorem Hyp.mem_normalizer_of_subgroupOf (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂)
    (h21 : ¬ A₂ ≤ A₁) {K : Subgroup G} (hn : ¬ A₁ ⊓ K ≤ A₂) {w : K}
    (hwS : (w : G) ∈ (S : Subgroup G))
    (hw : w ∈ Subgroup.normalizer ((A₁.subgroupOf K : Subgroup K) : Set K)) :
    (w : G) ∈ Subgroup.normalizer (A₁ : Set G) := by
  rcases h.sylow_le_pairStabilizer h12 h21 hwS with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact (rightConjugate_eq_self_iff A₁ _).mp h₁
  · exfalso
    apply hn
    rintro x ⟨hxA, hxK⟩
    have hmem : (⟨x, hxK⟩ : K) ∈ A₁.subgroupOf K := hxA
    have h1 := (Subgroup.mem_normalizer_iff.mp hw _).mp hmem
    rw [← h₁, mem_rightConjugate_iff]
    exact h1

theorem Hyp.le_overlapClosure_of_statement (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂)
    (h21 : ¬ A₂ ≤ A₁) (IH : Statement (Nat.card G - 1)) {K : Subgroup G} (hK : K ≠ ⊤)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (S : Subgroup G).subgroupOf K)
    (hr₁ : 2 ≤ pRank 2 (A₁ ⊓ K)) (hr₂ : 2 ≤ pRank 2 (A₂ ⊓ K))
    (hn₁ : ¬ A₁ ⊓ K ≤ A₂) (hn₂ : ¬ A₂ ⊓ K ≤ A₁)
    (h3 : ¬ DihedralCase (P : Subgroup K) (A₁.subgroupOf K) (A₂.subgroupOf K)) :
    K ≤ overlapClosure A₁ A₂ := by
  have hcardK : Nat.card K ≤ Nat.card G - 1 := by
    have h1 := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hK)
    rw [Subgroup.card_top] at h1
    omega
  have hmap := overlapClosure_subgroupOf_map_le A₁ A₂ K
  have hmemH : ∀ y ∈ overlapClosure (A₁.subgroupOf K) (A₂.subgroupOf K),
      (y : G) ∈ overlapClosure A₁ A₂ := fun y hy => hmap ⟨y, hy, rfl⟩
  have hmemS : ∀ y : K, y ∈ (P : Subgroup K) → (y : G) ∈ (S : Subgroup G) := by
    intro y hy
    rw [hP] at hy
    exact hy
  have hunion : ∀ y : K, y ∈ ((A₁.subgroupOf K : Subgroup K) : Set K) ∪
      (A₂.subgroupOf K : Subgroup K) ↔ (y : G) ∈ (A₁ : Set G) ∪ A₂ := fun y => Iff.rfl
  have hconj : ∀ y a : K, ((y⁻¹ * a * y : K) : G) = (y : G)⁻¹ * a * y := fun _ _ => rfl
  have hyp : Hyp P (A₁.subgroupOf K) (A₂.subgroupOf K) :=
    { le_one := fun x hx => by rw [hP]; exact h.le_one hx
      le_two := fun x hx => by rw [hP]; exact h.le_two hx
      comm := commutator_subgroupOf_eq_bot h.comm K
      rank_one := by rw [pRank_subgroupOf_eq]; exact hr₁
      rank_two := by rw [pRank_subgroupOf_eq]; exact hr₂
      closed_overlap := by
        intro a ha y hy hmem
        rw [hunion, hconj]
        exact h.conj_mem_of_mem_overlapClosure ((hunion a).mp ha) (hmemH y hy)
          (hmemS _ hmem.2)
      closed_one := by
        intro a ha y _ hmem
        rw [hunion, hconj]
        exact h.conj_mem_of_mem_normalizer ((hunion a).mp ha) (hmemS _ hmem.1)
          (Or.inl (h.mem_normalizer_of_subgroupOf h12 h21 hn₁ (hmemS _ hmem.1) hmem.2))
      closed_two := by
        intro a ha y _ hmem
        rw [hunion, hconj]
        exact h.conj_mem_of_mem_normalizer ((hunion a).mp ha) (hmemS _ hmem.1)
          (Or.inr (h.symm.mem_normalizer_of_subgroupOf h21 h12 hn₂ (hmemS _ hmem.1)
            hmem.2)) }
  rcases IH K hcardK P (A₁.subgroupOf K) (A₂.subgroupOf K) hyp with htop | hle | hle | hd
  · intro k hk
    exact hmemH ⟨k, hk⟩ (htop ▸ Subgroup.mem_top _)
  · exact absurd (fun x hx => hle (show (⟨x, hx.2⟩ : K) ∈ A₁.subgroupOf K from hx.1)) hn₁
  · exact absurd (fun x hx => hle (show (⟨x, hx.2⟩ : K) ∈ A₂.subgroupOf K from hx.1)) hn₂
  · exact absurd hd h3

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
