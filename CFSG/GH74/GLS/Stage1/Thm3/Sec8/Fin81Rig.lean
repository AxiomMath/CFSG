module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AutCfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Q8

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

theorem FusedCfg.exists_labelling {A A' : Type*} [Group A] [Group A'] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'}
    (hc : FusedCfg K₁ K₂ S F) (hc' : FusedCfg K₁' K₂' S' F) (g : M128 ≃* ↥S) (α : ↥S ≃* ↥S') :
    ((∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₁') ∧
        (∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₂')) ∨
      ((∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₂') ∧
        (∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₁')) := by
  obtain ⟨q1⟩ := (hc.nonempty_equiv_q8 hodd hmod).1
  obtain ⟨q2⟩ := (hc.nonempty_equiv_q8 hodd hmod).2
  obtain ⟨q1'⟩ := (hc'.nonempty_equiv_q8 hodd hmod).1
  obtain ⟨q2'⟩ := (hc'.nonempty_equiv_q8 hodd hmod).2
  obtain ⟨z, hz, hzo, hzS, hzc⟩ := hc.z_ex
  obtain ⟨z', hz', hzo', hzS', hzc'⟩ := hc'.z_ex
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzo; omega
  have hz1' : z' ≠ 1 := fun h => by rw [h, orderOf_one] at hzo'; omega
  have key := q8_pair_transport g α ((S ⊓ K₁).subgroupOf S) ((S ⊓ K₂).subgroupOf S)
    ((S' ⊓ K₁').subgroupOf S') ((S' ⊓ K₂').subgroupOf S')
    ((Subgroup.subgroupOfEquivOfLe (inf_le_left : S ⊓ K₁ ≤ S)).trans q1)
    ((Subgroup.subgroupOfEquivOfLe (inf_le_left : S ⊓ K₂ ≤ S)).trans q2)
    ((Subgroup.subgroupOfEquivOfLe (inf_le_left : S' ⊓ K₁' ≤ S')).trans q1')
    ((Subgroup.subgroupOfEquivOfLe (inf_le_left : S' ⊓ K₂' ≤ S')).trans q2')
    (fun a ha b hb => Subtype.ext (hc.comm _ ha.2 _ hb.2))
    (fun a ha b hb => Subtype.ext (hc'.comm _ ha.2 _ hb.2))
    ⟨z, hzS⟩ (fun h => hz1 (congrArg Subtype.val h))
    (fun s => Subtype.ext (hzc _ s.2)) ⟨hzS, hz.1⟩ ⟨hzS, hz.2⟩
    ⟨z', hzS'⟩ (fun h => hz1' (congrArg Subtype.val h))
    (fun s => Subtype.ext (hzc' _ s.2)) ⟨hzS', hz'.1⟩ ⟨hzS', hz'.2⟩
  have conv : ∀ (K : Subgroup A) (K' : Subgroup A') (x : ↥S),
      (x ∈ (S ⊓ K).subgroupOf S ↔ α x ∈ (S' ⊓ K').subgroupOf S') ↔
        ((x : A) ∈ K ↔ ((α x : ↥S') : A') ∈ K') := by
    intro K K' x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h; constructor
      · intro hx; exact (h.1 ⟨x.2, hx⟩).2
      · intro hx; exact (h.2 ⟨(α x).2, hx⟩).2
    · intro h; constructor
      · intro hx; exact ⟨(α x).2, h.1 hx.2⟩
      · intro hx; exact ⟨x.2, h.2 hx.2⟩
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact Or.inl ⟨fun x => (conv K₁ K₁' x).1 (k1 x), fun x => (conv K₂ K₂' x).1 (k2 x)⟩
  · exact Or.inr ⟨fun x => (conv K₁ K₂' x).1 (k1 x), fun x => (conv K₂ K₁' x).1 (k2 x)⟩

theorem rigidity {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A'] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'}
    (hc : FusedCfg K₁ K₂ S F) (hc' : FusedCfg K₁' K₂' S' F) (g : M128 ≃* ↥S) (α : ↥S ≃* ↥S') :
    Nonempty (↥(K₁ ⊔ K₂ ⊔ S) ≃* ↥(K₁' ⊔ K₂' ⊔ S')) := by
  rcases hc.exists_labelling hodd hmod hc' g α with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact rigidity_core hodd h5 hmod hc hc' α h₁ h₂
  · obtain ⟨Ψ⟩ := rigidity_core hodd h5 hmod hc hc'.swap α h₁ h₂
    exact ⟨Ψ.trans (MulEquiv.subgroupCongr (by rw [sup_comm K₂' K₁']))⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
