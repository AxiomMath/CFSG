module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KC.StabChain

variable {G X : Type*} [Group G]

@[expose] def ChainOK (act : G → X → X) (H : Subgroup G) : List (X × List G) → Prop
  | [] => True
  | (b, T) :: L => (∀ t ∈ T, t ∈ H) ∧ (T.map fun t => act t b).Nodup ∧
      (∀ l ∈ L, ∀ t ∈ l.2, act t b = b) ∧ ChainOK act H L

theorem exists_finset_of_chainOK (act : G → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (hone : ∀ x, act 1 x = x)
    (H : Subgroup G) : ∀ L : List (X × List G), ChainOK act H L → ∃ s : Finset G,
      s.card = (L.map fun l => l.2.length).prod ∧ (∀ g ∈ s, g ∈ H) ∧
      ∀ x, (∀ l ∈ L, ∀ t ∈ l.2, act t x = x) → ∀ g ∈ s, act g x = x
  | [], _ => ⟨{1}, rfl, fun g hg => by rw [Finset.mem_singleton.1 hg]; exact H.one_mem,
      fun x _ g hg => by rw [Finset.mem_singleton.1 hg, hone]⟩
  | (b, T) :: L, h => by
    classical
    obtain ⟨hT, hnd, hfix, hL⟩ := h
    obtain ⟨s, hcard, hsH, hsfix⟩ := exists_finset_of_chainOK act hmul hone H L hL
    have hpb : ∀ p ∈ s, act p b = b := hsfix b hfix
    refine ⟨(T.toFinset ×ˢ s).image (fun q => q.1 * q.2), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn, Finset.card_product,
        List.toFinset_card_of_nodup (List.Nodup.of_map _ hnd), hcard, List.map_cons,
        List.prod_cons]
      rintro ⟨t, p⟩ hq ⟨t', p'⟩ hq' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hq hq'
      have hb : act t b = act t' b := by
        have := congrArg (fun g => act g b) h
        simpa only [hmul, hpb p hq.2, hpb p' hq'.2] using this
      have htt : t = t' := List.inj_on_of_nodup_map hnd hq.1 hq'.1 hb
      subst htt
      have h' : t * p = t * p' := h
      rw [mul_left_cancel h']
    · intro g hg
      obtain ⟨⟨t, p⟩, hq, rfl⟩ := Finset.mem_image.1 hg
      rw [Finset.mem_product, List.mem_toFinset] at hq
      exact H.mul_mem (hT t hq.1) (hsH p hq.2)
    · intro x hx g hg
      obtain ⟨⟨t, p⟩, hq, rfl⟩ := Finset.mem_image.1 hg
      rw [Finset.mem_product, List.mem_toFinset] at hq
      rw [hmul, hsfix x (fun l hl => hx l (List.mem_cons_of_mem _ hl)) p hq.2,
        hx (b, T) List.mem_cons_self t hq.1]

theorem prod_le_card_of_chainOK (act : G → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (hone : ∀ x, act 1 x = x)
    (H : Subgroup G) [Finite H] (L : List (X × List G)) (h : ChainOK act H L) :
    (L.map fun l => l.2.length).prod ≤ Nat.card H := by
  obtain ⟨s, hcard, hsH, -⟩ := exists_finset_of_chainOK act hmul hone H L h
  rw [← hcard]
  have hinj : Function.Injective (fun g : s => (⟨g, hsH g g.2⟩ : H)) :=
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

end CFSG.KC.StabChain
