module

public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.GH74.Uniqueness.Section12Transport
public import CFSG.GH74.Uniqueness.Section12Center
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.exists_torus
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n e : ℕ}
    (hB : BenderSub Z M (cenHull Z c.u) n 1 e) :
    2 ≤ n ∧ ∃ A : Subgroup X, A ≤ c.D ⊓ cenHull Z c.u ∧ Nat.card A = 2 ^ n - 1 ∧
      ∀ a ∈ A, c.t * a * c.t⁻¹ = a⁻¹ := by
  set F := cenHull Z c.u with hF
  have hodd : Odd (Nat.card (center ↥F)) := by
    have h1 := odd_card_pPrimeCoreIn F
    rwa [hB.core, card_map_of_injective F.subtype_injective] at h1
  have hgen : closure {x : ↥F | x * x = 1} = ⊤ := by
    have hle : F ≤ (closure {x : ↥F | x * x = 1}).map F.subtype := by
      have h1 : zHull Z F ≤ (closure {x : ↥F | x * x = 1}).map F.subtype := by
        refine (closure_le _).mpr fun y hy => ?_
        refine ⟨⟨y, hy.2⟩, subset_closure ?_, rfl⟩
        exact Subtype.ext (S.invariant.mul_self_eq_one hy.1)
      rwa [hB.zhull] at h1
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcen : center ↥F = ⊥ := center_eq_bot_of_benderType (Or.inl rfl) hgen hodd hB.bender
  have hBF : Bender.BenderType ↥F n 1 e := benderType_of_center_eq_bot hB.bender hcen
  obtain ⟨T, hT⟩ := hB.borel
  obtain ⟨Q, hQ⟩ := exists_sylow_normalizer_eq_of_center_eq_bot hcen hT
  have htF : c.t ∈ F := subset_closure ⟨c.ht, c.ht_B⟩
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have ht'2 : (⟨c.t, htF⟩ : ↥F) * ⟨c.t, htF⟩ = 1 := Subtype.ext ht2
  have ht'Q : (⟨c.t, htF⟩ : ↥F) ∉ Bender.borel (Q : Subgroup ↥F) := by
    intro h
    change (⟨c.t, htF⟩ : ↥F) ∈ normalizer ((Q : Subgroup ↥F) : Set ↥F) at h
    rw [← hQ] at h
    exact c.htM (mem_inf.mp (mem_subgroupOf.mp h)).1
  have hc := hBF.benderCore Q ht'2 ht'Q
  have L := hBF.lemma_3_2 Q ht'2 ht'Q
  refine ⟨hBF.two_le.2, (⁅Bender.cartan (Q : Subgroup ↥F) ⟨c.t, htF⟩,
    zpowers (⟨c.t, htF⟩ : ↥F)⁆).map F.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxc := (hc.mem_commutator_cartan_iff.mp hx).1
    have hmem : (x : X) ∈ (Bender.cartan (Q : Subgroup ↥F) ⟨c.t, htF⟩).map F.subtype :=
      ⟨x, hxc, rfl⟩
    rw [map_subtype_cartan hQ htF] at hmem
    exact mem_inf.mpr ⟨(mem_inf.mp hmem).1, (mem_inf.mp hmem).2⟩
  · rw [card_map_of_injective F.subtype_injective]
    exact L.card_commutator
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := congrArg Subtype.val (L.inverted x hx)
    rw [hti]
    exact h1

end CFSG.GH74.Uniqueness
