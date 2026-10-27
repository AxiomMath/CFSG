module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem transfer8 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ (Y : Subgroup G) (v : G), Y ≤ S → Y.relIndex S = 2 → v ∈ S → v ∉ Y → v * v = 1 →
      ∃ g : G, g⁻¹ * v * g ∈ Y ∧ ∀ x ∈ S, x * v = v * x → g⁻¹ * x * g ∈ S := by
  intro Y v hYS hY2 hvS hvY hv2
  have hM := hs.m4 hII
  have hSsyl : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In S ⊤ := hM.S_top
  have hsimple := hs.fused.std.simple
  have hY1 : Y ≠ S := by
    intro e
    rw [e] at hY2
    simp at hY2
  have hYn : ∀ s ∈ S, ∀ q ∈ Y, s * q * s⁻¹ ∈ Y := fun s hs q hq =>
    Basic.conj_mem_of_relIndex_two hY2 hs hq hYS
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Y := by
    refine ⟨v, hvS, fun s hs => ?_⟩
    rcases Basic.relIndex_two_pigeon hY2 hvS hs with h1 | h1 | h1
    · exact absurd h1 hvY
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  have hv1 : v ≠ 1 := fun e => hvY (e ▸ Y.one_mem)
  have hvo : orderOf v = 2 := orderOf_eq_prime (by simpa [pow_two] using hv2) hv1
  have hord : ∀ w ∈ S, w ∉ Y → orderOf v ≤ orderOf w := by
    intro w _ hwY
    have hw1 : w ≠ 1 := fun e => hwY (e ▸ Y.one_mem)
    have h1 : orderOf w ≠ 1 := fun e => hw1 (orderOf_eq_one_iff.1 e)
    have h2 := orderOf_pos w
    rw [hvo]; omega
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * v * g = y) →
      CFSG.GH74.GLS.Stage1.Thm6.Sec12.IsExtremal S y → y ∈ Y ∨ v⁻¹ * y ∈ Y := by
    intro y hyS _ _
    rcases Basic.relIndex_two_pigeon hY2 hvS hyS with h1 | h1 | h1
    · exact absurd h1 hvY
    · exact Or.inl h1
    · exact Or.inr h1
  rcases CFSG.GH74.GLS.Stage1.Thm6.Sec12.ig_15_15 G S Y v hSsyl hYS hYn hY1 hcyc hvS hvY hord hext
    with ⟨N, hN, hcycN, -, hvN⟩ | ⟨g, hgY, -, hgC⟩
  · exfalso
    rcases hsimple.1.eq_bot_or_eq_top_of_normal N with e | e
    · subst e
      obtain ⟨a, b, hab⟩ := hsimple.2.1
      have hcycG : IsCyclic G := isCyclic_of_surjective
        (QuotientGroup.quotientBot (G := G)).toMonoidHom
        (QuotientGroup.quotientBot (G := G)).surjective
      have hc : IsMulCommutative G := IsCyclic.isMulCommutative
      exact hab (hc.is_comm.comm a b)
    · exact hvN (e ▸ Subgroup.mem_top v)
  · refine ⟨g, hgY, fun x hxS hxv => ?_⟩
    exact (hgC x ⟨hxS, Subgroup.mem_centralizer_singleton_iff.2 hxv⟩).1

theorem orderOf_conj' (c w : G) : orderOf (c * w * c⁻¹) = orderOf w := by
  have h1 := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective w
  have e : (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ := by simp
  rw [e] at h1
  exact h1

theorem one_class (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP2 : (Pz S z).relIndex S = 2) :
    ∀ v : G, orderOf v = 2 → IsConj z v := by
  have hM := hs.m4 hII
  obtain ⟨u', hu'P, hu'c, hu'z⟩ := hs.fused.fused
  have hord' : orderOf u' = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hu'c
    rw [← hc, orderOf_conj', hs.fused.std.orderOf_z]
  have hL := lemma_4_2 hII h31 G z S K₁ K₂ hs.fused.std
    ⟨u', Subgroup.mem_sup_left hu'P, hord', hu'c, hu'z⟩
  have hPz : ∀ w ∈ Pz S z, orderOf w = 2 → IsConj z w := hL.1
  have hPzS : Pz S z ≤ S := inf_le_left
  have hS : ∀ w ∈ S, orderOf w = 2 → IsConj z w := by
    intro w hwS hw2
    by_cases hwP : w ∈ Pz S z
    · exact hPz w hwP hw2
    · have hwsq : w * w = 1 := by
        have := pow_orderOf_eq_one w
        rwa [hw2, pow_two] at this
      obtain ⟨g, hg, -⟩ := hs.transfer8 hII (Pz S z) w hPzS hP2 hwS hwP hwsq
      have hgo : orderOf (g⁻¹ * w * g) = 2 := by
        have := orderOf_conj' g⁻¹ w
        rw [inv_inv] at this
        rw [this, hw2]
      have h1 := hPz _ hg hgo
      exact h1.trans (isConj_iff.2 ⟨g, by group⟩)
  intro v hv
  have hpg : IsPGroup 2 ↥(zpowers v) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hv, pow_one]⟩
  obtain ⟨P, hP, hvP⟩ := M.exists_syl2In_ge hpg (le_top : zpowers v ≤ ⊤)
  obtain ⟨c, -, hc⟩ := hM.S_top.exists_conj hP
  have hvP' : v ∈ P := hvP (Subgroup.mem_zpowers v)
  rw [hc, M.mem_cj] at hvP'
  have hw := hS _ hvP' (by rw [orderOf_conj', hv])
  exact hw.trans (isConj_iff.2 ⟨c⁻¹, by group⟩)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
