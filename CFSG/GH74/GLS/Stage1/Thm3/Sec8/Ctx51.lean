module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx24

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Basic

theorem W_eq_M {G : Type*} [Group G] [Finite G] {Q W M : Subgroup G} {z : G} (hWQ : W ≤ Q)
    (hWc : IsCyclic ↥W) (hW8 : Nat.card ↥W = 8) (hM8 : Nat.card ↥M = 8)
    (hout : ∀ x ∈ Q, x ∉ M → x * x = z) (hz2 : z * z = 1) : W = M := by
  obtain ⟨g, hg⟩ := hWc.exists_generator
  have hgo : orderOf (g : G) = 8 := by
    have h1 : Nat.card ↥(zpowers g) = orderOf g := Nat.card_zpowers g
    have h2 : zpowers g = ⊤ := Subgroup.eq_top_iff' _ |>.2 hg
    rw [h2, Subgroup.card_top, hW8] at h1
    rw [Subgroup.orderOf_coe g]
    exact h1.symm
  by_cases hgM : (g : G) ∈ M
  · have hle : W ≤ M := by
      intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      have : x = (g : G) ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      rw [this]
      exact Subgroup.zpow_mem _ hgM k
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  · exfalso
    have h1 : (g : G) * (g : G) = z := hout g (hWQ g.2) hgM
    have h4 : (g : G) ^ 4 = 1 := by
      have e : (g : G) ^ 4 = ((g : G) * (g : G)) * ((g : G) * (g : G)) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, h1]
      exact hz2
    have := orderOf_dvd_of_pow_eq_one h4
    rw [hgo] at this
    omega

theorem card_le_two_mul_inf {G : Type*} [Group G] [Finite G] {C S S₁ : Subgroup G} (hCS : C ≤ S)
    (h2 : S₁.relIndex S ≤ 2) : Nat.card ↥C ≤ 2 * Nat.card ↥(S₁ ⊓ C) := by
  have h1 : S₁.relIndex C ≤ S₁.relIndex S :=
    Subgroup.relIndex_le_of_le_right hCS (relIndex_ne_zero' _ _)
  have h3 := card_mul_relIndex_of_le (A := S₁ ⊓ C) (B := C) inf_le_right
  rw [Subgroup.inf_relIndex_right] at h3
  have h4 : Nat.card ↥(S₁ ⊓ C) * S₁.relIndex C ≤ Nat.card ↥(S₁ ⊓ C) * 2 :=
    Nat.mul_le_mul_left _ (h1.trans h2)
  omega

end Basic

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem Q_conj_mem (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {g : G} (hg : g ∈ S1 S K₁) {y : G} (hy : y ∈ Qof S K) :
    g * y * g⁻¹ ∈ Qof S K := by
  obtain ⟨hN, -⟩ := hs.nc_quot hK
  have hQS1 : Qof S K ≤ S1 S K₁ := by
    rcases hK with rfl | rfl
    · exact hs.Q₁_le_S1
    · exact hs.Q₂_le_S1 hII
  have := hN.conj_mem ⟨y, hQS1 hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨g, hg⟩
  have h2 := Subgroup.mem_subgroupOf.1 this
  simpa using h2

theorem case3 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS256 : Nat.card ↥S = 2 ^ 8) :
    Nat.card ↥(Qof S K₁) = 16 ∧ Nat.card ↥(Qof S K₂) = 16 ∧ S1 S K₁ = Qof S K₁ ⊔ Qof S K₂ ∧
      (S1 S K₁).relIndex S = 2 := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hP₂ : Nat.card ↥(Pof S K₂) = 8 := by omega
  obtain ⟨-, hcard⟩ := hs.card_S1 hII
  have hP := hs.card_P hII
  have hPz : Nat.card ↥(Pz S z) = 32 := by
    rw [hP8, hP₂] at hP
    omega
  have hS1 : Nat.card ↥(S1 S K₁) = 64 * e := by rw [hcard, hri, hPz]; ring
  have he2 : e = 2 := by
    rcases hs.card_S_of with ⟨-, hc⟩ | ⟨-, hc⟩
    · rw [hS256, hS1] at hc
      omega
    · rw [hS256, hS1] at hc
      omega
  subst he2
  have hSne : S ≠ S1 S K₁ := by
    intro h'
    have : Nat.card ↥S = Nat.card ↥(S1 S K₁) := by rw [← h']
    rw [hS256, hS1] at this
    omega
  have h4 : (Pz S z).relIndex (S1 S K₁) = 4 := by omega
  refine ⟨by rw [hq1, hP₂], by rw [hq2, hP8], (hs.fused.p66.2.2.2 h4).2, hs.relIndex_S1_S hSne⟩

theorem w_mem_S1 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hV4 : Nat.card ↥(Vof S K₁ W₂) = 4) {w : G} (hwS : w ∈ S)
    (hinv : ∀ x ∈ Vof S K₁ W₂, w * x * w⁻¹ = x⁻¹) : w ∈ S1 S K₁ := by
  by_contra hn
  obtain ⟨h1, -⟩ := hs.swap_of_not_mem hII hwS hn
  have hle : Vof S K₁ W₂ ≤ zpowers z := by
    rw [← hs.P_inf hII]
    intro x hx
    have hxP : x ∈ Pof S K₁ := hx.2
    have hxinv : x⁻¹ ∈ Pof S K₁ := inv_mem hxP
    have hwx : w * x * w⁻¹ ∈ K₁ := by
      rw [hinv x hx]
      exact hxinv.2
    have hxK₂ : x ∈ K₂ := by
      have hx' : x ∈ conjugate K₁ w := mem_conjugate_iff.2 hwx
      rw [h1] at hx'
      exact hx'
    exact ⟨hxP, ⟨hxP.1, hxK₂⟩⟩
  have hz1 : z ≠ 1 := hs.z_ne
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs.z_sq) hz1
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hzo, hV4] at this
  omega

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
