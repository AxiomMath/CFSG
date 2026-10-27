module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Cfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Q16

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

theorem quat_iso_of_sylow {S K : Subgroup G} (hP : M.Syl2In (S ⊓ K) K)
    (hK : IsDoubleCoverOfAlt (Hat K) 7) : Nonempty (↥(S ⊓ K) ≃* QuaternionGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, z₀, hcov, -⟩ := CFSG.GH74.KGroups.TwoA7.exists_cover hK
  have hSyl := isSylow2In_hatImg (K := K) (S := S ⊓ K) hP
  let P : Sylow 2 (Hat K) := hSyl.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSyl.2.2)
  have hPeq : (P : Subgroup (Hat K)) = hatImg K (S ⊓ K) := rfl
  obtain ⟨e⟩ := CFSG.GH74.KGroups.TwoA7.sylow_quaternion hcov P
  have hSK : S ⊓ K ≤ K := inf_le_right
  let f : ↥(S ⊓ K) →* ↥(P : Subgroup (Hat K)) :=
    ((hatMk K).comp (Subgroup.inclusion hSK)).codRestrict (P : Subgroup (Hat K)) (fun x => by
      rw [hPeq]
      exact hatMk_mem_hatImg hSK x.2)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : hatMk K ⟨(x : G), hSK x.2⟩ = hatMk K ⟨(y : G), hSK y.2⟩ := congrArg Subtype.val hxy
      exact Subtype.ext (eq_of_hatMk_eq hSK hP.2.1 x.2 y.2 h1)
    · intro y
      have hy : (y : Hat K) ∈ hatImg K (S ⊓ K) := by rw [← hPeq]; exact y.2
      obtain ⟨a, haS, ha⟩ := mem_hatImg.mp hy
      exact ⟨⟨(a : G), haS⟩, Subtype.ext ha⟩
  exact ⟨(MulEquiv.ofBijective f hf).trans e⟩

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem P₁_syl (hII : II4_4_4_center) : M.Syl2In (Pof S K₁) K₁ := by
  have hM := h.m4 hII
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  rw [← e1]
  exact hM.Pi_syl (Or.inl rfl)

theorem P₁_quat (hII : II4_4_4_center) :
    Nonempty (↥(Pof S K₁) ≃* QuaternionGroup 4) :=
  quat_iso_of_sylow (h.P₁_syl hII) h.d₁

theorem P₁_card (hII : II4_4_4_center) : Nat.card ↥(Pof S K₁) = 16 := by
  obtain ⟨e⟩ := h.P₁_quat hII
  exact q16_card e

theorem exists_a₁ (hII : II4_4_4_center) :
    ∃ a b : G, a ∈ Pof S K₁ ∧ b ∈ Pof S K₁ ∧ orderOf a = 8 ∧
      (∀ y ∈ Pof S K₁, y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a⁻¹) ∧
      (∀ y ∈ Pof S K₁, y * a = a * y → y ∈ zpowers a) ∧ b * a * b⁻¹ = a⁻¹ ∧ b * b = a ^ 4 := by
  obtain ⟨e⟩ := h.P₁_quat hII
  obtain ⟨x, hx⟩ := q16_exists_order_eight e
  obtain ⟨b, hb1, hb2⟩ := q16_exists_inv e hx
  refine ⟨(x : G), (b : G), x.2, b.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hx, Subgroup.orderOf_coe]
  · intro y hy
    rcases q16_conj_gen e hx ⟨y, hy⟩ with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1
  · intro y hy hcomm
    have h1 : (⟨y, hy⟩ : ↥(Pof S K₁)) * x = x * ⟨y, hy⟩ := Subtype.ext hcomm
    have h2 := q16_comm_mem_zpowers e hx h1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h2
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
  · exact congrArg Subtype.val hb1
  · exact congrArg Subtype.val hb2

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
