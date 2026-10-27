module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveInversion

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

theorem sec8t84_index_two {G : Type} [Group G] [Finite G] {X H T : Subgroup G} {t : G}
    (ht : t * t = 1) (hHX : H ≤ X) (hnorm : ∀ x ∈ X, ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hXt : H ⊔ zpowers t = X) (htH : t ∉ H) (hT : IsSylow2Of T X) (htT : t ∈ T) :
    IsSylow2Of (T ⊓ H) H ∧ Nat.card T = 2 * Nat.card ↥(T ⊓ H) ∧
      T = zpowers t ⊔ (T ⊓ H) := by
  have htX : t ∈ X := by
    rw [← hXt]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hzX : zpowers t ≤ X := by
    rw [← hXt]
    exact le_sup_right
  have hzn : zpowers t ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx h hh
    exact hnorm x (hzX hx) h hh
  have memX : ∀ b ∈ X, b ∈ H ∨ b * t ∈ H := by
    intro b hb
    have hbs := Subgroup.coe_mul_of_right_le_normalizer_left (N := H) (H := zpowers t) hzn
    have hbset : b ∈ (H : Set G) * (zpowers t : Set G) := by
      rw [← hbs]
      simpa [← hXt] using hb
    obtain ⟨h, hh, s, hs, rfl⟩ := Set.mem_mul.mp hbset
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self_eq_one ht hs with rfl | rfl
    · exact Or.inl (by simpa using hh)
    · exact Or.inr (by rw [mul_assoc, ht, mul_one]; exact hh)
  have hHidx : H.relIndex X = 2 := by
    refine (Subgroup.relIndex_eq_two_iff_exists_notMem_and (H := H) (K := X)).mpr
      ⟨t, htX, htH, ?_⟩
    intro b hb
    rcases memX b hb with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hTHidx : (T ⊓ H).relIndex T = 2 := by
    refine (Subgroup.relIndex_eq_two_iff_exists_notMem_and (H := T ⊓ H) (K := T)).mpr
      ⟨t, htT, fun h => htH h.2, ?_⟩
    intro b hb
    rcases memX b (hT.1 hb) with h | h
    · exact Or.inr ⟨hb, h⟩
    · exact Or.inl ⟨mul_mem hb htT, h⟩
  have hodd : ¬ 2 ∣ (T ⊓ H).relIndex H := by
    have e1 : (T ⊓ H).relIndex H * H.relIndex X = (T ⊓ H).relIndex X :=
      Subgroup.relIndex_mul_relIndex (H := T ⊓ H) (K := H) (L := X) inf_le_right hHX
    have e2 : (T ⊓ H).relIndex T * T.relIndex X = (T ⊓ H).relIndex X :=
      Subgroup.relIndex_mul_relIndex (H := T ⊓ H) (K := T) (L := X) inf_le_left hT.1
    rw [hHidx] at e1
    rw [hTHidx] at e2
    have heq : (T ⊓ H).relIndex H = T.relIndex X :=
      Nat.mul_right_cancel (m := 2) (by norm_num) (by
        rw [mul_comm (T.relIndex X) 2, e1, e2])
    rw [heq]
    exact hT.2.2
  have hcard : Nat.card T = 2 * Nat.card ↥(T ⊓ H) := by
    have h := Subgroup.relIndex_mul_card (H := T ⊓ H) (K := T)
    have hinf : (T ⊓ H) ⊓ T = T ⊓ H := inf_eq_left.mpr inf_le_left
    rw [hinf, hTHidx] at h
    exact h.symm
  have hsup : T ≤ zpowers t ⊔ (T ⊓ H) := by
    intro x hx
    rcases memX x (hT.1 hx) with h | h
    · exact Subgroup.mem_sup_right ⟨hx, h⟩
    · have hmem : (x * t) * t ∈ (T ⊓ H) ⊔ zpowers t :=
        Subgroup.mul_mem_sup (show x * t ∈ T ⊓ H from ⟨mul_mem hx htT, h⟩)
          (Subgroup.mem_zpowers t)
      rw [show (x * t) * t = x by rw [mul_assoc, ht, mul_one], sup_comm] at hmem
      exact hmem
  refine ⟨⟨inf_le_right, IsPGroup.to_inf_left (K := H) hT.2.1, hodd⟩, hcard, ?_⟩
  exact le_antisymm hsup (sup_le (Subgroup.zpowers_le.mpr htT) inf_le_left)

end CFSG.OddStandard.SmallF3.Omega
