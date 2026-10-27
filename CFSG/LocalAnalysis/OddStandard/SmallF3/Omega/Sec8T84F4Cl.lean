module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Pr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Le

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_classify_E8 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {A : Subgroup G}
    (hA : A ≤ T) (h8 : IsElemAb2 A 8) :
    A = E ∨ A = F1 ⊔ F2 ∨ A = V1 ⊔ F2 ∨ A = F1 ⊔ V2 := by
  have hAT0 : A ≤ T1 ⊔ T2 := sec8t84_E8_le_T0 D hA h8
  have he : CFSG.Open.IsElemAbelian 2 A := h8.1
  obtain ⟨A1, A2, hA1T1, hA2T2, hA1e, hA2e, hAsub, hAcardle, hcoord, hA1proj, hA2proj⟩ :=
    sec8t84_proj_split D.wr hAT0 he
  have hnoe32 : ∀ B : Subgroup G, B ≤ T1 → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 16 → B = V1 ∨ B = F1 := by
    intro B hBT1 hBe hBcard
    exact D.mod1.only B hBT1 ⟨hBe, by rw [hBcard]; norm_num⟩
  have hA1le16 : Nat.card A1 ≤ 16 :=
    sec8t84_no_e32 (P := T1) (B1 := V1) (B2 := F1) hnoe32 hA1T1 hA1e
  have hmapT1 : A2.map (MulAut.conj t).toMonoidHom ≤ T1 := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa [MulAut.conj_apply] using D.swap2 x (hA2T2 hx)
  have hmape : CFSG.Open.IsElemAbelian 2 (A2.map (MulAut.conj t).toMonoidHom) :=
    hA2e.map (MulAut.conj t).toMonoidHom
  have hcardmap : Nat.card (A2.map (MulAut.conj t).toMonoidHom) = Nat.card A2 :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hA2le16 : Nat.card A2 ≤ 16 := by
    have h := sec8t84_no_e32 (P := T1) (B1 := V1) (B2 := F1) hnoe32 hmapT1 hmape
    rwa [hcardmap] at h
  have hAcard : Nat.card A = 2 ^ 8 := h8.2
  have hAcard256 : Nat.card A = 256 := by rw [hAcard]; norm_num
  have h256 : 256 ≤ Nat.card A1 * Nat.card A2 := hAcard256 ▸ hAcardle
  have hA1card : Nat.card A1 = 16 := by
    by_contra hne
    have hlt : Nat.card A1 < 16 := lt_of_le_of_ne hA1le16 hne
    have hle15 : Nat.card A1 ≤ 15 := by omega
    have hprod : Nat.card A1 * Nat.card A2 ≤ 15 * 16 := Nat.mul_le_mul hle15 hA2le16
    omega
  have hA2card : Nat.card A2 = 16 := by
    have h16 : 256 ≤ 16 * Nat.card A2 := by rw [← hA1card]; exact h256
    omega
  have hA2back : (A2.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = A2 := by
    have hff : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
      ext x
      show t * (t * x * t⁻¹) * t⁻¹ = x
      rw [inv_eq_of_mul_eq_one_right D.t_sq]
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [D.t_sq]; simp
    rw [Subgroup.map_map, hff, Subgroup.map_id]
  have hA2only : A2 = V2 ∨ A2 = F2 := by
    rcases D.mod1.only (A2.map (MulAut.conj t).toMonoidHom) hmapT1
      ⟨hmape, by rw [hcardmap, hA2card]; norm_num⟩ with h | h
    · left
      have h' := congrArg (fun S : Subgroup G => S.map (MulAut.conj t).toMonoidHom) h
      rw [hA2back] at h'
      exact h'.trans D.V2_eq.symm
    · right
      have h' := congrArg (fun S : Subgroup G => S.map (MulAut.conj t).toMonoidHom) h
      rw [hA2back] at h'
      exact h'.trans D.F2_eq.symm
  have hcomm : ∀ a ∈ A1, ∀ b ∈ A2, a * b = b * a :=
    fun a ha b hb => D.comm a (hA1T1 ha) b (hA2T2 hb)
  have hinf : A1 ⊓ A2 = ⊥ := by
    have hle : A1 ⊓ A2 ≤ T1 ⊓ T2 := inf_le_inf hA1T1 hA2T2
    rw [D.inf] at hle
    exact le_bot_iff.mp hle
  have hAsup : A = A1 ⊔ A2 := by
    have hcard : Nat.card ↥(A1 ⊔ A2) = Nat.card A1 * Nat.card A2 := sec124_card_sup hcomm hinf
    have hcard' : Nat.card ↥(A1 ⊔ A2) = 256 := by
      norm_num [hcard, hA1card, hA2card]
    exact Subgroup.eq_of_le_of_card_ge hAsub (by simp [hcard', hAcard256])
  rcases D.mod1.only A1 hA1T1 ⟨hA1e, by rw [hA1card]; norm_num⟩ with hA1V | hA1F
  · rcases hA2only with hA2V | hA2F
    · left
      rw [hAsup, hA1V, hA2V, D.E_eq]
    · right; right; left
      rw [hAsup, hA1V, hA2F]
  · rcases hA2only with hA2V | hA2F
    · right; right; right
      rw [hAsup, hA1F, hA2V]
    · right; left
      rw [hAsup, hA1F, hA2F]

end TData

end CFSG.OddStandard.SmallF3.Omega
