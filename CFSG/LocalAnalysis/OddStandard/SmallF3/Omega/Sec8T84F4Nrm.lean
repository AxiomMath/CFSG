module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Pr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Le

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_normal_E8 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {A : Subgroup G}
    (hA : A ≤ T) (h8 : IsElemAb2 A 8) (hn : (A.subgroupOf T).Normal) :
    A = E ∨ A = F1 ⊔ F2 := by
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
  have hA2le16 : Nat.card A2 ≤ 16 := by
    have hmapT1 : A2.map (MulAut.conj t).toMonoidHom ≤ T1 := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa [MulAut.conj_apply] using D.swap2 x (hA2T2 hx)
    have hmape : CFSG.Open.IsElemAbelian 2 (A2.map (MulAut.conj t).toMonoidHom) :=
      hA2e.map (MulAut.conj t).toMonoidHom
    have hcardmap : Nat.card (A2.map (MulAut.conj t).toMonoidHom) = Nat.card A2 :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
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
  have htT : t ∈ T := by
    rw [D.T_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right D.t_sq
  have hconjA : ∀ x ∈ A, t * x * t⁻¹ ∈ A := by
    intro x hxA
    have hxT : x ∈ T := hA hxA
    have hxM : (⟨x, hxT⟩ : ↥T) ∈ A.subgroupOf T := Subgroup.mem_subgroupOf.mpr hxA
    have h := hn.conj_mem (⟨x, hxT⟩ : ↥T) hxM (⟨t, htT⟩ : ↥T)
    simpa [Subgroup.mem_subgroupOf] using h
  have hA2eq : A2 = A1.map (MulAut.conj t).toMonoidHom := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map]
      obtain ⟨x, hxT1, hxyA⟩ := hA2proj y hy
      have hyT2 : y ∈ T2 := hA2T2 hy
      have hzT1 : t * y * t⁻¹ ∈ T1 := D.swap2 y hyT2
      have hwT2 : t * x * t⁻¹ ∈ T2 := D.swap1 x hxT1
      have hconj : t * (x * y) * t⁻¹ ∈ A := hconjA (x * y) hxyA
      have heq : t * (x * y) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹) := by
        rw [D.comm x hxT1 y hyT2]
        group
      rw [heq] at hconj
      have hzA1 : t * y * t⁻¹ ∈ A1 :=
        (hcoord (t * y * t⁻¹) hzT1 (t * x * t⁻¹) hwT2 hconj).1
      refine ⟨t * y * t⁻¹, hzA1, ?_⟩
      change t * (t * y * t⁻¹) * t⁻¹ = y
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
        _ = y := by rw [D.t_sq, htinv, D.t_sq]; simp
    · rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hxA1, rfl⟩ := hy
      obtain ⟨y', hy'T2, hxy'A⟩ := hA1proj x hxA1
      have hxT2 : t * x * t⁻¹ ∈ T2 := D.swap1 x (hA1T1 hxA1)
      have hy'T1 : t * y' * t⁻¹ ∈ T1 := D.swap2 y' hy'T2
      have hconj : t * (x * y') * t⁻¹ ∈ A := hconjA (x * y') hxy'A
      have heq : t * (x * y') * t⁻¹ = (t * y' * t⁻¹) * (t * x * t⁻¹) := by
        rw [D.comm x (hA1T1 hxA1) y' hy'T2]
        group
      rw [heq] at hconj
      have hxA2 : t * x * t⁻¹ ∈ A2 :=
        (hcoord (t * y' * t⁻¹) hy'T1 (t * x * t⁻¹) hxT2 hconj).2
      simpa [MulAut.conj_apply] using hxA2
  have hA2card : Nat.card A2 = 16 := by
    rw [hA2eq, Subgroup.card_map_of_injective (MulAut.conj t).injective, hA1card]
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
  · left
    have hA2V : A2 = V2 := by rw [hA2eq, hA1V, D.V2_eq]
    rw [hAsup, hA1V, hA2V, D.E_eq]
  · right
    have hA2F : A2 = F2 := by rw [hA2eq, hA1F, D.F2_eq]
    rw [hAsup, hA1F, hA2F]

end TData

end CFSG.OddStandard.SmallF3.Omega
