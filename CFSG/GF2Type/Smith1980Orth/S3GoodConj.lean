module

public import CFSG.GF2Type.Smith1980Orth.S3Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

theorem conj_mem_Cbar_of_mem_M1 {y c : S.O} (hy : y ∈ M1) (hc : c ∈ D.Cbar) :
    y * c * y⁻¹ ∈ D.Cbar := by
  obtain ⟨s, hs, c', hc', rfl⟩ := D.exists_mul_Cbar_of_mem_M1 hy
  have hcc : c' * c * c'⁻¹ ∈ D.Cbar := mul_mem (mul_mem hc' hc) (inv_mem hc')
  have hcomm : s * (c' * c * c'⁻¹) = (c' * c * c'⁻¹) * s := mem_centralizer_iff.mp hcc.2 s hs
  have e : s * c' * c * (s * c')⁻¹ = c' * c * c'⁻¹ := by
    calc s * c' * c * (s * c')⁻¹ = s * (c' * c * c'⁻¹) * s⁻¹ := by group
      _ = c' * c * c'⁻¹ := by rw [hcomm]; group
  rw [e]
  exact hcc

theorem t_notMem_Obar : D.t ∉ D.Obar := by
  intro h
  have h3 : D.t ^ 3 = 1 := S13.pow_three_eq_one D.card_Obar h
  have h2 : D.t ^ 2 = 1 := by rw [pow_two]; exact D.t_mul_t
  apply D.good.ht1
  calc D.t = D.t ^ 3 * (D.t ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem notMem_Obar_of_isTInv {s : S.O} (hs : D.IsTInv s) : s ∉ D.Obar := by
  have hk : D.k ∈ D.Obar := D.k_mem_Obar
  rcases hs with rfl | rfl | rfl
  · exact D.t_notMem_Obar
  · intro h
    apply D.t_notMem_Obar
    have := mul_mem (inv_mem hk) h
    rwa [inv_mul_cancel_left] at this
  · intro h
    apply D.t_notMem_Obar
    have := mul_mem (inv_mem (mul_mem hk hk)) h
    rwa [show (D.k * D.k)⁻¹ * (D.k * D.k * D.t) = D.t by group] at this

theorem isTInv_iff {s : S.O} : D.IsTInv s ↔ s ∈ D.Obar ⊔ zpowers D.t ∧ s ∉ D.Obar := by
  constructor
  · intro hs
    exact ⟨D.mem_sup_of_isTInv hs, D.notMem_Obar_of_isTInv hs⟩
  · rintro ⟨h1, h2⟩
    rcases D.mem_Obar_sup_cases h1 with h | h | h | h
    · exact absurd h h2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by rw [h, pow_two]))

theorem isTInv_conj_of_mem_M1 {s y : S.O} (hs : D.IsTInv s) (hy : y ∈ M1) :
    D.IsTInv (y * s * y⁻¹) := by
  obtain ⟨s', hs', c, hc, rfl⟩ := D.exists_mul_Cbar_of_mem_M1 hy
  have hsc : s * c = c * s := D.comm_of_isTInv_of_mem_Cbar hs hc
  have e : s' * c * s * (s' * c)⁻¹ = s' * s * s'⁻¹ := by
    calc s' * c * s * (s' * c)⁻¹ = s' * (c * s) * c⁻¹ * s'⁻¹ := by group
      _ = s' * (s * c) * c⁻¹ * s'⁻¹ := by rw [hsc]
      _ = s' * s * s'⁻¹ := by group
  rw [e, D.isTInv_iff]
  refine ⟨mul_mem (mul_mem hs' (D.mem_sup_of_isTInv hs)) (inv_mem hs'), fun h => ?_⟩
  apply D.notMem_Obar_of_isTInv hs
  have hs'M1 : s' ∈ M1 := by
    refine sup_le D.Obar_le_M1 (zpowers_le.mpr D.t_mem_M1) hs'
  have := D.conj_mem_Obar_of_mem_M1 (inv_mem hs'M1) h
  rwa [show s'⁻¹ * (s' * s * s'⁻¹) * s'⁻¹⁻¹ = s by group] at this

theorem isUInv_conj_of_mem_M1 {s y : S.O} (hs : D.IsUInv s) (hy : y ∈ M1) :
    D.IsUInv (y * s * y⁻¹) := by
  obtain ⟨hsC, hsA⟩ := hs
  obtain ⟨s', hs', c, hc, rfl⟩ := D.exists_mul_Cbar_of_mem_M1 hy
  have hcc : c * s * c⁻¹ ∈ D.Cbar := mul_mem (mul_mem hc hsC) (inv_mem hc)
  have hcomm : s' * (c * s * c⁻¹) = (c * s * c⁻¹) * s' := mem_centralizer_iff.mp hcc.2 s' hs'
  have e : s' * c * s * (s' * c)⁻¹ = c * s * c⁻¹ := by
    calc s' * c * s * (s' * c)⁻¹ = s' * (c * s * c⁻¹) * s'⁻¹ := by group
      _ = c * s * c⁻¹ := by rw [hcomm]; group
  refine ⟨by rw [e]; exact hcc, ?_⟩
  have h1 : (⟨s' * c * s * (s' * c)⁻¹, by rw [e]; exact hcc⟩ : D.Cbar) =
      (⟨c, hc⟩ : D.Cbar) * ⟨s, hsC⟩ * (⟨c, hc⟩ : D.Cbar)⁻¹ :=
    Subtype.ext e
  rw [h1, map_mul, map_mul, map_inv]
  exact isTypeA_conj hsA
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => D.QV_resC ⟨c, hc⟩ v)

section Full

variable (D : S2Data S)

theorem conj_mem_Cbar {y c : S.O} (hy : y ∈ S.Mbar) (hc : c ∈ D.Cbar) :
    y * c * y⁻¹ ∈ D.Cbar :=
  D.conj_mem_Cbar_of_mem_M1 hy hc

theorem isTInv_conj {s y : S.O} (hs : D.IsTInv s) (hy : y ∈ S.Mbar) :
    D.IsTInv (y * s * y⁻¹) :=
  D.isTInv_conj_of_mem_M1 hs hy

theorem isUInv_conj {s y : S.O} (hs : D.IsUInv s) (hy : y ∈ S.Mbar) :
    D.IsUInv (y * s * y⁻¹) :=
  D.isUInv_conj_of_mem_M1 hs hy

end Full

end S2Data

end CFSG.GF2Type.Smith1980Orth
