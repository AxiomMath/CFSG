module

public import CFSG.GH74.GLS.SP.Local.SPLCtC3

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Final

@[expose] def mkD2 {G : Type} [Group G] (D₁ : SPLNot1 G) (x : G) : SPLNot2 G :=
  { toSPLNot1 := D₁, A := D₁.Act, I := D₁.Ict, x := x }

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G} {T T₀ T₁ : Subgroup G} {y : G}

theorem ct_J_eq (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hK2 : SPLCenIAt D)
    (hT : SPLCtT D T T₀ T₁ y) {x : G} (hYgen : zpowers x ⊔ zpowers D.z = T₀ ⊔ zpowers y)
    (hxt : x ^ (2 ^ (D.n - 2)) = D.t) (hT₀eq : T₀ = zpowers (x ^ 2) ⊔ zpowers D.z) :
    D.Ct = D.Ict ⊔ D.Act ⊔ D.F₀ ⊔ zpowers x ⊔ zpowers D.z := by
  have hxJ : x ∈ D.Ict ⊔ D.Act ⊔ D.F₀ ⊔ zpowers x ⊔ zpowers D.z :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers x))
  have hzJ : D.z ∈ D.Ict ⊔ D.Act ⊔ D.F₀ ⊔ zpowers x ⊔ zpowers D.z :=
    Subgroup.mem_sup_right (mem_zpowers D.z)
  set J : Subgroup G := D.Ict ⊔ D.Act ⊔ D.F₀ ⊔ zpowers x ⊔ zpowers D.z with hJ
  have hIJ : D.Ict ≤ J := fun h hh =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hh)))
  have hAJ : D.Act ≤ J := fun h hh =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hh)))
  have hF₀J : D.F₀ ≤ J := fun h hh =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hh))
  have hT₀J : T₀ ≤ J := by
    rw [hT₀eq]
    exact sup_le (zpowers_le.mpr (J.pow_mem hxJ 2)) (zpowers_le.mpr hzJ)
  have hyJ : y ∈ J := by
    have : y ∈ T₀ ⊔ zpowers y := Subgroup.mem_sup_right (mem_zpowers y)
    rw [← hYgen] at this
    exact (sup_le (zpowers_le.mpr hxJ) (zpowers_le.mpr hzJ) : zpowers x ⊔ zpowers D.z ≤ J) this
  have htJ : D.t ∈ J := by
    rw [← hxt]; exact J.pow_mem hxJ _
  apply le_antisymm
  · intro c hc
    obtain ⟨a, ha, s, hsT, c₁, hc₁, hcdec⟩ := ct_decomp D hs hA hK2 hT c hc
    have hsJ : s ∈ J := by
      have hTeq : T = (T₀ ⊔ T₁) ⊔ zpowers y := hT.T_eq
      have : T ≤ J := by
        rw [hTeq]
        exact sup_le (sup_le hT₀J (hT.T₁_eq ▸ inf_le_right |>.trans hIJ)) (zpowers_le.mpr hyJ)
      exact this hsT
    have hc₁J : c₁ ∈ J := by
      have hc₁' : c₁ ∈ (zpowers D.z ⊔ zpowers D.t) ⊔ (D.Ict ⊔ D.F₀) := by
        rw [← CCt_eq D hs]; exact hc₁
      exact (sup_le (sup_le (zpowers_le.mpr hzJ) (zpowers_le.mpr htJ)) (sup_le hIJ hF₀J) :
        (zpowers D.z ⊔ zpowers D.t) ⊔ (D.Ict ⊔ D.F₀) ≤ J) hc₁'
    rw [hcdec]
    exact J.mul_mem (J.mul_mem (hAJ ha) hsJ) hc₁J
  · refine sup_le (sup_le (sup_le (sup_le (Ict_le_Ct D hs) (Act_le_Ct D)) (fun f hf => hf.2)) ?_) ?_
    · rw [zpowers_le]
      exact hT.T_le (sup_le (T₀_le_T D hT) (zpowers_le.mpr hT.y_mem)
        (hYgen ▸ (Subgroup.mem_sup_left (mem_zpowers x) : x ∈ zpowers x ⊔ zpowers D.z)))
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)

theorem dihedral_conj_I (hs : SPLSetup D.toSPLNot0) {b x : G} (hb : b ∈ D.Ict) {m : ℕ}
    (hY : IVK.IsDihedralOrder ↥(zpowers x ⊔ zpowers D.z) m) :
    IVK.IsDihedralOrder ↥(zpowers (b * x * b⁻¹) ⊔ zpowers D.z) m := by
  have hzb : D.z * b = b * D.z := z_central_in_K D hs (mem_zpowers D.z) b (Ict_le_K D hs hb)
  have hbz : b * D.z * b⁻¹ = D.z := by
    calc b * D.z * b⁻¹ = D.z * b * b⁻¹ := by rw [← hzb]
      _ = D.z := by group
  have hmap : (zpowers x ⊔ zpowers D.z).map (MulAut.conj b).toMonoidHom =
      zpowers (b * x * b⁻¹) ⊔ zpowers D.z := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hbz]
  rw [← hmap]
  exact CtW.isDihedralOrder_of_mulEquiv
    (Subgroup.equivMapOfInjective _ (MulAut.conj b).toMonoidHom (MulAut.conj b).injective) hY

end Final

end CFSG.GH74.GLS.SP.Local
