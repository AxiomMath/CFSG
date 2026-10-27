module

public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter
open scoped commutatorElement

section RingAut

variable (F : Type) [Field F] [Finite F]

noncomputable def ringAutEquivAlgEquiv (p : ℕ) [Algebra (ZMod p) F] :
    (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : (σ.toRingHom.comp (algebraMap (ZMod p) F) : ZMod p →+* F) =
        algebraMap (ZMod p) F := RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  invFun σ := σ.toRingEquiv
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

theorem ringAut_isCyclic : IsCyclic (F ≃+* F) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let : Algebra (ZMod p) F := ZMod.algebra F p
  exact (ringAutEquivAlgEquiv F p).isCyclic.mpr inferInstance

theorem card_ringAut (p n : ℕ) (hp : p.Prime) (hcard : Nat.card F = p ^ n) :
    Nat.card (F ≃+* F) = n := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have hFcard : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have : CharP F p := charP_of_card_eq_prime_pow hFcard
  let : Algebra (ZMod p) F := ZMod.algebra F p
  rw [Nat.card_congr (ringAutEquivAlgEquiv F p).toEquiv, IsGalois.card_aut_eq_finrank]
  have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
  rw [ZMod.card, hFcard] at h1
  exact (Nat.pow_right_injective hp.two_le h1).symm

end RingAut

theorem ivk_1_2b : IVK_1_2b := by
  intro F _ _ hF K _ e
  have := Finite.of_equiv _ (e.toEquiv.symm)
  exact card_eq_of_L2Field e hF

theorem isCyclic_fieldAutSub {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* L2 F) : IsCyclic ↥(fieldAutSub e) :=
  ((MonoidHom.ofInjective (fieldAutHom_injective e)).symm).isCyclic.mpr (ringAut_isCyclic F)

theorem ivk_1_2a_struct : IVK_1_2a_struct := by
  intro F _ _ hF K _ _ e N
  have hsup := innAut_sup_zpowers_eq e hF N.t_mem_diag N.t_not_mem_inn
  refine ⟨?_, isCyclic_fieldAutSub e, ?_, ?_⟩
  · rw [hsup]
    exact innDiagSub_sup_fieldAutSub e
  · rw [hsup]
    exact innDiagSub_inf_fieldAutSub e
  · intro x _ y hy
    rw [hsup] at hy
    have hNΔ := innDiagSub_normal e
    have hz : x * y * x⁻¹ ∈ innDiagSub e := hNΔ.conj_mem y hy x
    have hidx := innAut_relIndex_two e hF
    unfold Subgroup.relIndex at hidx
    let yΔ : ↥(innDiagSub e) := ⟨y, hy⟩
    let zΔ : ↥(innDiagSub e) := ⟨x * y * x⁻¹, hz⟩
    have hmem : zΔ * yΔ⁻¹ ∈ (innAut K).subgroupOf (innDiagSub e) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
      show x * y * x⁻¹ ∈ innAut K ↔ y ∈ innAut K
      constructor
      · intro h
        have := (innAut_normal (K := K)).conj_mem _ h x⁻¹
        simpa [mul_assoc] using this
      · intro h
        exact (innAut_normal (K := K)).conj_mem y h x
    have hcomm : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := by simp [commutatorElement_def]
    rw [hcomm]
    exact hmem

theorem ivk_1_2e : IVK_1_2e := by
  intro F _ _ hF K _ _ e
  have hinj := fieldAutHom_injective e
  have equ : ↥(fieldAutSub e) ≃* (F ≃+* F) := (MonoidHom.ofInjective hinj).symm
  refine ⟨?_, ⟨equ⟩, ?_⟩
  · exact equ.isCyclic.mpr (ringAut_isCyclic F)
  · intro p n hp hcard
    rw [Nat.card_congr equ.toEquiv]
    exact card_ringAut F p n hp hcard

section Sylow

theorem hasDihedralSylowTwo_of_equiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') (h : HasDihedralSylowTwo G) : HasDihedralSylowTwo G' := by
  intro S'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective S'
  obtain ⟨m, hm, ⟨d⟩⟩ := h S
  refine ⟨m, hm, ⟨?_⟩⟩
  have hS : (S : Subgroup G) = (S' : Subgroup G').map e.symm.toMonoidHom := rfl
  exact ((S' : Subgroup G').equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
    ((MulEquiv.subgroupCongr hS.symm).trans d)

theorem sylow_inf_normal_dihedral {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : HasDihedralSylowTwo ↥N) (T : Sylow 2 G) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥((T : Subgroup G) ⊓ N) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal (G := G) (p := 2) T (N := N)
  obtain ⟨m, hm, ⟨d⟩⟩ := hN P
  refine ⟨m, hm, ⟨?_⟩⟩
  have e1 : ↥(((T : Subgroup G) ⊓ N).subgroupOf N) ≃* ↥((T : Subgroup G) ⊓ N) :=
    Subgroup.subgroupOfEquivOfLe inf_le_right
  exact e1.symm.trans ((MulEquiv.subgroupCongr hP.symm).trans d)

end Sylow


section Parts

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

noncomputable def innAutEquiv : innAut K ≃* PSL2 F :=
  (MonoidHom.ofInjective (conj_injective_of_L2 e)).symm.trans (toPSL e)

noncomputable def innDiagEquiv : innDiagSub e ≃* PGL2 F :=
  (MonoidHom.ofInjective (innDiagHom_injective e)).symm

include e in
theorem dihedral_of_sylow_inf_innAut (h : L2Field F) (T : Sylow 2 (MulAut K)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥((T : Subgroup (MulAut K)) ⊓ innAut K) ≃* DihedralGroup (2 ^ m)) := by
  have hdih : HasDihedralSylowTwo ↥(innAut K) :=
    hasDihedralSylowTwo_of_equiv (innAutEquiv e).symm
      (psl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower_of_L2Field h))
  exact sylow_inf_normal_dihedral (innAut K) hdih T

theorem dihedral_of_sylow_inf_innDiag (h : L2Field F) (T : Sylow 2 (MulAut K)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥((T : Subgroup (MulAut K)) ⊓ innDiagSub e) ≃* DihedralGroup (2 ^ m)) := by
  have := innDiagSub_normal e
  have : Finite (PGL2 F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F)
      Matrix.ProjGenLinGroup.mk_surjective
  have hdih : HasDihedralSylowTwo ↥(innDiagSub e) :=
    hasDihedralSylowTwo_of_equiv (innDiagEquiv e).symm
      (pgl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower_of_L2Field h))
  exact sylow_inf_normal_dihedral (innDiagSub e) hdih T

theorem isDihedralTwoGroup_of_equiv {Y : Type} [Group Y] {m : ℕ} (hm : 1 ≤ m)
    (d : Y ≃* DihedralGroup (2 ^ m)) : IsDihedralTwoGroup Y (m + 1) := by
  refine ⟨by omega, 2 ^ m, by rw [pow_succ]; ring, ?_, ⟨d⟩⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem ivk_1_2c : IVK_1_2c := by
  intro F _ _ hF K _ _ e N
  obtain ⟨m, hm, ⟨d⟩⟩ := dihedral_of_sylow_inf_innAut e hF N.T
  exact ⟨m + 1, isDihedralTwoGroup_of_equiv hm d⟩

theorem P_sup_zpowers_eq_Pt (hF : L2Field F) (N : L2Notation e) :
    N.P ⊔ Subgroup.zpowers N.t = N.Pt := by
  have hidx := innAut_relIndex_two e hF
  unfold Subgroup.relIndex at hidx
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact inf_le_inf_left _ (innAut_le_innDiagSub e)
    · exact (Subgroup.zpowers_le).2 ⟨N.t_mem, N.t_mem_diag⟩
  · rintro x ⟨hxT, hxΔ⟩
    by_cases hx : x ∈ innAut K
    · exact Subgroup.mem_sup_left ⟨hxT, hx⟩
    · have hmem : (⟨x, hxΔ⟩ : ↥(innDiagSub e)) * (⟨N.t, N.t_mem_diag⟩ : ↥(innDiagSub e))⁻¹ ∈
          (innAut K).subgroupOf (innDiagSub e) := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
        exact iff_of_false hx N.t_not_mem_inn
      have hP : x * N.t⁻¹ ∈ N.P := ⟨(N.T : Subgroup (MulAut K)).mul_mem hxT
        ((N.T : Subgroup (MulAut K)).inv_mem N.t_mem), hmem⟩
      have := Subgroup.mul_mem_sup hP (Subgroup.mem_zpowers N.t)
      simpa using this

theorem ivk_1_2d : IVK_1_2d := by
  intro F _ _ hF K _ _ e N
  refine ⟨innAut_sup_zpowers_eq e hF N.t_mem_diag N.t_not_mem_inn, ⟨innDiagEquiv e⟩,
    P_sup_zpowers_eq_Pt e hF N, ?_⟩
  obtain ⟨m, hm, ⟨d⟩⟩ := dihedral_of_sylow_inf_innDiag e hF N.T
  exact ⟨m + 1, isDihedralTwoGroup_of_equiv hm d⟩

end Parts



end CFSG.GH74.GLS.IVK
