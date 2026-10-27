module

public import CFSG.GF2Type.SmithTypeE.E7.IdMod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.DMod

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Stabilizers

theorem map_conj_K0_of_mem_Stab0 {n : TD6} (hn : n ∈ Stab0) :
    K0.map (MulAut.conj n).toMonoidHom = K0 := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact K0_normal hn hk
  · intro k hk
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * k * n, K0_normal (inv_mem hn) hk, ?_⟩
    show n * (n⁻¹ * k * n) * n⁻¹ = k
    group

theorem normalizer_K0 {n : TD6} (hn : K0.map (MulAut.conj n).toMonoidHom = K0) :
    n • (0 : Fin 75735) = 0 := by
  have hconj : ∀ k ∈ K0, n⁻¹ * k * n ∈ K0 := by
    intro k hk
    have hk' : k ∈ K0.map (MulAut.conj n).toMonoidHom := by rw [hn]; exact hk
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hk'
    have e : n⁻¹ * k * n = x := by
      rw [← hxk]
      show n⁻¹ * (n * x * n⁻¹) * n = x
      group
    rw [e]
    exact hx
  have hfix : ∀ k ∈ K0, rhoMod k (wtV (n • (0 : Fin 75735)).val) =
      wtV (n • (0 : Fin 75735)).val := by
    intro k hk
    have h1 : wtV (n • (0 : Fin 75735)).val = rhoMod n (wtV 0) := by
      rw [← rhoMod_wtV n 0]
      rfl
    have h2 : rhoMod (n⁻¹ * k * n) (wtV 0) = wtV 0 := by
      have hs : n⁻¹ * k * n ∈ Stab0 := K0_le_stab (hconj k hk)
      have h3 := rhoMod_wtV (n⁻¹ * k * n) 0
      rw [MulAction.mem_stabilizer_iff.mp hs] at h3
      exact h3
    have e : k * n = n * (n⁻¹ * k * n) := by group
    rw [h1, ← LinearEquiv.mul_apply (rhoMod k) (rhoMod n) (wtV 0),
      ← map_mul, e, map_mul, LinearEquiv.mul_apply, h2]
  rcases fixed_of_K0 hfix with h0 | h1
  · exact absurd h0 (wtV_ne_zero (n • (0 : Fin 75735)).2)
  · exact Fin.ext (wtV_injective (n • (0 : Fin 75735)).2 (by norm_num) h1)

theorem map_conj_mul (A : Subgroup TD6) (a b : TD6) :
    A.map (MulAut.conj (a * b)).toMonoidHom = (A.map (MulAut.conj b).toMonoidHom).map
      (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem map_conj_one (A : Subgroup TD6) : A.map (MulAut.conj (1 : TD6)).toMonoidHom = A := by
  ext k
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hk
    exact ⟨k, hk, by simp⟩

theorem conj_K0_eq_iff {a b : TD6} :
    K0.map (MulAut.conj a).toMonoidHom = K0.map (MulAut.conj b).toMonoidHom ↔
      a • (0 : Fin 75735) = b • (0 : Fin 75735) := by
  constructor
  · intro h
    have hn : K0.map (MulAut.conj (b⁻¹ * a)).toMonoidHom = K0 := by
      rw [map_conj_mul K0 b⁻¹ a, h, ← map_conj_mul K0 b⁻¹ b, inv_mul_cancel, map_conj_one]
    have h0 := normalizer_K0 hn
    calc a • (0 : Fin 75735) = (b * (b⁻¹ * a)) • (0 : Fin 75735) := by rw [mul_inv_cancel_left]
      _ = b • ((b⁻¹ * a) • (0 : Fin 75735)) := mul_smul _ _ _
      _ = b • (0 : Fin 75735) := by rw [h0]
  · intro h
    have hn : b⁻¹ * a ∈ Stab0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
    have hn' := map_conj_K0_of_mem_Stab0 hn
    have e := map_conj_mul K0 b (b⁻¹ * a)
    rw [hn', mul_inv_cancel_left] at e
    exact e

end Stabilizers

section Planes

@[expose] noncomputable def planeOfPsi (S : Setting G) (ψ : S.Mbar ≃* TD6) (h : S.M) :
    Fin 75735 :=
  ψ (rhoM S h) • (0 : Fin 75735)

theorem subgroupOf_Lbar_mul {g : G} (h : S.M) :
    (S.Lbar ((h : G) * g)).subgroupOf S.Mbar =
      ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj (rhoM S h)).toMonoidHom := by
  ext x
  rw [mem_subgroupOf, S.Lbar_mul (g := g) h.2]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, S.Lbar_le_Mbar g hy⟩, mem_subgroupOf.mpr hy, Subtype.ext ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_rhoM]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    exact hyx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨(y : S.O), mem_subgroupOf.mp hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_rhoM] using this

theorem map_Lbar_mul_eq (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0) (h : S.M) :
    ((S.Lbar ((h : G) * g)).subgroupOf S.Mbar).map ψ.toMonoidHom =
      K0.map (MulAut.conj (ψ (rhoM S h))).toMonoidHom := by
  rw [← hψ, subgroupOf_Lbar_mul h, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv]

theorem Lbar_eq_of_planeOfPsi_eq (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0) {h h' : S.M}
    (he : planeOfPsi S ψ h = planeOfPsi S ψ h') :
    S.Lbar ((h : G) * g) = S.Lbar ((h' : G) * g) := by
  have e : ((S.Lbar ((h : G) * g)).subgroupOf S.Mbar).map ψ.toMonoidHom =
      ((S.Lbar ((h' : G) * g)).subgroupOf S.Mbar).map ψ.toMonoidHom := by
    rw [map_Lbar_mul_eq ψ hψ h, map_Lbar_mul_eq ψ hψ h']
    exact conj_K0_eq_iff.mpr he
  have e2 := Subgroup.map_injective ψ.injective e
  rw [subgroupOf_inj, inf_eq_left.mpr (S.Lbar_le_Mbar _),
    inf_eq_left.mpr (S.Lbar_le_Mbar _)] at e2
  exact e2

theorem cl_eq_of_planeOfPsi_eq [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {h h' : S.M}
    (he : planeOfPsi S ψ h = planeOfPsi S ψ h') :
    S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹) =
      S.cl (((h' : G) * g) * S.z * ((h' : G) * g)⁻¹) := by
  obtain ⟨hbQ, hbne⟩ := mul_conj_mem h haQ hne
  obtain ⟨hcQ, hcne⟩ := mul_conj_mem h' haQ hne
  have hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) := ⟨ψ.trans omegaTD6.symm⟩
  have hL := Lbar_eq_of_planeOfPsi_eq ψ hψ he
  exact ((Lbar_eq_iff_cl_eq I hw hO hbQ hbne hcQ hcne).mp hL.symm).symm

theorem planeOfPsi_surj (ψ : S.Mbar ≃* TD6) (i : Fin 75735) :
    ∃ h : S.M, planeOfPsi S ψ h = i := by
  obtain ⟨t, ht⟩ := exists_smul_zero_eq i
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm t)
  refine ⟨m, ?_⟩
  rw [planeOfPsi, hm, MulEquiv.apply_symm_apply, ht]

theorem planeOfPsi_mul (ψ : S.Mbar ≃* TD6) (m h : S.M) :
    planeOfPsi S ψ (m * h) = ψ (rhoM S m) • planeOfPsi S ψ h := by
  simp only [planeOfPsi, map_mul, mul_smul]

end Planes

@[expose] noncomputable def xcl
    (S : Setting G) (ψ : S.Mbar ≃* TD6) (g : G) (i : ℕ) :
    S.Qt :=
  Classical.epsilon fun v : S.Qt => ∃ h : S.M, (planeOfPsi S ψ h).val = i ∧
    S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹) = v

section Classes

theorem xcl_eq_cl [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16) (ψ : S.Mbar ≃* TD6)
    {g : G} (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (i : ℕ) {h : S.M}
    (hi : (planeOfPsi S ψ h).val = i) :
    xcl S ψ g i = S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹) := by
  have hex : ∃ v : S.Qt, ∃ h' : S.M, (planeOfPsi S ψ h').val = i ∧
      S.cl (((h' : G) * g) * S.z * ((h' : G) * g)⁻¹) = v :=
    ⟨_, h, hi, rfl⟩
  obtain ⟨h', hpl, hv⟩ := Classical.epsilon_spec hex
  have heq : planeOfPsi S ψ h = planeOfPsi S ψ h' := Fin.ext (hi.trans hpl.symm)
  rw [xcl, ← hv]
  exact (cl_eq_of_planeOfPsi_eq I hw ψ hψ haQ hne heq).symm

theorem xcl_smul [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16) (ψ : S.Mbar ≃* TD6)
    {g : G} (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M) (i : Fin 75735) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (xcl S ψ g i.val) =
      xcl S ψ g (ψ (rhoM S m) • i).val := by
  obtain ⟨h, hh⟩ := planeOfPsi_surj ψ i
  have e1 := xcl_eq_cl I hw ψ hψ haQ hne i.val (h := h) (by rw [hh])
  have hmh : planeOfPsi S ψ (m * h) = ψ (rhoM S m) • i := by
    rw [planeOfPsi_mul, hh]
  have e2 := xcl_eq_cl I hw ψ hψ haQ hne (ψ (rhoM S m) • i).val (h := m * h) (by rw [hmh])
  rw [e1, e2]
  obtain ⟨hbQ, -⟩ := mul_conj_mem h haQ hne
  have e3 := S.ρ_cl_conj_z m.2 hbQ
  rw [show ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.ρ ⟨(m : G), m.2⟩ from rfl, e3]
  congr 1
  simp only [Subgroup.coe_mul, mul_assoc]

end Classes

end CFSG.GF2Type.SmithTypeE.E7
