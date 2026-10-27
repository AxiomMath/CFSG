module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenURep
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BSuzDat
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open Subgroup CFSG.Open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzRecog

section Form

open CFSG.ComponentClassification.AS81.Sec2Omega in
theorem bilM_nondeg (w : Fin 6 → ZMod 2) (hw : ∀ v, bilM v w = 0) : w = 0 :=
  qMinusForm_nondegenerate.2 w fun v => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hw v

theorem bilM_add_left (x y w : Fin 6 → ZMod 2) : bilM (x + y) w = bilM x w + bilM y w :=
  QuadraticMap.polar_add_left _ _ _ _

open CFSG.ComponentClassification.AS81.Sec2Omega in
theorem bilM_orthogonal {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup qMinusForm) (v w : Fin 6 → ZMod 2) :
    bilM (g v) (g w) = bilM v w := by
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg
  show qMinusForm (g v + g w) - qMinusForm (g v) - qMinusForm (g w) =
    qMinusForm (v + w) - qMinusForm v - qMinusForm w
  rw [← map_add g v w, h, h, h]

end Form

section Rho

theorem mem_invD_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ invD 1 ↔ g ∈ suzT ∧ g * suzInv 1 = suzInv 1 * g := by
  rw [invD_eq_centT (by norm_num)]
  exact ⟨fun h => ⟨(mem_inf.1 h).2, mem_centralizer_singleton_iff.1 (mem_inf.1 h).1⟩,
    fun h => mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h.2, h.1⟩⟩

theorem invD_le_norm : invD 1 ≤ normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ⊓
    centralizer ({suzInv 1} : Set (Equiv.Perm (Fin 1782))) := fun g hg => by
  obtain ⟨hgT, hgt⟩ := mem_invD_iff.1 hg
  exact ⟨normalizer_Q_of_comm hgT hgt, mem_centralizer_singleton_iff.2 hgt⟩

@[expose] noncomputable def rhoD :
    ↥(invD 1) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
  coord_qVec.rho invD_le_norm

theorem rhoD_eq_rho1 (c : ↥(invE 1)) :
    rhoD ⟨c, invE_le_invD (by norm_num) c.2⟩ = rho1 c := by
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨a, ha, rfl⟩ := coord_qVec.psi_surj u
  exact (coord_qVec.rho_psi invD_le_norm _ ha).trans (coord_qVec.rho_psi invE_le c ha).symm

theorem rho1_ne_rhoD_outer (c : ↥(invE 1)) :
    rho1 c ≠ rhoD ⟨q0OuterGen, q0OuterGen_mem_invD⟩ := by
  intro h
  have key : ∀ {v : ℕ}, v < 64 → rhoD ⟨q0OuterGen, q0OuterGen_mem_invD⟩ (bitVec v) =
      bitVec (colFold (fun i => (oact i).1) v) := fun {v} hv =>
    coord_qVec.rho_bitVec invD_le_norm (⟨q0OuterGen, q0OuterGen_mem_invD⟩ : ↥(invD 1))
      (w := fun i => (oact i).1) (b := fun i => (oact i).2) (fun i hi => (oact_lt i hi).1)
      (fun i hi => (oact_lt i hi).2) (fun i hi => q0OuterGen_conj hi) hv
  have htab : TabRep outerMat (kappa (rho1 c)) := by
    refine ⟨outerMat_size, fun v => ?_⟩
    rw [outerMat_get v.2, kappa_apply, h]
    change _ = ((bitEquiv.symm (rhoD ⟨q0OuterGen, q0OuterGen_mem_invD⟩ (bitVec v)) : Fin 64) : ℕ)
    rw [show rhoD ⟨q0OuterGen, q0OuterGen_mem_invD⟩ (bitVec v) =
      bitVec (colFold (fun i => (oact i).1) v) from key v.2,
      bitEquiv_symm_bitVec (colFold_oact_lt v v.2)]
  obtain ⟨t, ht, htr⟩ := kappa_rho1_enumerates.complete _ ⟨_, ⟨c, rfl⟩, rfl⟩
  have htt : t = outerMat := htr.tab_eq htab
  obtain ⟨j, hj, hjt⟩ := exists_getElem!_of_mem ht
  have h4 := q0_parts.2.2.2 j hj
  rw [hjt, htt, beq_self_eq_true] at h4
  exact absurd h4 (by decide)

theorem mem_Q_of_rhoD_eq_one {g : Equiv.Perm (Fin 1782)} (hgD : g ∈ invD 1)
    (h : rhoD ⟨g, hgD⟩ = 1) : g ∈ coord_qVec.Q := by
  obtain ⟨hgT, hgt⟩ := mem_invD_iff.1 hgD
  by_cases hgM : g ∈ suzM
  · have hgE : g ∈ invE 1 := by
      rw [invE_eq_centM (by norm_num)]
      exact ⟨mem_centralizer_singleton_iff.2 hgt, hgM⟩
    have hker : (⟨g, hgE⟩ : ↥(invE 1)) ∈ rho1.ker := by
      rw [MonoidHom.mem_ker, ← rhoD_eq_rho1 ⟨g, hgE⟩]
      exact h
    rw [ker_rho1] at hker
    exact mem_subgroupOf.mp hker
  · exfalso
    have hg₀D := q0OuterGen_mem_invD
    obtain ⟨hg₀T, hg₀t⟩ := mem_invD_iff.1 hg₀D
    have hcM : q0OuterGen⁻¹ * g ∈ suzM := by
      have h := (mul_mem_iff_of_index_two suzM_index_T (a := (⟨q0OuterGen, hg₀T⟩ : ↥suzT)⁻¹)
        (b := ⟨g, hgT⟩)).mpr ⟨fun h => absurd (mem_subgroupOf.mp (inv_mem_iff.mp h))
          q0OuterGen_not_mem, fun h => absurd (mem_subgroupOf.mp h) hgM⟩
      exact mem_subgroupOf.mp h
    have hct : (q0OuterGen⁻¹ * g) * suzInv 1 = suzInv 1 * (q0OuterGen⁻¹ * g) := by
      calc (q0OuterGen⁻¹ * g) * suzInv 1 = q0OuterGen⁻¹ * (suzInv 1 * g) := by rw [mul_assoc, hgt]
        _ = q0OuterGen⁻¹ * (suzInv 1 * q0OuterGen) * q0OuterGen⁻¹ * g := by group
        _ = q0OuterGen⁻¹ * (q0OuterGen * suzInv 1) * q0OuterGen⁻¹ * g := by rw [hg₀t]
        _ = suzInv 1 * (q0OuterGen⁻¹ * g) := by group
    have hcD : q0OuterGen⁻¹ * g ∈ invD 1 := mem_invD_iff.2 ⟨suzM_le_suzT hcM, hct⟩
    have hcE : (q0OuterGen⁻¹ * g)⁻¹ ∈ invE 1 := by
      rw [invE_eq_centM (by norm_num)]
      exact inv_mem ⟨mem_centralizer_singleton_iff.2 hct, hcM⟩
    have hmul : (⟨g, hgD⟩ : ↥(invD 1)) = ⟨q0OuterGen, hg₀D⟩ * ⟨q0OuterGen⁻¹ * g, hcD⟩ :=
      Subtype.ext (mul_inv_cancel_left q0OuterGen g).symm
    have h2 : rhoD ⟨q0OuterGen, hg₀D⟩ * rhoD ⟨q0OuterGen⁻¹ * g, hcD⟩ = 1 := by
      rw [← map_mul, ← hmul]
      exact h
    refine rho1_ne_rhoD_outer ⟨(q0OuterGen⁻¹ * g)⁻¹, hcE⟩ ?_
    rw [← rhoD_eq_rho1]
    exact (map_inv rhoD (⟨q0OuterGen⁻¹ * g, hcD⟩ : ↥(invD 1))).trans
      (inv_eq_of_mul_eq_one_left h2)

theorem mem_invD_of_mem_cent {d : ↥suzT} (hd : d ∈ centralizer ({suzT1} : Set ↥suzT)) :
    (d : Equiv.Perm (Fin 1782)) ∈ invD 1 :=
  mem_invD_iff.2 ⟨d.2, congrArg Subtype.val (mem_centralizer_singleton_iff.1 hd)⟩

@[expose] noncomputable def embD : ↥(centralizer ({suzT1} : Set ↥suzT)) →* ↥(invD 1) where
  toFun d := ⟨(d : ↥suzT), mem_invD_of_mem_cent d.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem uSuz : USuz := by
  intro F X hFD hXD hF hFc hX hFX
  refine le_of_rep_isometry (V := Fin 6 → ZMod 2) (k := 3) (by rw [Module.finrank_fin_fun])
    bilM bilM_add_left bilM_nondeg (rhoD.comp embD) ?_ ?_ ?_ hFD hXD hF hFc hX hFX
  · exact coord_qVec.isPGroup_Q.of_equiv (subgroupOfEquivOfLe Q_le_suzT).symm
  · intro d hd
    exact mem_Q_of_rhoD_eq_one (mem_invD_of_mem_cent d.2) hd
  · intro d v w
    exact bilM_orthogonal (coord_qVec.rho_mem_orthogonalGroup invD_le_norm _) v w

end Rho

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
