module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0SuzCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup CFSG.Open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore

theorem q0_parts :
    permOK 1782 outerTab = true ∧ inM outerTab = false ∧
    (∀ i < 6, eqA 1782 (compA 1782 (compA 1782 outerTab (qArr i)) (invCand 1782 outerTab))
      (compA 1782 qProds[(oact i).1]! (tPow (oact i).2)) = true) ∧
    (∀ j < matEnum.tabs.size, (matEnum.tabs[j]! == outerMat) = false) := by
  have h := q0Suz_check
  rw [q0SuzCheck] at h
  simp only [Bool.and_eq_true, allBelow_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem oact_lt : ∀ i < 6, (oact i).1 < 64 ∧ (oact i).2 < 2 := by
  decide

theorem colFold_oact_lt : ∀ v < 64, colFold (fun i => (oact i).1) v < 64 := by
  decide

theorem outerMat_get {v : ℕ} (hv : v < 64) : outerMat[v]! = colFold (fun i => (oact i).1) v := by
  unfold outerMat
  exact getElem!_ofFn' _ hv

theorem outerMat_size : outerMat.size = 64 := by
  unfold outerMat
  exact Array.size_ofFn

@[expose] noncomputable def q0OuterGen : Equiv.Perm (Fin 1782) := permC 1782 outerTab

theorem rep_q0OuterGen : Rep 1782 outerTab q0OuterGen :=
  rep_permOK q0_parts.1

theorem q0OuterGen_not_mem :
    q0OuterGen ∉ suzM := fun h => by
  have := (inM_iff rep_q0OuterGen).mpr h
  rw [q0_parts.2.1] at this
  exact Bool.false_ne_true this

theorem invFullGenArrs_one_size : (invFullGenArrs 1).size = 6 := by
  simp [invFullGenArrs, invFullGenCounts]

theorem q0OuterGen_mem_invD :
    q0OuterGen ∈ invD 1 := by
  have h3 : 3 < (invFullChain 1).originalCount := by
    change 3 < (invFullGenArrs 1).size
    rw [invFullGenArrs_one_size]
    norm_num
  have hrep := (invFullChain_arrays (by norm_num : 1 < 4)).orig ⟨3, h3⟩
  rw [show q0OuterGen = (invFullChain 1).original.get ⟨3, h3⟩ from
    rep_q0OuterGen.unique hrep]
  exact subset_closure (schreier_vector_get_mem_toList _ _)

theorem q0OuterGen_conj
    {i : ℕ} (hi : i < 6) :
    q0OuterGen * qVec (2 ^ i) * q0OuterGen⁻¹ = qVec (oact i).1 * suzInv 1 ^ (oact i).2 := by
  rw [qVec_two_pow hi]
  exact eq_of_eqA (rep_compA (rep_compA rep_q0OuterGen (rep_qArr hi))
    (rep_invCand rep_q0OuterGen q0_parts.1))
    (rep_compA (rep_qProds (oact_lt i hi).1) (rep_tPow (oact_lt i hi).2)) (q0_parts.2.2.1 i hi)

theorem mem_zpowers_of_mem_centralizer_Q
    {g : Equiv.Perm (Fin 1782)} (hgT : g ∈ suzT)
    (hg : g ∈ centralizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782)))) :
    g ∈ zpowers (suzInv 1) := by
  set C := coord_qVec with hC
  have hgt : g * suzInv 1 = suzInv 1 * g := (mem_centralizer_iff.mp hg _ C.t_mem).symm
  have hgD : g ∈ invD 1 := by
    rw [invD_eq_centT (by norm_num)]
    exact ⟨mem_centralizer_singleton_iff.mpr hgt, hgT⟩
  by_cases hgM : g ∈ suzM
  ·
    have hgE : g ∈ invE 1 := by
      rw [invE_eq_centM (by norm_num)]
      exact ⟨mem_centralizer_singleton_iff.mpr hgt, hgM⟩
    have hker : (⟨g, hgE⟩ : ↥(invE 1)) ∈ rho1.ker := by
      rw [MonoidHom.mem_ker]
      refine LinearEquiv.ext fun u => ?_
      obtain ⟨a, ha, rfl⟩ := C.psi_surj u
      change C.rho invE_le ⟨g, hgE⟩ (Coord.psi a) = Coord.psi a
      rw [C.rho_psi invE_le _ ha]
      congr 1
      rw [← mem_centralizer_iff.mp hg a ha, mul_inv_cancel_right]
    rw [ker_rho1] at hker
    have hgQ : g ∈ C.Q := mem_subgroupOf.mp hker
    have hgZ : g ∈ centerIn C.Q := mem_inf.mpr ⟨hgQ, hg⟩
    rwa [C.centerIn_Q] at hgZ
  ·
    exfalso
    have hg₀D := q0OuterGen_mem_invD
    rw [invD_eq_centT (by norm_num)] at hg₀D
    obtain ⟨hg₀t, hg₀T⟩ := mem_inf.mp hg₀D
    have hcM : q0OuterGen⁻¹ * g ∈ suzM := by
      have hidx := suzM_index_T
      have h := (mul_mem_iff_of_index_two hidx (a := (⟨q0OuterGen, hg₀T⟩ : ↥suzT)⁻¹)
        (b := ⟨g, hgT⟩)).mpr ⟨fun h => absurd (mem_subgroupOf.mp (inv_mem_iff.mp h))
          q0OuterGen_not_mem, fun h => absurd (mem_subgroupOf.mp h) hgM⟩
      exact mem_subgroupOf.mp h
    have hct : (q0OuterGen⁻¹ * g) * suzInv 1 = suzInv 1 * (q0OuterGen⁻¹ * g) := by
      have h1 := mem_centralizer_singleton_iff.mp hg₀t
      calc (q0OuterGen⁻¹ * g) * suzInv 1 = q0OuterGen⁻¹ * (suzInv 1 * g) := by rw [mul_assoc, hgt]
        _ = q0OuterGen⁻¹ * (suzInv 1 * q0OuterGen) * q0OuterGen⁻¹ * g := by group
        _ = q0OuterGen⁻¹ * (q0OuterGen * suzInv 1) * q0OuterGen⁻¹ * g := by rw [h1]
        _ = suzInv 1 * (q0OuterGen⁻¹ * g) := by group
    have hcE : (q0OuterGen⁻¹ * g)⁻¹ ∈ invE 1 := by
      rw [invE_eq_centM (by norm_num)]
      refine inv_mem ⟨mem_centralizer_singleton_iff.mpr hct, hcM⟩
    have hconj : ∀ i < 6, (q0OuterGen⁻¹ * g)⁻¹ * qVec (2 ^ i) * ((q0OuterGen⁻¹ * g)⁻¹)⁻¹ =
        qVec (oact i).1 * suzInv 1 ^ (oact i).2 := by
      intro i hi
      have hmem : q0OuterGen * qVec (2 ^ i) * q0OuterGen⁻¹ ∈ C.Q := by
        rw [q0OuterGen_conj hi]
        exact C.mem_Q_iff.mpr ⟨_, (oact_lt i hi).1, _, (oact_lt i hi).2, rfl⟩
      have h1 := mem_centralizer_iff.mp hg _ hmem
      rw [← q0OuterGen_conj hi]
      calc (q0OuterGen⁻¹ * g)⁻¹ * qVec (2 ^ i) * ((q0OuterGen⁻¹ * g)⁻¹)⁻¹ =
          g⁻¹ * (q0OuterGen * qVec (2 ^ i) * q0OuterGen⁻¹ * g) := by group
        _ = g⁻¹ * (g * (q0OuterGen * qVec (2 ^ i) * q0OuterGen⁻¹)) := by rw [h1]
        _ = q0OuterGen * qVec (2 ^ i) * q0OuterGen⁻¹ := by group
    set c' : ↥(invE 1) := ⟨(q0OuterGen⁻¹ * g)⁻¹, hcE⟩ with hc'
    have htab : TabRep outerMat (kappa (rho1 c')) := by
      refine ⟨outerMat_size, fun v => ?_⟩
      rw [outerMat_get v.2, kappa_apply]
      change _ = ((bitEquiv.symm (C.rho invE_le c' (bitVec v)) : Fin 64) : ℕ)
      rw [C.rho_bitVec invE_le c' (w := fun i => (oact i).1) (b := fun i => (oact i).2)
        (fun i hi => (oact_lt i hi).1) (fun i hi => (oact_lt i hi).2) hconj v.2,
        bitEquiv_symm_bitVec (colFold_oact_lt v v.2)]
    obtain ⟨t, ht, htr⟩ := kappa_rho1_enumerates.complete _ ⟨_, ⟨c', rfl⟩, rfl⟩
    have htt : t = outerMat := htr.tab_eq htab
    obtain ⟨j, hj, hjt⟩ := exists_getElem!_of_mem ht
    have h4 := q0_parts.2.2.2 j hj
    rw [hjt, htt, beq_self_eq_true] at h4
    exact absurd h4 (by decide)

end CFSG.ComponentClassification.AS81.SuzB0
