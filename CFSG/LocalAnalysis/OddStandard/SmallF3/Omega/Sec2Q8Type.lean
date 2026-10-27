module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Lin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem orthogonalDet_of_block_anticomm (hQ : Q.Nondegenerate) {y t s : OGroup Q}
    (hy : y * y = 1) (hty : t * y = y * t) (hsy : s * y = y * s) (htt : t * t = y)
    (hst : s * t * s⁻¹ = piOrth Q * t⁻¹)
    (hW : Even (Module.finrank (ZMod 3) (commSp y))) :
    QuadraticMap.orthogonalDet Q t = (-1) ^ (Module.finrank (ZMod 3) (fixSp y) / 2) := by
  have ht : t ∈ Subgroup.centralizer ({y} : Set (OGroup Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hty
  have hs : s ∈ Subgroup.centralizer ({y} : Set (OGroup Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hsy
  rw [← range_blockHom hQ hy] at ht hs
  obtain ⟨p, rfl⟩ := ht
  obtain ⟨p', rfl⟩ := hs
  have hpp : p * p = (1, piOrth (Q.restrict (commSp y))) := by
    apply blockHom_injective hy
    rw [map_mul, htt, blockHom_one_piOrth hy]
  have hp1sq : p.1 * p.1 = 1 := by simpa using (Prod.ext_iff.mp hpp).1
  have hp2sq : p.2 * p.2 = piOrth (Q.restrict (commSp y)) := by
    simpa using (Prod.ext_iff.mp hpp).2
  have hp' : p' * p * p'⁻¹ =
      (piOrth (Q.restrict (fixSp y)), piOrth (Q.restrict (commSp y))) * p⁻¹ := by
    apply blockHom_injective hy
    simpa only [map_mul, map_inv, blockHom_piOrth_piOrth hy] using hst
  have hp1rel : p'.1 * p.1 * p'.1⁻¹ = piOrth (Q.restrict (fixSp y)) * p.1 := by
    have h1 : p'.1 * p.1 * p'.1⁻¹ = piOrth (Q.restrict (fixSp y)) * (p.1)⁻¹ := by
      simpa using (Prod.ext_iff.mp hp').1
    rw [inv_eq_of_mul_eq_one_right hp1sq] at h1
    exact h1
  have hdet1 : QuadraticMap.orthogonalDet (Q.restrict (fixSp y)) p.1 =
      (-1) ^ (Module.finrank (ZMod 3) (fixSp y) / 2) :=
    (orthogonalDet_of_conj (V := fixSp y) (Q := Q.restrict (fixSp y))
      (nondegenerate_restrict_fixSp hQ hy) hp1sq hp1rel).2
  have hdet2 : QuadraticMap.orthogonalDet (Q.restrict (commSp y)) p.2 = 1 :=
    orthogonalDet_eq_one_of_mul_self_eq_piOrth (V := commSp y)
      (Q := Q.restrict (commSp y)) hW hp2sq
  rw [orthogonalDet_blockHom hy p, hdet1, hdet2, mul_one]

theorem invType_eq_of_q8_lift (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    {q r : OGroup Q} (hq : q ∈ omegaGroup hQ) (hr : r ∈ omegaGroup hQ)
    (hyy : (q * q) * (q * q) = 1) (hy1 : q * q ≠ 1) (hyπ : q * q ≠ piOrth Q)
    (hb : r * r = q * q ∨ r * r = piOrth Q * (q * q))
    (hc : r * q = q⁻¹ * r ∨ r * q = piOrth Q * (q⁻¹ * r)) :
    invType (q * q) = (4, 1) := by
  have hΩ : q * q ∈ omegaGroup hQ := mul_mem hq hq
  have homega := (involution_mem_omegaGroup_iff hQ hyy).mp hΩ
  have hev : Even (invDim (q * q)) := homega.1
  have hsign : invSign (q * q) = (-1) ^ (invDim (q * q) / 2) := homega.2
  have hle : invDim (q * q) ≤ 8 := by rw [← hdim]; exact invDim_le (q * q)
  have hne0 : invDim (q * q) ≠ 0 := fun h => hy1 ((invDim_eq_zero_iff hyy).mp h)
  have hne8 : invDim (q * q) ≠ 8 := by
    intro h
    have hfin : invDim (q * q) = Module.finrank (ZMod 3) V := by rw [h, hdim]
    exact hyπ ((invDim_eq_finrank_iff hyy).mp hfin)
  have h4 : 4 ∣ invDim (q * q) := by
    rcases hc with hcA | hcB
    · rcases hb with hb0 | hb1
      · exact (four_dvd_invDim_of_quaternion hQ hb0.symm hyy hcA).1
      ·
        have hcommπq : q * piOrth Q = piOrth Q * q :=
          Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) q
        have hcommπr : r * piOrth Q = piOrth Q * r :=
          Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) r
        have hcommyπ : Commute (q * q) (piOrth Q) :=
          Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (q * q)
        have hsy' : q * (piOrth Q * (q * q)) = (piOrth Q * (q * q)) * q := by
          calc q * (piOrth Q * (q * q))
              = q * piOrth Q * (q * q) := (mul_assoc q (piOrth Q) (q * q)).symm
            _ = piOrth Q * q * (q * q) := by rw [hcommπq]
            _ = piOrth Q * (q * (q * q)) := mul_assoc (piOrth Q) q (q * q)
            _ = piOrth Q * ((q * q) * q) := by rw [mul_assoc q q q]
            _ = (piOrth Q * (q * q)) * q := (mul_assoc (piOrth Q) (q * q) q).symm
        have hty' : r * (piOrth Q * (q * q)) = (piOrth Q * (q * q)) * r := by
          rw [← hb1]; exact (mul_assoc r r r).symm
        have hyinv : (q * q)⁻¹ = q * q := inv_eq_of_mul_eq_one_right hyy
        have hqr : q * r = r * q⁻¹ := by
          have h : (q * r) * q = r := by
            rw [mul_assoc, hcA, ← mul_assoc, mul_inv_cancel, one_mul]
          exact eq_mul_inv_iff_mul_eq.mpr h
        have hL : q * r * q⁻¹ = r * (q * q) := by
          rw [hqr, mul_assoc, ← mul_inv_rev, hyinv]
        have hr4 : (r * r) * (r * r) = 1 := by
          rw [hb1, Commute.mul_mul_mul_comm hcommyπ (piOrth Q) (q * q),
            piOrth_mul_self, one_mul, hyy]
        have hr_inv : r⁻¹ = r * (r * r) := by
          apply inv_eq_of_mul_eq_one_right
          calc r * (r * (r * r)) = (r * r) * (r * r) := (mul_assoc r r (r * r)).symm
            _ = 1 := hr4
        have hmid : piOrth Q * (piOrth Q * (q * q)) = q * q := by
          rw [← mul_assoc, piOrth_mul_self, one_mul]
        have hR : piOrth Q * r⁻¹ = r * (q * q) := by
          rw [hr_inv, hb1]
          calc piOrth Q * (r * (piOrth Q * (q * q)))
              = (piOrth Q * r) * (piOrth Q * (q * q)) :=
                  (mul_assoc (piOrth Q) r (piOrth Q * (q * q))).symm
            _ = (r * piOrth Q) * (piOrth Q * (q * q)) := by rw [← hcommπr]
            _ = r * (piOrth Q * (piOrth Q * (q * q))) :=
                  mul_assoc r (piOrth Q) (piOrth Q * (q * q))
            _ = r * (q * q) := by rw [hmid]
        have hst : q * r * q⁻¹ = piOrth Q * r⁻¹ := hL.trans hR.symm
        have hdim_y' : invDim (piOrth Q * (q * q)) = 8 - invDim (q * q) := by
          have h := congrArg Prod.fst (invType_piOrth_mul hQ hyy)
          rw [hdim] at h
          exact h
        have hev' : Even (invDim (piOrth Q * (q * q))) := by
          rw [hdim_y']
          obtain ⟨m, hm⟩ := hev
          exact ⟨4 - m, by omega⟩
        have hdetr : QuadraticMap.orthogonalDet Q r =
            (-1) ^ (Module.finrank (ZMod 3) (fixSp (piOrth Q * (q * q))) / 2) :=
          orthogonalDet_of_block_anticomm hQ (piOrth_mul_mul_self hyy) hty' hsy' hb1 hst hev'
        have hrdet : QuadraticMap.orthogonalDet Q r = 1 := by
          have h := (mem_omegaGroup_iff hQ).mp hr
          rw [CFSG.ClassicalInvolution.detSpinorNorm_apply] at h
          simpa using congrArg Prod.fst h
        have hevfix' : Even (Module.finrank (ZMod 3) (fixSp (piOrth Q * (q * q))) / 2) := by
          rw [hdetr] at hrdet
          exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp hrdet
        have hsum' : Module.finrank (ZMod 3) (fixSp (piOrth Q * (q * q))) +
            invDim (piOrth Q * (q * q)) = Module.finrank (ZMod 3) V :=
          finrank_fixSp_add_finrank_commSp (Q := Q) (piOrth Q * (q * q))
        rw [hdim, hdim_y'] at hsum'
        have hfix'_eq : Module.finrank (ZMod 3) (fixSp (piOrth Q * (q * q))) =
            invDim (q * q) := by
          omega
        rw [hfix'_eq] at hevfix'
        obtain ⟨m, hm⟩ := hev
        obtain ⟨k, hk⟩ := hevfix'
        refine ⟨k, ?_⟩
        omega
    ·
      have hcommπr : r * piOrth Q = piOrth Q * r :=
        Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) r
      have hry : r * (q * q) = (q * q) * r := by
        rcases hb with hb0 | hb1
        · rw [← hb0]; exact (mul_assoc r r r).symm
        · have hy_eq : q * q = piOrth Q * (r * r) := by
            rw [hb1, ← mul_assoc, piOrth_mul_self, one_mul]
          rw [hy_eq]
          calc r * (piOrth Q * (r * r))
              = r * piOrth Q * (r * r) := (mul_assoc r (piOrth Q) (r * r)).symm
            _ = piOrth Q * r * (r * r) := by rw [hcommπr]
            _ = piOrth Q * (r * (r * r)) := mul_assoc (piOrth Q) r (r * r)
            _ = piOrth Q * ((r * r) * r) := by rw [mul_assoc r r r]
            _ = (piOrth Q * (r * r)) * r := (mul_assoc (piOrth Q) (r * r) r).symm
      have hqy : q * (q * q) = (q * q) * q := (mul_assoc q q q).symm
      have hst : r * q * r⁻¹ = piOrth Q * q⁻¹ := by rw [hcB]; group
      have hdetq : QuadraticMap.orthogonalDet Q q =
          (-1) ^ (Module.finrank (ZMod 3) (fixSp (q * q)) / 2) :=
        orthogonalDet_of_block_anticomm hQ hyy hqy hry rfl hst hev
      have hqdet : QuadraticMap.orthogonalDet Q q = 1 := by
        have h := (mem_omegaGroup_iff hQ).mp hq
        rw [CFSG.ClassicalInvolution.detSpinorNorm_apply] at h
        simpa using congrArg Prod.fst h
      have hevfix : Even (Module.finrank (ZMod 3) (fixSp (q * q)) / 2) := by
        rw [hdetq] at hqdet
        exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp hqdet
      have hsum : Module.finrank (ZMod 3) (fixSp (q * q)) + invDim (q * q) =
          Module.finrank (ZMod 3) V :=
        finrank_fixSp_add_finrank_commSp (Q := Q) (q * q)
      rw [hdim] at hsum
      have hfix_eq : Module.finrank (ZMod 3) (fixSp (q * q)) = 8 - invDim (q * q) := by
        omega
      rw [hfix_eq] at hevfix
      obtain ⟨m, hm⟩ := hev
      obtain ⟨k, hk⟩ := hevfix
      refine ⟨1, ?_⟩
      omega
  have hdim4 : invDim (q * q) = 4 := by
    obtain ⟨k, hk⟩ := h4
    omega
  have hsign4 : invSign (q * q) = 1 := by
    rw [hsign, hdim4]
    norm_num
  exact Prod.ext hdim4 hsign4

end CFSG.OddStandard.SmallF3.Omega
