module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSixInner

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem piOrth_mem_omegaGroup_eight (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) : piOrth Q ∈ omegaGroup hQ :=
  (piOrth_mem_omegaGroup_iff hQ).mpr ⟨by rw [hdim]; decide, by rw [hdim, hσ]; decide⟩

theorem isI4PlusIn_top_omegaProj_of_four_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) {y : omegaGroup hQ} (hyy : (y : OGroup Q) * y = 1)
    (hty : invType (y : OGroup Q) = (4, 1)) :
    IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) (omegaToProj hQ y) := by
  have hfix : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q)) := by
    have h1 := finrank_fixSp_add_finrank_commSp (Q := Q) (y : OGroup Q)
    have h2 : Module.finrank (ZMod 3) (commSp (y : OGroup Q)) = 4 := by
      simpa only [invType, invDim] using congrArg Prod.fst hty
    omega
  obtain ⟨K, M, hzK, hKM, hMC, hKM', hMC', hKsl, hKπ⟩ :=
    exists_pocket_chain_of_invType hQ y hyy hty hfix
  have hy1 : (y : OGroup Q) ≠ 1 := by
    intro h
    rw [h, invType_one] at hty
    exact absurd (congrArg Prod.fst hty) (by decide)
  have hzz : orderOf y = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hyy)
      (fun h => hy1 (congrArg Subtype.val h))
  have hdis : Disjoint K (omegaToProj hQ).ker := by
    rw [Subgroup.disjoint_def]
    intro k hk hkρ
    rcases (omegaToProj_eq_one_iff hQ k).mp (MonoidHom.mem_ker.mp hkρ) with h | h
    · exact Subtype.ext h
    · exact absurd h (hKπ k hk)
  exact isI4PlusIn_map_of_chain (omegaToProj hQ) (omegaToProj_surjective hQ)
    (fun m hm g => omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g) hzz hzK hKM hMC hKM'
    hMC' hKsl hdis

theorem innerData_omegaProj_of_two_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hσ : quadSign Q = 1) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hty : invType (y : OGroup Q) = (2, -1)) :
    InnerData (omegaProj hQ) (omegaToProj hQ y) := by
  let p : omegaGroup hQ := ⟨piOrth Q, piOrth_mem_omegaGroup_eight hQ hdim hσ⟩
  have hd : invDim (y : OGroup Q) = 2 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hs : invSign (y : OGroup Q) = -1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hty
  have h1 : ((p * y : omegaGroup hQ) : OGroup Q) * ((p * y : omegaGroup hQ) : OGroup Q) = 1 :=
    piOrth_mul_mul_self hyy
  have h2 : invType ((p * y : omegaGroup hQ) : OGroup Q) = (6, -1) := by
    change invType (piOrth Q * (y : OGroup Q)) = _
    rw [invType_piOrth_mul hQ hyy, hd, hs, hdim, hσ]
    decide
  have h3 : omegaToProj hQ (p * y) = omegaToProj hQ y := by
    rw [map_mul, (omegaToProj_eq_one_iff hQ p).mpr (Or.inr rfl), one_mul]
  have h4 := innerData_omegaProj_of_six_minus hQ hdim hσ h1 h2
  rwa [h3] at h4

theorem innerData_omegaProj_of_not_pocketed (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hσ : quadSign Q = 1)
    (hproj : ∀ y : omegaGroup hQ, (y : OGroup Q) * y = piOrth Q →
      InnerData (omegaProj hQ) (omegaToProj hQ y))
    {z : omegaProj hQ} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hnp : ¬ IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) z) : InnerData (omegaProj hQ) z := by
  obtain ⟨y, rfl⟩ := omegaToProj_surjective hQ z
  have hyy : omegaToProj hQ (y * y) = 1 := by rw [map_mul]; exact hzz
  rcases (omegaToProj_eq_one_iff hQ (y * y)).mp hyy with h | h
  ·
    have h' : (y : OGroup Q) * y = 1 := h
    obtain ⟨hev, hsg⟩ := (involution_mem_omegaGroup_iff hQ h').mp y.2
    obtain ⟨k, hk⟩ := hev
    have hle : invDim (y : OGroup Q) ≤ 8 := hdim ▸ invDim_le (y : OGroup Q)
    have hcases : invDim (y : OGroup Q) = 0 ∨ invDim (y : OGroup Q) = 2 ∨
        invDim (y : OGroup Q) = 4 ∨ invDim (y : OGroup Q) = 6 ∨ invDim (y : OGroup Q) = 8 := by
      omega
    rcases hcases with h0 | h2 | h4 | h6 | h8
    · exact absurd ((omegaToProj_eq_one_iff hQ y).mpr (Or.inl ((invDim_eq_zero_iff h').mp h0))) hz1
    · refine innerData_omegaProj_of_two_minus hQ hdim hσ h' ?_
      refine Prod.ext h2 ?_
      change invSign (y : OGroup Q) = -1
      rw [hsg, h2]
      decide
    · refine absurd ?_ hnp
      refine isI4PlusIn_top_omegaProj_of_four_plus hQ hdim h' (Prod.ext h4 ?_)
      change invSign (y : OGroup Q) = 1
      rw [hsg, h4]
      decide
    · refine innerData_omegaProj_of_six_minus hQ hdim hσ h' (Prod.ext h6 ?_)
      change invSign (y : OGroup Q) = -1
      rw [hsg, h6]
      decide
    · have hpi : (y : OGroup Q) = piOrth Q :=
        (invDim_eq_finrank_iff h').mp (by rw [h8, hdim])
      refine absurd ?_ hz1
      exact (omegaToProj_eq_one_iff hQ y).mpr (Or.inr hpi)
  · exact hproj y h

end CFSG.OddStandard.SmallF3.Omega
