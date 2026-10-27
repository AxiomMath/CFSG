module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Y

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

omit [Finite G] in
theorem InA.data (hInA : InA Ω K J) (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) :
    J ∉ omegaNbr Ω K ∧ K ≠ J ∧ ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J := by
  obtain ⟨⟨-, hJK, -⟩, hJnot, zK, zJ, hzK, hzJ, hnot⟩ := hInA
  have e1 : zK = z := hzK.eq hz
  have e2 : zJ = j := hzJ.eq hj
  rw [e1, e2] at hnot
  exact ⟨hJnot, Ne.symm hJK, fun y hy h => hnot ⟨y, hy, h⟩⟩

theorem ne_of_not_mem_omegaNbr (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hJnot : J ∉ omegaNbr Ω K)
    (hT : IsSylow2In T J) : z ≠ j := by
  rintro rfl
  exact hJnot ⟨hJ, Ne.symm hKJ, T, mem_RSet_of_isSylow2In hJ hT, hT.1,
    hT.1.trans (le_normalizer_of_twin hΩ hJ hK (Ne.symm hKJ) hj hz)⟩

theorem l6_4ThreeGenAll : L6_4ThreeGenAll := by
  intro G _ _ Ω hΩ K hK J hJ hInA z j hz hj X Y hX hY u v hU hUK hV hVJ hUV R T hR hT huR hvT
    hRN hTN
  subst hX hY
  obtain ⟨hJnot, hKJ, hA⟩ := InA.data hInA hz hj
  have hzj := ne_of_not_mem_omegaNbr hΩ hK hJ hKJ hz hj hJnot hT
  have hKnot := not_mem_omegaNbr_symm hΩ hK hJ hz hj hzj hJnot
  have c : Cfg64 Ω K J z j u v R T :=
    ⟨hΩ, hK, hJ, hKJ, hz, hj, hJnot, hKnot, hU, hUK, hV, hVJ, hUV, hR, hT, huR, hvT, hRN, hTN⟩
  obtain ⟨N₀K, hK0⟩ := exists_oddCompl c.sylow_U inferInstance
  obtain ⟨N₀J, hJ0⟩ := exists_oddCompl c.sylow_V inferInstance
  obtain ⟨r, hr, hru⟩ := c.exists_r
  obtain ⟨t, ht, htv⟩ := c.symm.exists_r
  have d : Cfg64D Ω K J z j u v R T N₀K N₀J r t := ⟨c, hK0, hJ0, hr, hru, ht, htv⟩
  have := d.normal
  have hne := d.Kstar_ne hA
  have htw := d.twinSet_eq hA
  refine ⟨⟨(c.X_eq_oddCore_sup hK0 hJ0).2.2, sup_le c.R_le_Y c.T_le_Y⟩,
    ⟨c.X_le_Y, c.Y_le_normalizer_X hK0 hJ0, sup_le inf_le_right inf_le_right, d.exists_D12 hA⟩,
    ⟨conjSub (r * t)⁻¹ J, hne, htw, ⟨(r * t)⁻¹, Subgroup.inv_mem _ d.rho_mem_Y, rfl⟩,
      d.v_sq_mem hne, ⟨conjSub (r * t)⁻¹ T, d.Rstar0_sylow, d.Rstar0_le_normalizer⟩, ?_⟩,
    ⟨fun r' hr' hru' => c.conj_j_of_not_mem hr' hru', fun t' ht' htv' => c.conj_t_z ht' htv',
      c.sylow_V⟩,
    d.centralizer_UV_le hA, fun W hW2 hUVW hWc => d.inf_eq_UV hA hW2 hUVW hWc⟩
  intro Rstar hRs hRsN
  refine ⟨d.Rstar_le_Y hRs hRsN, ⟨(r * t)⁻¹ * v * (r * t)⁻¹⁻¹, ?_, ?_, ?_⟩, ?_⟩
  · rw [← AscL62.conjSub_zpowers_eq, d.Rstar_inf_eq hRs hRsN]
  · rw [← AscL62.conjSub_zpowers_eq]
    exact d.Ustar_mem_USet
  · rw [← AscL62.conjSub_zpowers_eq]
    exact d.UV_eq
  · intro r' hr' hru' rs hrs hrsj
    have d' : Cfg64D Ω K J z j u v R T N₀K N₀J r' t := ⟨c, hK0, hJ0, hr', hru', ht, htv⟩
    have hKs : conjSub (r' * t)⁻¹ J = conjSub (r * t)⁻¹ J := by
      have hmem : conjSub (r' * t)⁻¹ J ∈ twinSet Ω K :=
        ⟨d'.Kstar_mem, z, hz, d'.isUniqueInvolution_J'⟩
      rw [htw] at hmem
      rcases hmem with h | h
      · exact absurd h (d'.Kstar_ne hA)
      · exact h
    rw [← hKs] at hRs
    exact ⟨d'.rrstar_inv (d'.Kstar_ne hA) hRs hRsN hrs hrsj,
      d'.centralizer_Z_eq hA hRs hRsN hrs hrsj⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
