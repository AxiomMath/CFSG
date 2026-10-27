module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sign_mul_symmDiff {n : ℕ} (T1 T2 : Finset (Fin n)) (i : Fin n) :
    ((if i ∈ T1 then (-1 : ZMod 3) else 1) * (if i ∈ T2 then (-1 : ZMod 3) else 1)) =
      (if i ∈ symmDiff T1 T2 then -1 else 1) := by
  by_cases h1 : i ∈ T1 <;> by_cases h2 : i ∈ T2 <;>
    simp [Finset.mem_symmDiff, h1, h2]

private lemma coe_inv_sign {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {T : Finset (Fin n)}
    {g : OGroup Q}
    (h : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i)
    (i : Fin n) :
    ((g⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i := by
  rw [Subgroup.coe_inv]
  show ((g : V ≃ₗ[ZMod 3] V)).symm (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i
  rw [LinearEquiv.symm_apply_eq, map_smul, h i]
  by_cases hi : i ∈ T <;> simp [hi, smul_smul]

theorem sec9t_cosets (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    (F : Subgroup (ProjSim Q)) (hF16 : Nat.card F = 2 ^ 4)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4)
    {u v : ProjSim Q} (hu : ∀ f ∈ F, u * f = f * u) (hv : ∀ f ∈ F, v * f = f * v) :
    u ∈ F ∨ v ∈ F ∨ v⁻¹ * u ∈ F := by
  classical
  let Ft : Subgroup (OGroup Q) := F.comap (phiSim Q)
  obtain ⟨b, hb⟩ := sec9t_exists_evenFrame hQ h6 F hF16 hlift
  have hn : 3 ≤ Module.finrank (ZMod 3) V := by rw [h6]; norm_num
  have hlift' : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f := by
    intro f hf hne
    obtain ⟨t, htt, htf, -, -⟩ := hlift f hf hne
    exact ⟨t, htt, htf⟩
  have hsq : ∀ g ∈ Ft, g * g = 1 := sec9e_comap_sq F hlift'
  have hev : ∀ g ∈ Ft, Even (invDim g) := sec9e_invDim_even hQ h6 F hF16 hlift
  have hu' : ∀ g ∈ Ft, u * phiSim Q g = phiSim Q g * u := by
    intro g hg
    exact hu (phiSim Q g) (Subgroup.mem_comap.mp hg)
  have hv' : ∀ g ∈ Ft, v * phiSim Q g = phiSim Q g * v := by
    intro g hg
    exact hv (phiSim Q g) (Subgroup.mem_comap.mp hg)
  obtain ⟨g1, T1, hg1phi, hg1act⟩ := sec9t_lift_diag hQ h6 hb hn hsq hev hu'
  obtain ⟨g2, T2, hg2phi, hg2act⟩ := sec9t_lift_diag hQ h6 hb hn hsq hev hv'
  by_cases hT1 : Even T1.card
  · left
    have hg1mem : g1 ∈ Ft := (IsEvenFrame.mem_iff hb).mpr ⟨T1, hT1, hg1act⟩
    rw [← hg1phi]
    exact Subgroup.mem_comap.mp hg1mem
  · by_cases hT2 : Even T2.card
    · right; left
      have hg2mem : g2 ∈ Ft := (IsEvenFrame.mem_iff hb).mpr ⟨T2, hT2, hg2act⟩
      rw [← hg2phi]
      exact Subgroup.mem_comap.mp hg2mem
    · right; right
      have hsymm : Even (symmDiff T1 T2).card := by simp [hT1, hT2]
      have hprod : ∀ i, ((g2⁻¹ * g1 : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) =
          (if i ∈ symmDiff T1 T2 then (-1 : ZMod 3) else 1) • b i := by
        intro i
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hg1act i, map_smul,
          coe_inv_sign hg2act i, smul_smul, sign_mul_symmDiff]
      have hgmem : g2⁻¹ * g1 ∈ Ft :=
        (IsEvenFrame.mem_iff hb).mpr ⟨symmDiff T1 T2, hsymm, hprod⟩
      have hphi : phiSim Q (g2⁻¹ * g1) = v⁻¹ * u := by
        rw [map_mul, map_inv, hg2phi, hg1phi]
      rw [← hphi]
      exact Subgroup.mem_comap.mp hgmem

end CFSG.OddStandard.SmallF3.Omega
