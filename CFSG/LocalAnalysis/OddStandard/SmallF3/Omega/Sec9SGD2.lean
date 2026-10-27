module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec9g_simHasType_of_simHasDim (hQ : Q.Nondegenerate)
    (h6 : Module.finrank (ZMod 3) V = 6) {x : ProjSim Q} {r : ℕ} (hr1 : 1 ≤ r) (hr5 : r ≤ 5)
    (h : SimHasDim x r) : ∃ α : ℤˣ, SimHasType x r α := by
  obtain ⟨t, htt, htr, htx⟩ := h
  have ht_ne : toProj Q t ≠ 1 := by
    intro h1
    have hmem : t ∈ piGroup Q := (QuotientGroup.eq_one_iff t).mp h1
    rcases mem_piGroup_iff.mp hmem with h1 | hpi
    · have h0 : invDim t = 0 := by
        rw [h1]
        exact congrArg Prod.fst invType_one
      omega
    · have hd : invDim t = 6 := by
        rw [hpi]
        have := congrArg Prod.fst (invType_piOrth hQ)
        simpa only [invType, h6] using this
      omega
  refine ⟨invSign t, toProj Q t, htx, ht_ne, t, htt, ?_, rfl⟩
  simp only [invType]
  rw [htr]

theorem sec9g_i1_of_coset (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    (F : Subgroup (ProjSim Q)) (hF16 : Nat.card F = 2 ^ 4)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4)
    {u : ProjSim Q} (hu : ∀ f ∈ F, u * f = f * u) (hnot : u ∉ F) :
    ∃ f ∈ F, SimHasDim (u * f) 1 := by
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
  obtain ⟨g1, T1, hg1phi, hg1act⟩ := sec9t_lift_diag hQ h6 hb hn hsq hev hu'
  have hT1odd : Odd T1.card := by
    rw [← Nat.not_even_iff_odd]
    intro hT1even
    have hg1mem : g1 ∈ Ft := (IsEvenFrame.mem_iff hb).mpr ⟨T1, hT1even, hg1act⟩
    exact hnot (by rw [← hg1phi]; exact Subgroup.mem_comap.mp hg1mem)
  let i0 : Fin (Module.finrank (ZMod 3) V) := ⟨0, by omega⟩
  let S : Finset (Fin (Module.finrank (ZMod 3) V)) := symmDiff T1 {i0}
  have hSeven : Even S.card := by
    have hT1not : ¬ Even T1.card := Nat.not_even_iff_odd.mpr hT1odd
    have h1not : ¬ Even ({i0} : Finset (Fin (Module.finrank (ZMod 3) V))).card := by
      rw [Finset.card_singleton]
      norm_num
    rw [Finset.even_card_symmDiff_iff]
    exact ⟨fun h => absurd h hT1not, fun h => absurd h h1not⟩
  obtain ⟨g', hg'mem, hg'act⟩ := hb.2 S hSeven
  have hS : symmDiff T1 S = {i0} := by
    simp only [S, symmDiff_symmDiff_cancel_left]
  have hprod : ∀ i, ((g1 * g' : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) =
      (if i ∈ ({i0} : Finset (Fin (Module.finrank (ZMod 3) V))) then
        (-1 : ZMod 3) else 1) • b i := by
    intro i
    have h := sec9g_mul_diag hg1act hg'act i
    rwa [hS] at h
  refine ⟨phiSim Q g', Subgroup.mem_comap.mp hg'mem, g1 * g', sec9g_mul_self_diag hprod, ?_, ?_⟩
  · rw [sec9g_invDim_diag hprod, Finset.card_singleton]
  · change projOrthToProjSim Q (toProj Q (g1 * g')) = u * phiSim Q g'
    rw [← hg1phi, ← map_mul]
    rfl

end CFSG.OddStandard.SmallF3.Omega
