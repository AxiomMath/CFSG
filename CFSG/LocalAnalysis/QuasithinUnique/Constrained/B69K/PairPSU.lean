module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Pair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSUTorus

public section

namespace CFSG.Quasithin

namespace B69K

open CFSG.QuasithinUnique CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

theorem psu_finrank_hypFlag {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) : Module.finrank K (hypFlag h r ε d) = d := by
  have hd' : d ≤ 2 * r + ε := by omega
  rw [hypFlag_eq_posFlag h hε hd']
  exact finrank_posFlag hd

theorem psu_hypFlag_isotropic {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) :
    ∀ x ∈ hypFlag h r ε d, ∀ y ∈ hypFlag h r ε d, hypForm h r ε x y = 0 := by
  have hd' : d ≤ 2 * r + ε := by omega
  rw [hypFlag_eq_posFlag h hε hd']
  exact posFlag_isotropic h hd

theorem psu_flag_separator {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    ∃ g : hypSU h r ε, g ∉ isoStabilizer h r ε (hypFlag h r ε d) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ r → j ≠ d → g ∈ isoStabilizer h r ε (hypFlag h r ε j) := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hgen := (unitary_subflag_generation (r := r) (ε := ε) (I := Set.Icc 1 r \ {d}) h hr hε
    hc hc0 Set.sdiff_subset).2.2 (hypFlag h r ε d)
  have hex : ∃ g ∈ flagStabilizer h r ε (Set.Icc 1 r \ {d}),
      g • hypFlag h r ε d ≠ hypFlag h r ε d := by
    by_contra hcon
    have hinv : ∀ g ∈ flagStabilizer h r ε (Set.Icc 1 r \ {d}),
        g • hypFlag h r ε d = hypFlag h r ε d :=
      fun g hg => Classical.byContradiction fun hne => hcon ⟨g, hg, hne⟩
    rcases hgen.mp ⟨psu_hypFlag_isotropic h hε hdr, hinv⟩ with h0 | ⟨i, hi, hie⟩
    · have h1 := psu_finrank_hypFlag h hε hdr
      have h2 := psu_finrank_hypFlag h hε (Nat.zero_le r)
      rw [h0, h2] at h1
      omega
    · obtain ⟨⟨-, hir⟩, hid⟩ := hi
      have h1 := psu_finrank_hypFlag h hε hdr
      have h2 := psu_finrank_hypFlag h hε hir
      rw [hie, h2] at h1
      exact hid (Set.mem_singleton_iff.mpr h1)
  obtain ⟨g, hg, hgne⟩ := hex
  refine ⟨g, fun hmem => hgne (mem_isoStabilizer.mp hmem), fun j hj1 hjr hjd => ?_⟩
  exact mem_isoStabilizer.mpr
    (mem_flagStabilizer.mp hg j ⟨⟨hj1, hjr⟩, fun hm => hjd (Set.mem_singleton_iff.mp hm)⟩)

theorem psu_index_ne {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (hr : 2 ≤ r) (hε : ε ≤ 1) :
    (projIsoStabilizer h r ε (hypFlag h r ε 1)).index ≠
      (projIsoStabilizer h r ε (hypFlag h r ε 2)).index := by
  intro heq
  have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := h.one_le; omega) 2
  obtain ⟨hp1, hi1, -⟩ := isotropic_stabilizer_index h (hypFlag h r ε 1)
    (psu_hypFlag_isotropic h hε (show 1 ≤ r by omega))
  obtain ⟨hp2, hi2, -⟩ := isotropic_stabilizer_index h (hypFlag h r ε 2)
    (psu_hypFlag_isotropic h hε hr)
  rw [psu_finrank_hypFlag h hε (show 1 ≤ r by omega)] at hi1
  rw [psu_finrank_hypFlag h hε hr] at hi2
  have hnat : (isoStabilizer h r ε (hypFlag h r ε 1)).index =
      (isoStabilizer h r ε (hypFlag h r ε 2)).index := hp1.symm.trans (heq.trans hp2)
  have hQ : isoIndexCount (2 ^ f) (2 * r + ε) 1 = isoIndexCount (2 ^ f) (2 * r + ε) 2 := by
    rw [← hi1, ← hi2, hnat]
  rcases Nat.lt_or_ge (2 * r + ε) 5 with hn | hn
  · have hn4 : 2 * r + ε = 4 := by omega
    have hlt := ((isotropic_index_comparison (n := 2 * r + ε) hq).2.2.1 hn4).2.2
    rw [hn4] at hQ
    rw [hQ] at hlt
    exact lt_irrefl _ hlt
  · have hlt := (isotropic_index_comparison (n := 2 * r + ε) hq).2.1 hn 2 le_rfl (by omega)
    rw [hQ] at hlt
    exact lt_irrefl _ hlt

theorem parabolicPair_hypPSU {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (r ε : ℕ)
    (hr : 2 ≤ r) (hε : ε ≤ 1) :
    ∃ U : Subgroup (hypPSU h r ε), IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  haveI : Finite K := h.finite
  haveI : Finite (hypPSU h r ε) := inferInstance
  have hr1 : 1 ≤ r := by omega
  obtain ⟨-, -, -, -, ⟨P0, hP0⟩, -⟩ := unitary_order_and_Sylow h (r := r) (ε := ε) hr1 hε
  have hU0 : IsSylowTwoOf (hypProjUnitriangular h r ε) ⊤ := by
    rw [← hP0]
    exact CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P0
  have hUP : ∀ d : ℕ, 1 ≤ d → d ≤ r →
      hypProjUnitriangular h r ε ≤ projIsoStabilizer h r ε (hypFlag h r ε d) := fun d hd hdn =>
    (Subgroup.map_mono (hypUnitriangular_le_hypBorel h (r := r) (ε := ε))).trans
      (hypProjBorel_le_projIsoStabilizer h hd hdn (ε := ε))
  refine ⟨hypProjUnitriangular h r ε, hU0, ?_⟩
  refine parabolicPair_of_coatoms
    (Ps := (fun d : ℕ => projIsoStabilizer h r ε (hypFlag h r ε d)) '' {d | 1 ≤ d ∧ d ≤ r})
    ?_ ?_ ?_ ?_
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact ⟨isCoatom_projIsoStabilizer_hypFlag h hr1 hε hd hdn, hUP d hd hdn⟩
  · intro A hUA hA
    obtain ⟨d, hd, hdn, hAd⟩ := CFSG.Quasithin.LieOver.psuCover_all_of_torus
      CFSG.Quasithin.LieOver.psuTorusOvergroup_holds f K h r ε hr hε A hA hUA
    exact ⟨projIsoStabilizer h r ε (hypFlag h r ε d), ⟨d, ⟨hd, hdn⟩, rfl⟩, hAd⟩
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    obtain ⟨g, hg, hgj⟩ := psu_flag_separator h hr1 hε hd hdn
    refine ⟨hypProj h r ε g, ?_, ?_⟩
    · intro hmem
      have hmem' : g ∈ (projIsoStabilizer h r ε (hypFlag h r ε d)).comap (hypProj h r ε) := hmem
      rw [comap_projIsoStabilizer] at hmem'
      exact hg hmem'
    · rintro P' ⟨j, ⟨hj, hjn⟩, rfl⟩ hne
      have hjd : j ≠ d := fun h' => hne (by rw [h'])
      exact Subgroup.mem_map_of_mem (hypProj h r ε) (hgj j hj hjn hjd)
  · exact ⟨projIsoStabilizer h r ε (hypFlag h r ε 1), ⟨1, ⟨le_rfl, hr1⟩, rfl⟩,
      projIsoStabilizer h r ε (hypFlag h r ε 2), ⟨2, ⟨by norm_num, hr⟩, rfl⟩,
      psu_index_ne h hr hε⟩

end B69K

end CFSG.Quasithin
