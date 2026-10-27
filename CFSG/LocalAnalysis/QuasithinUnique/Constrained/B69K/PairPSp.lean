module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Pair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherIntrinsicPoints

public section

namespace CFSG.Quasithin

namespace B69K

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial

theorem flag_inj {r : ℕ} {K : Type} [Field K] {d i : ℕ} (hd : d ≤ r) (hi : i ≤ r)
    (h : SymplecticFlag.flag r K d = SymplecticFlag.flag r K i) : d = i := by
  have h' : Module.finrank K (SymplecticFlag.flag r K d) =
      Module.finrank K (SymplecticFlag.flag r K i) := by rw [h]
  rwa [SymplecticHigher.finrank_flag (r := r) (K := K) (i := d) (by omega),
    SymplecticHigher.finrank_flag (r := r) (K := K) (i := i) (by omega)] at h'

theorem exists_stabilizer_not_mem {r : ℕ} {K : Type} [Field K] {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    ∃ x : StatedSp r K,
      (∀ j : ℕ, 1 ≤ j → j ≤ r → j ≠ d →
        x ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.flag r K j)) ∧
        x ∉ SymplecticFlag.stabilizer r K (SymplecticFlag.flag r K d) := by
  have hI : ∀ i ∈ {j : ℕ | 1 ≤ j ∧ j ≤ r ∧ j ≠ d}, i ≤ r := fun i hi => hi.2.1
  have hnle : ¬ (SymplecticHigher.flagStabilizer r K {j : ℕ | 1 ≤ j ∧ j ≤ r ∧ j ≠ d} ≤
      SymplecticFlag.stabilizer r K (SymplecticFlag.flag r K d)) := by
    intro hle
    have key := (SymplecticHigher.subflag_generation (K := K)
      {j : ℕ | 1 ≤ j ∧ j ≤ r ∧ j ≠ d} hI).2.2 (SymplecticFlag.flag r K d)
      (CFSG.Quasithin.LieOver.ld_isTI hdr)
    rcases key.mp hle with h0 | ⟨i, hiI, hi⟩
    · have := flag_inj hdr (Nat.zero_le r) h0
      omega
    · exact hiI.2.2 (flag_inj hdr hiI.2.1 hi).symm
  obtain ⟨x, hxI, hxd⟩ : ∃ x, x ∈ SymplecticHigher.flagStabilizer r K {j : ℕ | 1 ≤ j ∧ j ≤ r ∧ j ≠ d} ∧
      x ∉ SymplecticFlag.stabilizer r K (SymplecticFlag.flag r K d) := by
    by_contra hcon
    push_neg at hcon
    exact hnle fun x hx => hcon x hx
  exact ⟨x, fun j hj1 hjr hjd => (SymplecticHigher.mem_flagStabilizer.mp hxI) j ⟨hj1, hjr, hjd⟩, hxd⟩

theorem parabolicPair_projectiveSp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r) :
    ∃ U : Subgroup (StatedProj (StatedSp r K)), IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  have : Finite (StatedProj (StatedSp r K)) := inferInstance
  obtain ⟨P0, hP0⟩ := SymplecticFlag.exists_sylow_projUnipotent (K := K) 2 (by omega : 1 ≤ r)
  have hU0 : IsSylowTwoOf (SymplecticFlag.projUnipotent r K) ⊤ :=
    hP0 ▸ CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P0
  have hUP : ∀ d : ℕ, 1 ≤ d → d ≤ r →
      SymplecticFlag.projUnipotent r K ≤
        SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d) := fun d _ hdr =>
    Subgroup.map_mono ((SymplecticFlag.unipotent_le_borelSubgroup (r := r) (K := K)).trans
      (SymplecticHigher.borelSubgroup_le_stabilizer_flag hdr))
  refine ⟨SymplecticFlag.projUnipotent r K, hU0, ?_⟩
  refine parabolicPair_of_coatoms
    (Ps := (fun d : ℕ => SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d)) ''
      {d | 1 ≤ d ∧ d ≤ r}) ?_ ?_ ?_ ?_
  · rintro P ⟨d, ⟨hd, hdr⟩, rfl⟩
    exact ⟨SymplecticHigher.isCoatom_projStabilizer_flag hd hdr, hUP d hd hdr⟩
  · intro A hUA hA
    obtain ⟨i, hi1, hin, hAi⟩ :=
      (CFSG.QuasithinUnique.Setup.X7a.symplectic_unitriangular_overgroup_subflag_containment
        (r := r) (K := K)).2 A hA hUA
    exact ⟨SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K i),
      ⟨i, ⟨hi1, hin⟩, rfl⟩, hAi⟩
  · rintro P ⟨d, ⟨hd, hdr⟩, rfl⟩
    obtain ⟨x, hxj, hxd⟩ := exists_stabilizer_not_mem (K := K) hd hdr
    refine ⟨SymplecticFlag.proj r K x, ?_, ?_⟩
    · intro h
      have h' : x ∈ (SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d)).comap
          (SymplecticFlag.proj r K) := h
      rw [SymplecticHigher.comap_projStabilizer] at h'
      exact hxd h'
    · rintro P' ⟨j, ⟨hj, hjr⟩, rfl⟩ hne
      have hjd : j ≠ d := fun h => hne (by rw [h])
      have h' : x ∈ (SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K j)).comap
          (SymplecticFlag.proj r K) := by
        rw [SymplecticHigher.comap_projStabilizer]
        exact hxj j hj hjr hjd
      exact h'
  · refine ⟨SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 1),
      ⟨1, ⟨le_rfl, by omega⟩, rfl⟩,
      SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 2),
      ⟨2, ⟨by norm_num, by omega⟩, rfl⟩, ?_⟩
    intro h
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    have h1 := SymplecticHigher.index_projStabilizer_eq_isoGaussian (K := K) (r := r) rfl
      (CFSG.Quasithin.LieOver.ld_isTI (K := K) (r := r) (d := 1) (by omega))
    have h2 := SymplecticHigher.index_projStabilizer_eq_isoGaussian (K := K) (r := r) rfl
      (CFSG.Quasithin.LieOver.ld_isTI (K := K) (r := r) (d := 2) (by omega))
    rw [SymplecticHigher.finrank_flag (r := r) (K := K) (i := 1) (by omega)] at h1
    rw [SymplecticHigher.finrank_flag (r := r) (K := K) (i := 2) (by omega)] at h2
    have hg : SymplecticHigher.isoGaussian r 1 (Nat.card K) <
        SymplecticHigher.isoGaussian r 2 (Nat.card K) :=
      SymplecticHigher.isotropic_gaussian_minimum hq hr (k := 2) (by norm_num) (by omega)
    have hcast : ((SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 1)).index : ℚ) =
        ((SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 2)).index : ℚ) := by
      rw [h]
    rw [h1, h2] at hcast
    exact (ne_of_lt hg) hcast

end B69K

end CFSG.Quasithin
