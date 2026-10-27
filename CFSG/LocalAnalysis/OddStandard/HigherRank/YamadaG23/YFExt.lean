module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YHyp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

private theorem cen_map_of_injective {P Q : Type} [Group P] [Group Q] (f : P →* Q)
    (hf : Function.Injective f) (X : Subgroup P) : cen (X.map f) = (cen X).map f := by
  ext y
  constructor
  · intro hy
    rw [cen, Subgroup.mem_inf] at hy
    obtain ⟨hyX, hyC⟩ := hy
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hyX
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [cen, Subgroup.mem_inf]
    refine ⟨hxX, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h : f (z * x) = f (x * z) := by
      rw [map_mul, map_mul]
      exact hyC (f z) (Subgroup.mem_map_of_mem f hz)
    exact hf h
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [cen, Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxX, hxC⟩ := hx
    refine ⟨Subgroup.mem_map_of_mem f hxX, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨z', hz'X, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxC z' hz'X]

private theorem isExtraspecialTwo_map_iff {P Q : Type} [Group P] [Group Q] (f : P →* Q)
    (hf : Function.Injective f) (X : Subgroup P) (n : ℕ) :
    IsExtraspecialTwo n (X.map f) ↔ IsExtraspecialTwo n X := by
  have hcard := Subgroup.card_map_of_injective (f := f) (K := X) hf
  have hcen := cen_map_of_injective f hf X
  have hcardC := Subgroup.card_map_of_injective (f := f) (K := cen X) hf
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hcard]; exact h1
    · rw [← hcardC, ← hcen]; exact h2
    · apply Subgroup.map_injective hf
      rw [Subgroup.map_commutator, ← hcen]
      exact h3
    · intro y hy
      have hmem : f (y ^ 2) ∈ cen (X.map f) := by
        rw [map_pow]
        exact h4 (f y) (Subgroup.mem_map_of_mem f hy)
      rw [hcen] at hmem
      obtain ⟨c, hc, hfc⟩ := Subgroup.mem_map.mp hmem
      rwa [← hf hfc]
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcard]; exact h1
    · rw [hcen, hcardC]; exact h2
    · rw [← Subgroup.map_commutator, h3, ← hcen]
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_pow, hcen]
      exact Subgroup.mem_map_of_mem f (h4 x hx)

theorem isExtraspecialTwo_conjSub {Γ : Type} [Group Γ] {n : ℕ} (x : Γ) {X : Subgroup Γ}
    (h : IsExtraspecialTwo n X) : IsExtraspecialTwo n (conjSub x X) := by
  rw [conjSub]
  exact (isExtraspecialTwo_map_iff (MulAut.conj x).toMonoidHom (MulAut.conj x).injective X n).mpr h

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem s3_A_extraspecial {s : Setting3 G L} (hA : LFactsA s) : IsExtraspecialTwo 2 s.fr.A := by
  have hcardZ : Nat.card ↥s.fr.Z = 2 := by
    rw [SFrame.Z, Nat.card_zpowers, hA.z_order]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA.card_A]; norm_num
  · rw [hA.cen_A]; exact hcardZ
  · rw [hA.cen_A]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      exact fun a ha b hb => hA.comm_A a ha b hb
    · obtain ⟨a, ha, b, hb, hab⟩ := hA.nonab_A
      have hne : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_commute.mp h)
      have hmem : ⁅a, b⁆ ∈ ⁅s.fr.A, s.fr.A⁆ := Subgroup.commutator_mem_commutator ha hb
      have hZmem : ⁅a, b⁆ ∈ s.fr.Z := hA.comm_A a ha b hb
      rw [SFrame.Z] at hZmem
      have hz : s.fr.z ∈ ⁅s.fr.A, s.fr.A⁆ := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hZmem
        have hmod := zpow_mod_orderOf s.fr.z k
        rw [hA.z_order] at hmod
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · exfalso
          have hk1 : s.fr.z ^ k = 1 := by
            rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
            simp
          exact hne (hk ▸ hk1)
        · have hk1 : s.fr.z ^ k = s.fr.z := by
            rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
            simp
          rw [← hk1, hk]
          exact hmem
      rw [SFrame.Z]
      exact Subgroup.zpowers_le.mpr hz
  · intro y hy
    rw [hA.cen_A]
    exact hA.sq_A y hy

theorem s3_A_unique (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {X : Subgroup G} (hX : X ≤ s.fr.S) (hXe : IsExtraspecialTwo 2 X) :
    X = s.fr.A := by
  have hA_le_S : s.fr.A ≤ s.fr.S :=
    Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hXe' : IsExtraspecialTwo 2 ((X.subgroupOf s.fr.S).map s.fr.S.subtype) := by
    rwa [Subgroup.map_subgroupOf_eq_of_le hX]
  have hX₀ : IsExtraspecialTwo 2 (X.subgroupOf s.fr.S) :=
    (isExtraspecialTwo_map_iff s.fr.S.subtype s.fr.S.subtype_injective
      (X.subgroupOf s.fr.S) 2).mp hXe'
  have hXmap : IsExtraspecialTwo 2 ((X.subgroupOf s.fr.S).map (jOn L (s3_S_le_N s))) :=
    (isExtraspecialTwo_map_iff (jOn L (s3_S_le_N s)) (s3_jOn_S_injective s hS hZ)
      (X.subgroupOf s.fr.S) 2).mpr hX₀
  have hmap : (X.subgroupOf s.fr.S).map (jOn L (s3_S_le_N s)) = jSub L X := by
    ext α
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_jSub L).mpr ⟨(x : G), Subgroup.mem_subgroupOf.mp hx,
        jOn_actsAs L (s3_S_le_N s) x⟩
    · intro hα
      obtain ⟨g, hgX, hgα⟩ := (mem_jSub L).mp hα
      rw [Subgroup.mem_map]
      refine ⟨⟨g, hX hgX⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hgX
      · exact actsAs_unique L (jOn_actsAs L (s3_S_le_N s) ⟨g, hX hgX⟩) hgα
  rw [hmap] at hXmap
  obtain ⟨-, -, -, -, -, -, huniq⟩ := s.facts.2.2.2.1.2.1
  have hjeq : jSub L X = s.fr'.A :=
    huniq (jSub L X) ((jSub_mono L hX).trans (le_of_eq (s3_jSub_S s))) hXmap
  have hjeqA : jSub L X = jSub L s.fr.A := hjeq.trans (s3_jSub_A s).symm
  refine le_antisymm ?_ ?_
  · intro x hx
    have hφx : jOn L (s3_S_le_N s) ⟨x, hX hx⟩ ∈ jSub L X :=
      hmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [hjeqA] at hφx
    obtain ⟨a, ha, hact⟩ := (mem_jSub L).mp hφx
    have hxa : x = a := s3_inj_on_S s hS hZ (hX hx) (hA_le_S ha)
      (jOn_actsAs L (s3_S_le_N s) ⟨x, hX hx⟩) hact
    rw [hxa]; exact ha
  · intro a ha
    have hφa : jOn L (s3_S_le_N s) ⟨a, hA_le_S ha⟩ ∈ jSub L s.fr.A :=
      (mem_jSub L).mpr ⟨a, ha, jOn_actsAs L (s3_S_le_N s) ⟨a, hA_le_S ha⟩⟩
    rw [← hjeqA] at hφa
    obtain ⟨x, hx, hact⟩ := (mem_jSub L).mp hφa
    have hax : a = x := s3_inj_on_S s hS hZ (hA_le_S ha) (hX hx)
      (jOn_actsAs L (s3_S_le_N s) ⟨a, hA_le_S ha⟩) hact
    rw [hax]; exact hx

end CFSG.OddStandard.HigherRank.YamadaG23
