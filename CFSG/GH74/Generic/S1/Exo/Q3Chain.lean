module

public import CFSG.GH74.Generic.S1.Exo.Q3Blocks
public import CFSG.GH74.Generic.S1.Exo.Q3Norm
public import CFSG.GH74.Generic.S1.Exo.Q3Perf

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.Assembly.LowTwoRank CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem range_ι_eq {x : G} (D : LayerData x (StatedSL 4 F)) :
    D.ι.range = (liftL x D.K).map (centralizer ({x} : Set G)).subtype := by
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨D.ιC s, D.ιC_mem s, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨D.liftIso.symm ⟨l, hl⟩, ?_⟩
    have h1 : D.ιC (D.liftIso.symm ⟨l, hl⟩) = l := by
      change (((D.liftIso (D.liftIso.symm ⟨l, hl⟩)) : ↥(liftL x D.K)) :
        ↥(centralizer ({x} : Set G))) = _
      rw [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1

theorem blkA3_normalized {x c : G} (D : LayerData x (StatedSL 4 F)) (hF : Nat.card F = 3)
    (hDc : D.ι (linZ0 F) = c) (s : ↥(StatedSL 4 F)) (hs : D.ι s * c = c * D.ι s) :
    ∀ j ∈ blkA3 D, D.ι s * j * (D.ι s)⁻¹ ∈ blkA3 D := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  have hcomm : s * linZ0 F = linZ0 F * s := by
    apply D.ι_injective
    rw [map_mul, map_mul, hDc]
    exact hs
  have hn := (blkLin_conj_mem_of_comm h2 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) linZ0_mem_blkLin linZ0_mul_self (linZ0_ne_one h2)
    hcomm).2
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨s * m * s⁻¹, hn m hm, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem blkB3_normalized {x c : G} (D : LayerData x (StatedSL 4 F)) (hF : Nat.card F = 3)
    (hDc : D.ι (linZ0 F) = c) (s : ↥(StatedSL 4 F)) (hs : D.ι s * c = c * D.ι s) :
    ∀ j ∈ blkB3 D, D.ι s * j * (D.ι s)⁻¹ ∈ blkB3 D := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  have hcomm : s * linZ0 F = linZ0 F * s := by
    apply D.ι_injective
    rw [map_mul, map_mul, hDc]
    exact hs
  have hn := (blkLin_conj_mem_of_comm h2 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) linZ0_mem_blkLin linZ0_mul_self (linZ0_ne_one h2)
    hcomm).1
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨s * m * s⁻¹, hn m hm, ?_⟩
  rw [map_mul, map_mul, map_inv]

omit [Finite F] in
theorem subnormal_of_normalized {x c : G} (D : LayerData x (StatedSL 4 F)) (hxc : x ∈ centralizer ({c} : Set G))
    {J : Subgroup G} (hJc : J ≤ centralizer ({c} : Set G)) (hJr : J ≤ D.ι.range)
    (hJn : ∀ s : ↥(StatedSL 4 F), D.ι s * c = c * D.ι s → ∀ j ∈ J, D.ι s * j * (D.ι s)⁻¹ ∈ J) :
    ((J.subgroupOf (centralizer ({c} : Set G))).subgroupOf
      (centralizer ({(⟨x, hxc⟩ : ↥(centralizer ({c} : Set G)))} :
        Set ↥(centralizer ({c} : Set G))))).IsSubnormal := by
  classical
  have hn := D.normal
  set C : Subgroup G := centralizer ({c} : Set G) with hC
  set Rg : Subgroup G := D.ι.range ⊓ C with hRg
  refine isSubnormal_subgroupOf_of_two_step (J := J.subgroupOf C) (R := Rg.subgroupOf C) (fun j hj => ?_) ?_ ?_
  · exact ⟨hJr hj, hJc hj⟩
  · intro r hr j hj
    have hr' : (r : G) ∈ Rg := hr
    obtain ⟨⟨s, hs⟩, hrC⟩ := hr'
    have hcomm : D.ι s * c = c * D.ι s := by
      rw [hs]
      exact mem_centralizer_singleton_iff.1 hrC
    have hj' : (j : G) ∈ J := hj
    have := hJn s hcomm _ hj'
    rw [hs] at this
    exact this
  · intro t ht r hr
    have hr' : (r : G) ∈ Rg := hr
    obtain ⟨hrr, hrC⟩ := hr'
    have htx : (t : G) ∈ centralizer ({x} : Set G) := by
      have := mem_centralizer_singleton_iff.1 ht
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hrL : (r : G) ∈ (liftL x D.K).map (centralizer ({x} : Set G)).subtype := by
      rw [← range_ι_eq]
      exact hrr
    obtain ⟨l, hl, hlr⟩ := hrL
    have hLn : (liftL x D.K).Normal := liftL_normal
    have hconj := hLn.conj_mem l hl ⟨(t : G), htx⟩
    have hmem : (t : G) * (r : G) * (t : G)⁻¹ ∈ D.ι.range := by
      rw [range_ι_eq]
      refine ⟨⟨(t : G), htx⟩ * l * ⟨(t : G), htx⟩⁻¹, hconj, ?_⟩
      have hlr' : ((l : ↥(centralizer ({x} : Set G))) : G) = (r : G) := hlr
      change (t : G) * (l : G) * (t : G)⁻¹ = _
      rw [hlr']
    have hmemC : (t : G) * (r : G) * (t : G)⁻¹ ∈ C := by
      have h1 : (t : G) ∈ C := t.2
      have h2 : (r : G) ∈ C := r.2
      exact C.mul_mem (C.mul_mem h1 h2) (C.inv_mem h1)
    show ((t * r * t⁻¹ : ↥C) : G) ∈ Rg
    exact ⟨hmem, hmemC⟩

theorem resCent_eq_bot_q3 {x c : G} (D : LayerData x (StatedSL 4 F)) (hF : Nat.card F = 3)
    (hDc : D.ι (linZ0 F) = c) : resCent ({x, c} : Set G) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  set P : Subgroup G := resCent ({x, c} : Set G) with hP
  have hPperf : ⁅P, P⁆ = P := resCent_perfect _
  have hPC : P ≤ centralizer ({x, c} : Set G) := resCent_le _
  have hPy : P ≤ centralizer ({x} : Set G) := fun p hp =>
    centralizer_le (Set.singleton_subset_iff.2 (by simp)) (hPC hp)
  have hPw : P ≤ centralizer ({c} : Set G) := fun p hp =>
    centralizer_le (Set.singleton_subset_iff.2 (by simp)) (hPC hp)
  have hrange := D.le_range_ι hPperf hPy
  set P' : Subgroup ↥(StatedSL 4 F) := P.comap D.ι with hP'
  have hmapP : P'.map D.ι = P := by
    rw [hP', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective D.ι_injective
    rw [Subgroup.map_commutator, hmapP, hPperf]
  have hP'comm : ∀ g ∈ P', g * linZ0 F = linZ0 F * g := by
    intro g hg
    have h1 : D.ι g ∈ centralizer ({c} : Set G) := hPw hg
    have h2' := mem_centralizer_singleton_iff.1 h1
    rw [← hDc] at h2'
    apply D.ι_injective
    rw [map_mul, map_mul]
    exact h2'
  have hbot := perfect_commute_z0_eq_bot hF linZ0_mem_blkLin linZ0_mul_self (linZ0_ne_one h2) P' hP'comm hP'perf
  rw [← hmapP, hbot, Subgroup.map_bot]

end CFSG.GH74.Generic.S1.Exo
