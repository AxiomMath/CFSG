module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Basic

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem Notation25.t_mem_centerOf_S (hf : Facts2511 N t zK) : t ∈ centerOf N.S := by
  have h : t ∈ Subgroup.closure ({t, N.z} : Set G) := Subgroup.subset_closure (by simp)
  rw [← hf.centerS_z] at h
  exact h

theorem Notation25.t_comm_of_mem_S (hf : Facts2511 N t zK) {s : G} (hs' : s ∈ N.S) :
    t * s = s * t :=
  (Subgroup.mem_centralizer_iff.mp (N.t_mem_centerOf_S hf).2 s hs').symm

theorem Notation25.t_mem_S (hf : Facts2511 N t zK) : t ∈ N.S := N.SC_le_S hf.t_mem

theorem Notation25.t_mem_centralizer_K (hf : Facts2511 N t zK) :
    t ∈ Subgroup.centralizer (N.K : Set G) :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.K_le_K0) hf.t_mem.2

theorem Notation25.t_mul_self' (hf : Facts2511 N t zK) : t * t = 1 := by
  have := hf.t_sq
  rwa [sq] at this

theorem Notation25.z_mul_self (hf : Facts2511 N t zK) : N.z * N.z = 1 := by
  have : N.z ^ 2 = 1 := by rw [← hf.z_order]; exact pow_orderOf_eq_one N.z
  rwa [sq] at this

theorem Notation25.t_mem_R (hf : Facts2511 N t zK) {i : G} (hiS : i ∈ N.S) :
    t ∈ Rgrp2519 N i :=
  ⟨⟨N.t_mem_S hf, Subgroup.mem_centralizer_singleton_iff.mpr (N.t_comm_of_mem_S hf hiS)⟩,
    N.t_mem_S hf, N.t_mem_centralizer_K hf⟩

theorem Hyp2519.mem_S {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) : i ∈ N.S := hi.1.1

theorem Hyp2519.mem_centralizer_K {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) :
    i ∈ Subgroup.centralizer (N.K : Set G) := hi.1.2

theorem Hyp2519.ne_one {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) : i ≠ 1 := hi.2.1

theorem Hyp2519.sq_eq_one {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) : i ^ 2 = 1 := hi.2.2.1

theorem Hyp2519.mul_self {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) : i * i = 1 := by
  have := hi.sq_eq_one
  rwa [_root_.sq] at this

theorem Hyp2519.not_comp {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) :
    ¬ IsComponentIn N.K (Subgroup.centralizer ({i} : Set G)) := hi.2.2.2

theorem Hyp2519.mem_R {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) : i ∈ Rgrp2519 N i :=
  ⟨⟨hi.mem_S, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, hi.mem_S, hi.mem_centralizer_K⟩

theorem Rgrp2519_le_S (N : Notation25 hs) (i : G) : Rgrp2519 N i ≤ N.S :=
  inf_le_left.trans inf_le_left

theorem Rgrp2519_isPGroup (N : Notation25 hs) (i : G) : IsPGroup 2 (Rgrp2519 N i) :=
  N.tuple.sylow.isPGroup.to_le (Rgrp2519_le_S N i)

theorem Rgrp2519_le_centralizer (N : Notation25 hs) (i : G) :
    Rgrp2519 N i ≤ Subgroup.centralizer ({i} : Set G) :=
  inf_le_left.trans inf_le_right

theorem Rgrp2519_le_centralizer_K (N : Notation25 hs) (i : G) :
    Rgrp2519 N i ≤ Subgroup.centralizer (N.K : Set G) :=
  inf_le_right.trans inf_le_right

theorem Notation25.closure_le_R (hf : Facts2511 N t zK) {i : G} (hi : Hyp2519 N i) :
    Subgroup.closure ({t, i} : Set G) ≤ Rgrp2519 N i := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact N.t_mem_R hf hi.mem_S
  · exact hi.mem_R

theorem Hyp2519.ne_t {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) (h : Lv2518 N t zK) :
    i ≠ t := by
  rintro rfl
  exact hi.not_comp h.concl2518.1

theorem Hyp2519.card_closure {N : Notation25 hs} {i : G} (hi : Hyp2519 N i) (h : Lv2518 N t zK) :
    Nat.card (Subgroup.closure ({t, i} : Set G)) = 4 :=
  card_closure_pair (N.t_mul_self' h.facts2511) hi.mul_self
    (N.t_comm_of_mem_S h.facts2511 hi.mem_S) h.facts2511.t_ne_one hi.ne_one (hi.ne_t h).symm

theorem Hyp2519.not_mem_centerOf_S {N : Notation25 hs} {i : G} (hi : Hyp2519 N i)
    (h : Lv2518 N t zK) : i ∉ centerOf N.S := by
  intro hZ
  have hf := h.facts2511
  have hiK0 : N.K0 ≤ Subgroup.centralizer ({i} : Set G) := by
    refine iSup_le fun s => ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcs : (s : G) * i = i * s := Subgroup.mem_centralizer_iff.mp hZ.2 (s : G) s.2
    have hyi : y * i = i * y := Subgroup.mem_centralizer_iff.mp hi.mem_centralizer_K y hy
    have hcs' : (s : G)⁻¹ * i = i * (s : G)⁻¹ := by
      calc (s : G)⁻¹ * i = (s : G)⁻¹ * (i * s) * (s : G)⁻¹ := by group
        _ = (s : G)⁻¹ * (s * i) * (s : G)⁻¹ := by rw [hcs]
        _ = i * (s : G)⁻¹ := by group
    show (s : G) * y * (s : G)⁻¹ * i = i * ((s : G) * y * (s : G)⁻¹)
    calc (s : G) * y * (s : G)⁻¹ * i = (s : G) * y * ((s : G)⁻¹ * i) := by group
      _ = (s : G) * y * (i * (s : G)⁻¹) := by rw [hcs']
      _ = (s : G) * (y * i) * (s : G)⁻¹ := by group
      _ = (s : G) * (i * y) * (s : G)⁻¹ := by rw [hyi]
      _ = ((s : G) * i) * y * (s : G)⁻¹ := by group
      _ = (i * (s : G)) * y * (s : G)⁻¹ := by rw [hcs]
      _ = i * ((s : G) * y * (s : G)⁻¹) := by group
  have hiSC : i ∈ N.SC := ⟨hi.mem_S, fun y hy => (hiK0 hy |> Subgroup.mem_centralizer_singleton_iff.mp)⟩
  have hzS : N.z ∈ centerOf N.S := by
    rw [hf.centerS_z]; exact Subgroup.subset_closure (by simp)
  have hcomm : t * N.z = N.z * t := N.t_comm_of_mem_S hf N.z_mem_S
  have hmem : i ∈ Subgroup.closure ({t, N.z} : Set G) := by rw [← hf.centerS_z]; exact hZ
  rcases mem_closure_pair_of_involutions (N.t_mul_self' hf) (N.z_mul_self hf) hcomm hmem with
    h1 | h1 | h1 | h1
  · exact hi.ne_one h1
  · exact hi.ne_t h h1
  · exact h.facts254.z_not_mem (h1 ▸ hiSC)
  · apply h.facts254.z_not_mem
    have : N.z = t * i := by rw [h1, ← mul_assoc, N.t_mul_self' hf, one_mul]
    rw [this]
    exact N.SC.mul_mem hf.t_mem hiSC

end Basic

end CFSG.QuasithinUnique
