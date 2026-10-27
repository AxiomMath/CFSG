module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_conjugate_conjugate (K : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate K a) b = CFSG.conjugate K (a * b) := by
  ext g
  rw [sec63P_mem_conjugate_iff, sec63P_mem_conjugate_iff, sec63P_mem_conjugate_iff]
  have h : a * (b * g * b⁻¹) * a⁻¹ = a * b * g * (a * b)⁻¹ := by group
  rw [h]

theorem l34g_conjugate_conjugate_self (K : Subgroup G) {a : G} (ha : orderOf a = 2) :
    CFSG.conjugate (CFSG.conjugate K a) a = K := by
  rw [l34g_conjugate_conjugate, sec63P_mul_self ha]
  ext g
  rw [sec63P_mem_conjugate_iff]
  simp

theorem l34g_isComponentIn_conjugate_centralizer {u : G} {I : Subgroup G}
    (h : IsComponentIn I (centralizer ({u} : Set G))) (g : G) :
    IsComponentIn (CFSG.conjugate I g) (centralizer ({g⁻¹ * u * g} : Set G)) := by
  have h' := h.map_mulEquiv (MulAut.conj g⁻¹)
  change IsComponentIn (CFSG.conjugate I g) (CFSG.conjugate (centralizer ({u} : Set G)) g) at h'
  rwa [conjugate_centralizer_singleton u g] at h'

theorem l34g_isComponentIn_conjugate_of_mem_normalizer {K H : Subgroup G}
    (h : IsComponentIn K H) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    IsComponentIn (CFSG.conjugate K g) H := by
  have h' := h.map_mulEquiv (MulAut.conj g⁻¹)
  change IsComponentIn (CFSG.conjugate K g) (CFSG.conjugate H g) at h'
  rwa [sec63P_conjugate_eq_iff.mpr hg] at h'

end CFSG.OddStandard.SmallF3.Omega
