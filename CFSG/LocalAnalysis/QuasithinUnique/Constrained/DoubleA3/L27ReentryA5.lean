module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L27Reentry
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDA5

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppD
  CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem eq_top_of_Dstd_le {Z : Subgroup (Perm (Fin 5))} (hD : Dstd ≤ Z)
    (hc : swap (2 : Fin 5) 3 * swap 3 4 ∈ Z) : Z = ⊤ := by
  have h01 : swap (0 : Fin 5) 1 ∈ Z := hD (Estd_le_Dstd ((mem_Estd _).2 AppC.t1_mem_Eset))
  have h23 : swap (2 : Fin 5) 3 ∈ Z := hD (Estd_le_Dstd ((mem_Estd _).2 AppC.t2_mem_Eset))
  have hg3 : swap (0 : Fin 5) 2 * swap 1 3 ∈ Z := hD ((mem_Dstd _).2 (by decide +kernel))
  have h34 : swap (3 : Fin 5) 4 ∈ Z := by
    have e : swap (3 : Fin 5) 4 =
        (swap 2 3 * swap 3 4) * swap 2 3 * (swap 2 3 * swap 3 4)⁻¹ := by decide
    rw [e]
    exact mul_mem (mul_mem hc h23) (inv_mem hc)
  have h24 : swap (2 : Fin 5) 4 ∈ Z := by
    have e : swap (2 : Fin 5) 4 = swap 2 3 * swap 3 4 * swap 2 3 := by decide
    rw [e]
    exact mul_mem (mul_mem h23 h34) h23
  have h14 : swap (1 : Fin 5) 4 ∈ Z := by
    have e : swap (1 : Fin 5) 4 =
        (swap 0 2 * swap 1 3) * swap 3 4 * (swap 0 2 * swap 1 3)⁻¹ := by decide
    rw [e]
    exact mul_mem (mul_mem hg3 h34) (inv_mem hg3)
  have h12 : swap (1 : Fin 5) 2 ∈ Z := by
    have e : swap (1 : Fin 5) 2 = swap 2 4 * swap 1 4 * swap 2 4 := by decide
    rw [e]
    exact mul_mem (mul_mem h24 h14) h24
  have hcl : Submonoid.closure (Set.range fun i : Fin 4 => swap i.castSucc i.succ) ≤
      Z.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
    · exact h34
  rw [eq_top_iff]
  intro σ _
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 4 => swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact hcl hσ

section A5Main

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem A5.not_Ggrp_le_M (C : AppC.Cfg T M H S L) {x : G} {M₀ : Subgroup G} (m : GMate S T M₀ x)
    (F : GFour (GCfg.ofCfg C) x) : ¬ Ggrp F ≤ M := by
  have hcs := C.hcs
  have hLH : L ≤ H := C56.le_H hcs
  have hSH : S ≤ H := hcs.sylow.le
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := C56.H_le_normalizer hcs C.hj
  have hc3 : swap (2 : Fin 5) 3 * swap 3 4 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  obtain ⟨l₀, hl₀⟩ := C.P.hα ⟨_, hc3⟩
  have hlL : (l₀ : G) ∈ L := l₀.2
  have hlN : (l₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hlH : (l₀ : G) ∈ H := hLH hlL
  have hπl : C.P.π ⟨(l₀ : G), hlN⟩ = swap (2 : Fin 5) 3 * swap 3 4 := by
    have := C.P.hπα (l₀ : G) hlL
    rw [show (⟨(l₀ : G), hlL⟩ : ↥L) = l₀ from rfl, hl₀] at this
    exact this
  have hvS : F.v ∈ S := m.V_le_S (GCfg.ofCfg C) F.hv
  have hvN : F.v ∈ Subgroup.normalizer (L : Set G) := C.hSN hvS
  have hvH : F.v ∈ H := hSH hvS
  have hπv : C.P.π ⟨F.v, hvN⟩ = swap 0 1 := by
    have h0 : (piSOfCfg C).pf F.v = swap 0 1 := F.hπ
    rw [(piSOfCfg C).pf_eq hvS] at h0
    exact h0
  have key : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (L : Set G)), y ∈ H →
      C.P.π ⟨y, hy⟩ * swap 0 1 * (C.P.π ⟨y, hy⟩)⁻¹ * (swap 0 1)⁻¹ = 1 →
      y * F.v * y⁻¹ * F.v⁻¹ ∈ pCoreOf 2 H := by
    intro y hy hyH hc
    have ht : y * F.v * y⁻¹ * F.v⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem (mul_mem hy hvN) (inv_mem hy)) (inv_mem hvN)
    have hπt : C.P.π ⟨y * F.v * y⁻¹ * F.v⁻¹, ht⟩ = 1 := by
      have e : (⟨y * F.v * y⁻¹ * F.v⁻¹, ht⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨y, hy⟩ * ⟨F.v, hvN⟩ * ⟨y, hy⟩⁻¹ * ⟨F.v, hvN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hπv]
      exact hc
    have hcent := (C.P.hker _).mp hπt
    have hmemC : y * F.v * y⁻¹ * F.v⁻¹ ∈ Subgroup.centralizer (blockU L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := hcent u hu
      have h2 : (y * F.v * y⁻¹ * F.v⁻¹) * u = u * (y * F.v * y⁻¹ * F.v⁻¹) := by
        calc (y * F.v * y⁻¹ * F.v⁻¹) * u
            = ((y * F.v * y⁻¹ * F.v⁻¹) * u * (y * F.v * y⁻¹ * F.v⁻¹)⁻¹) *
                (y * F.v * y⁻¹ * F.v⁻¹) := by group
          _ = u * (y * F.v * y⁻¹ * F.v⁻¹) := by rw [h1]
      exact h2.symm
    have htH : y * F.v * y⁻¹ * F.v⁻¹ ∈ H :=
      mul_mem (mul_mem (mul_mem hyH hvH) (inv_mem hyH)) (inv_mem hvH)
    rw [← C.hQ]
    exact ⟨htH, hmemC⟩
  have hcl : (l₀ : G) ∈ Ggrp F := by
    refine mem_normalizer_W m F hlH ?_ ?_
    · exact key _ hlN hlH (by rw [hπl]; decide)
    · have hπl' : C.P.π ⟨(l₀ : G)⁻¹, inv_mem hlN⟩ = (swap (2 : Fin 5) 3 * swap 3 4)⁻¹ := by
        have e : (⟨(l₀ : G)⁻¹, inv_mem hlN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
            ⟨(l₀ : G), hlN⟩⁻¹ := rfl
        rw [e, map_inv, hπl]
      have := key _ (inv_mem hlN) (inv_mem hlH) (by rw [hπl']; decide)
      simpa using this
  intro hXM
  have hlM : (l₀ : G) ∈ M := hXM hcl
  have hSM : S ≤ M := hcs.le_T.trans hcs.setting.le
  have hDZ : Dstd ≤ C.P.im (H ⊓ M) := by
    rw [← C.hS]
    exact C.P.im_mono (le_inf hSH hSM)
  have hcZ : swap (2 : Fin 5) 3 * swap 3 4 ∈ C.P.im (H ⊓ M) := by
    rw [← hπl]
    exact C.P.pi_mem_im (K := H ⊓ M) (y := ⟨(l₀ : G), hlN⟩) ⟨hlH, hlM⟩
  have hZ : C.P.im (H ⊓ M) = ⊤ := eq_top_of_Dstd_le hDZ hcZ
  have hHM : H ≤ M := by
    intro h hh
    have hhN : h ∈ Subgroup.normalizer (L : Set G) := hHN hh
    have hmem : C.P.π ⟨h, hhN⟩ ∈ C.P.im (H ⊓ M) := by rw [hZ]; trivial
    obtain ⟨y, hyK, hyπ⟩ := (C.P.mem_im).1 hmem
    have hq : (y : G)⁻¹ * h ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (inv_mem y.2) hhN
    have hπq : C.P.π ⟨(y : G)⁻¹ * h, hq⟩ = 1 := by
      have e : (⟨(y : G)⁻¹ * h, hq⟩ : ↥(Subgroup.normalizer (L : Set G))) = y⁻¹ * ⟨h, hhN⟩ := rfl
      rw [e, map_mul, map_inv, hyπ]
      group
    have hcent := (C.P.hker _).mp hπq
    have hqC : (y : G)⁻¹ * h ∈ Subgroup.centralizer (blockU L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := hcent u hu
      calc u * ((y : G)⁻¹ * h) = (((y : G)⁻¹ * h) * u * ((y : G)⁻¹ * h)⁻¹) * ((y : G)⁻¹ * h) := by
            rw [h1]
        _ = ((y : G)⁻¹ * h) * u := by group
    have hqH : (y : G)⁻¹ * h ∈ H := mul_mem (inv_mem hyK.1) hh
    have hqQ : (y : G)⁻¹ * h ∈ pCoreOf 2 H := by
      rw [← C.hQ]
      exact ⟨hqH, hqC⟩
    have hqM : (y : G)⁻¹ * h ∈ M := (C.hQS.trans hSM) hqQ
    have : h = (y : G) * ((y : G)⁻¹ * h) := by group
    rw [this]
    exact mul_mem hyK.2 hqM
  exact hcs.not_le (hLH.trans hHM)

variable (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha3 : SingleA3Excluded)
  (h25 : A5BlockS1)
include hSA hlin ha3 h25

theorem lemma2_4_27_1A5_of : Lemma2_4_27_1A5 := by
  intro G _ _ T M H S L hcs h5 hj
  obtain ⟨C⟩ := AppC.nonempty_cfg hcs hj h5
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  have hne' : S ≠ M₀ := by
    intro hh
    rw [← hh] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne' (le_antisymm hSM hcon)
  have m : GMate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  by_cases hTM : M₀ = T
  · refine ⟨?_, ?_, ?_⟩
    · rw [← hTM]; exact h2
    · exact (m.J_eq_B (GCfg.ofCfg C)).symm
    · rw [← hTM]; exact (thompsonJ_M₀_eq (GCfg.ofCfg C) hSM hMT h2).symm
  · obtain ⟨F⟩ := m.nonempty_four (GCfg.ofCfg C)
    exact (false_of_ne_normT hSA hlin ha3 h25 m hTM F (A5.not_Ggrp_le_M C m F)).elim

end A5Main

end CFSG.QuasithinUnique.DoubleA3
