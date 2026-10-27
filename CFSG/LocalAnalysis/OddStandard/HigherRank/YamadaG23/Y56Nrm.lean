module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Aut1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y56_conj_mem_centralizer {E : Subgroup G} {n y : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G))
    (hy : y ∈ Subgroup.centralizer (E : Set G)) :
    n * y * n⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro f hf
  have hf' : n⁻¹ * f * n ∈ E := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) f).mp hf
    simpa using h
  have hcomm := hy (n⁻¹ * f * n) hf'
  calc f * (n * y * n⁻¹)
      = n * ((n⁻¹ * f * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * f * n)) * n⁻¹ := by rw [hcomm]
    _ = (n * y * n⁻¹) * f := by group

private theorem y56_conj_mem_H {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {x y : G}
    (hyX : y ∈ e4X s) (hxH : x ∈ Subgroup.centralizer ({s.t} : Set G))
    (hxC : x ∈ Subgroup.centralizer (s.fr.E : Set G)) :
    y * x * y⁻¹ ∈ Subgroup.centralizer ({s.t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hxH ⊢
  obtain ⟨v', hv', hv'eq⟩ := y56_tX_sub hH y⁻¹ (Subgroup.inv_mem (e4X s) hyX)
  have hv'eq' : y⁻¹ * s.t * y = v' * s.t := by simpa using hv'eq
  have hxv' : x * v' = v' * x := (Subgroup.mem_centralizer_iff.mp hxC v' hv').symm
  have hcomm : x * (v' * s.t) = (v' * s.t) * x := by
    calc x * (v' * s.t) = (x * v') * s.t := by group
      _ = (v' * x) * s.t := by rw [hxv']
      _ = v' * (x * s.t) := by group
      _ = v' * (s.t * x) := by rw [hxH]
      _ = (v' * s.t) * x := by group
  have ht_eq : s.t = y * (v' * s.t) * y⁻¹ := by rw [← hv'eq']; group
  rw [ht_eq]
  calc (y * x * y⁻¹) * (y * (v' * s.t) * y⁻¹)
      = y * (x * (v' * s.t)) * y⁻¹ := by group
    _ = y * ((v' * s.t) * x) * y⁻¹ := by rw [hcomm]
    _ = (y * (v' * s.t) * y⁻¹) * (y * x * y⁻¹) := by group

theorem y56_Q_le_X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4Q s ≤ e4X0 s := by
  rw [e4Q, e4X0]
  refine sup_le ?_ ?_
  · intro f hf
    exact Subgroup.mem_inf.mpr
      ⟨s3_L_le_H s hH.hS (y56_E_le_L s hf),
        Subgroup.mem_centralizer_iff.mpr (fun f' hf' => (y56_E_comm hH f hf f' hf').symm)⟩
  · intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem s.H
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl) k, ?_⟩
    exact Subgroup.zpow_mem (Subgroup.centralizer (s.fr.E : Set G))
      (Subgroup.mem_centralizer_iff.mpr (fun f hf => y56_t_comm_E s f hf)) k

theorem y56_X0_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4X0 s ≤ e4X s := by
  intro x hx
  rw [e4X0, centIn, Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxC⟩ := hx
  have hxE : x ∈ Subgroup.normalizer (s.fr.E : Set G) :=
    Subgroup.centralizer_le_normalizer (s.fr.E : Set G) hxC
  have hEmap : (s.fr.E).map (MulAut.conj x) = s.fr.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxE
  have hcomm : x * s.t = s.t * x := Subgroup.mem_centralizer_singleton_iff.mp hxH
  have hconj : (↑(MulAut.conj x) : G →* G) s.t = s.t := by
    change (MulAut.conj x) s.t = s.t
    rw [MulAut.conj_apply, hcomm]; group
  rw [e4X, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, MonoidHom.map_zpowers,
    hconj, hEmap]

theorem y56_X0_le_Y {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4X0 s ≤ e4Y s := by
  intro x hx
  have hx0 : x ∈ e4X0 s := hx
  rw [e4X0, centIn, Subgroup.mem_inf] at hx
  rw [e4Y, centIn]
  exact Subgroup.mem_inf.mpr ⟨y56_X0_le_X hH hx0, hx.2⟩

theorem y56_N_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4N s ≤ e4X s := by
  intro n hn
  rw [e4N, normIn, Subgroup.mem_inf] at hn
  obtain ⟨hnH, hnE⟩ := hn
  have hEmap : (s.fr.E).map (MulAut.conj n) = s.fr.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnE
  have hcomm : n * s.t = s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hnH
  have hconj : (↑(MulAut.conj n) : G →* G) s.t = s.t := by
    change (MulAut.conj n) s.t = s.t
    rw [MulAut.conj_apply, hcomm]; group
  rw [e4X, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, MonoidHom.map_zpowers,
    hconj, hEmap]

theorem y56_NL_le_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.E ≤ e4N s := by
  intro n hn
  rw [normIn, Subgroup.mem_inf] at hn
  exact Subgroup.mem_inf.mpr ⟨s3_L_le_H s hH.hS hn.1, hn.2⟩

theorem y56_X_inf_H {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4X s ⊓ s.H = e4N s := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    exact Subgroup.mem_inf.mpr ⟨hx.2, y56_X_le_normE hH hx.1⟩
  · intro x hx
    have hxN : x ∈ e4N s := hx
    rw [e4N, normIn, Subgroup.mem_inf] at hx
    exact Subgroup.mem_inf.mpr ⟨y56_N_le_X hH hxN, hx.1⟩

theorem y56_N_norm_Y {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ e4N s, ∀ y ∈ e4Y s, n * y * n⁻¹ ∈ e4Y s := by
  intro n hn y hy
  have hnX : n ∈ e4X s := y56_N_le_X hH hn
  rw [e4N, normIn, Subgroup.mem_inf] at hn
  rw [e4Y, centIn, Subgroup.mem_inf] at hy
  rw [e4Y, centIn]
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hnX hy.1) (Subgroup.inv_mem _ hnX),
      y56_conj_mem_centralizer hn.2 hy.2⟩

theorem y56_Y_norm_X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ e4Y s, ∀ x ∈ e4X0 s, y * x * y⁻¹ ∈ e4X0 s := by
  intro y hy x hx
  rw [e4Y, centIn, Subgroup.mem_inf] at hy
  rw [e4X0, centIn, Subgroup.mem_inf] at hx
  rw [e4X0, centIn]
  exact Subgroup.mem_inf.mpr
    ⟨y56_conj_mem_H hH hy.1 hx.1 hx.2,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hy.2 hx.2) (Subgroup.inv_mem _ hy.2)⟩

theorem y56_NL_X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ normIn L s.fr.E, ∀ x ∈ e4X0 s, ⁅n, x⁆ ∈ s.fr.E := by
  intro n hn x hx
  rw [normIn, Subgroup.mem_inf] at hn
  obtain ⟨hnL, hnN⟩ := hn
  rw [e4X0, centIn, Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxC⟩ := hx
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := s3_H_le_N s hH.hS hxH
  have hmemL : n⁻¹ * x * n * x⁻¹ ∈ L := by
    have hxnx : x * n * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN n).mp hnL
    have h := Subgroup.mul_mem L (Subgroup.inv_mem L hnL) hxnx
    simpa only [mul_assoc] using h
  have hmemC : n⁻¹ * x * n * x⁻¹ ∈ Subgroup.centralizer (s.fr.E : Set G) := by
    have h1 : n⁻¹ * x * (n⁻¹)⁻¹ ∈ Subgroup.centralizer (s.fr.E : Set G) :=
      y56_conj_mem_centralizer (Subgroup.inv_mem _ hnN) hxC
    have h := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hxC)
    simpa only [inv_inv, mul_assoc] using h
  have hmemE : n⁻¹ * x * n * x⁻¹ ∈ s.fr.E := by
    rw [← y56_centIn_L_E hH]
    exact Subgroup.mem_inf.mpr ⟨hmemL, hmemC⟩
  have hconjE : x * n * x⁻¹ * n⁻¹ ∈ s.fr.E := by
    have h := (Subgroup.mem_normalizer_iff.mp hnN (n⁻¹ * x * n * x⁻¹)).mp hmemE
    have hEq : n * (n⁻¹ * x * n * x⁻¹) * n⁻¹ = x * n * x⁻¹ * n⁻¹ := by group
    rw [hEq] at h
    exact h
  rw [commutatorElement_def]
  have h := Subgroup.inv_mem (s.fr.E) hconjE
  have hEq : (x * n * x⁻¹ * n⁻¹)⁻¹ = n * x * n⁻¹ * x⁻¹ := by group
  rw [hEq] at h
  exact h

theorem y56_N_norm_Q {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ e4N s, ∀ q ∈ e4Q s, n * q * n⁻¹ ∈ e4Q s := by
  intro n hn q hq
  exact (Subgroup.mem_normalizer_iff.mp (y56_N_le_X hH hn) q).mp hq

theorem y56_Y_norm_Q {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ e4Y s, ∀ q ∈ e4Q s, y * q * y⁻¹ ∈ e4Q s := by
  intro y hy q hq
  rw [e4Y, centIn] at hy
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hy).1 q).mp hq

end CFSG.OddStandard.HigherRank.YamadaG23
