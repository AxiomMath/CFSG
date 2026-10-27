module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltCore
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltRho
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local Equiv Equiv.Perm
open scoped commutatorElement

theorem map_mem_normalizer {A B : Type} [Group A] [Group B] (ρ : A →* B) (X : Subgroup A) {g : A}
    (hg : g ∈ normalizer (X : Set A)) : ρ g ∈ normalizer ((X.map ρ : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx, by simp⟩
  · rintro ⟨x', hx', hx'h⟩
    refine ⟨g⁻¹ * x' * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x').mp hx'
      simpa using this
    · rw [map_mul, map_mul, map_inv, hx'h]
      group

theorem alt_reduction {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ} {X : Subgroup A}
    (hd : CellData zb p X) {n : ℕ} (hn7 : 7 ≤ n)
    (e : (↥(layer A) ⧸ center ↥(layer A)) ≃* alternatingGroup (Fin n)) : False := by
  classical
  have : (layer A).Normal := layer_normal
  have : Group.IsPerfect ↥(layer A) := hd.quasi.1
  obtain ⟨ρ, hρK, hρker⟩ := AltRho.exists_rho (layer A) (by omega) (by omega) e
  have : Fact p.Prime := ⟨hd.A4.prime⟩
  have hp2 : p ≠ 2 := hd.A4.odd
  have hZ2 : IsPGroup 2 ↥(center ↥(layer A)) := by rw [hd.Zcore]; exact CFSG.pCore_isPGroup
  have hzN : zb ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A hd.A4
  have hy : ρ zb * ρ zb = 1 := by rw [← map_mul, hd.z2, map_one]
  have hYp : IsPGroup p ↥(X.map ρ) := hd.A4.pgroup.map ρ
  have hyN : ρ zb ∈ normalizer ((X.map ρ : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) :=
    map_mem_normalizer ρ X hzN
  have hnc : ∃ x ∈ X.map ρ, x * ρ zb ≠ ρ zb * x := by
    by_contra hcon
    push Not at hcon
    have hcomm : ⁅X, zpowers zb⁆ ≤ ρ.ker := by
      rw [Subgroup.commutator_le]
      intro x hx w hw
      rw [MonoidHom.mem_ker]
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hxy : ρ x * ρ zb = ρ zb * ρ x := hcon (ρ x) ⟨x, hx, rfl⟩
      have hxm : Commute (ρ x) (ρ zb ^ m) := (show Commute (ρ x) (ρ zb) from hxy).zpow_right m
      simp only [commutatorElement_def, map_mul, map_inv, map_zpow]
      rw [hxm.eq]
      group
    rw [hd.A4.comm, hρker] at hcomm
    apply hd.nc
    rw [Subgroup.commutator_le]
    intro k hk x hx
    have h1 := Subgroup.mem_centralizer_iff.mp (hcomm hx) k hk
    have h2 : ⁅k, x⁆ = 1 := by rw [commutatorElement_def, h1]; group
    rw [h2]
    exact Subgroup.one_mem _
  have hD : ∀ v : Perm (Fin n), Odd (orderOf v) → v * ρ zb = ρ zb * v →
      v ∈ normalizer ((X.map ρ : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
    intro v hv hvy
    obtain ⟨k₁, hk₁K, hk₁z, hρk₁⟩ := AltRho.exists_odd_lift (layer A) ρ e hρK hρker hZ2 hv hvy
    have hcent : k₁ ∈ centralizer ({zb} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k₁ * zb = (zb * k₁ * zb⁻¹) * zb := by rw [hk₁z]
        _ = zb * k₁ := by group
    have hk₁N : k₁ ∈ normalizer (X : Set A) := hd.A4.inv k₁ (Subgroup.mem_top _) hcent
    rw [← hρk₁]
    exact map_mem_normalizer ρ X hk₁N
  exact AltCore.alt_core (by simpa using hn7) hp2 hYp hy hyN hD hnc

theorem cell87_FAlt : Cell87 FAlt := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hFK
  exfalso
  obtain ⟨n, hn7, -, ⟨e⟩⟩ := hFK
  exact alt_reduction (CellData.of_ctx hctx hsig hyp) hn7 e

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
