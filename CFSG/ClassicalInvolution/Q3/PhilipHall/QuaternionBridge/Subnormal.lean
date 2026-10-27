module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3

variable {Y : Type} [Group Y]

theorem inv_conj_of_central {t y ν : Y} (hν : ν ∈ Subgroup.center Y) (hy : y * t * y⁻¹ = t * ν) :
    y⁻¹ * t * y = t * ν⁻¹ := by
  have hνZ : ∀ a : Y, a * ν = ν * a := Subgroup.mem_center_iff.mp hν
  have hνy : y⁻¹ * ν * y = ν := by
    rw [hνZ y⁻¹]
    group
  have h1 : y⁻¹ * (t * ν) * y = t := by
    rw [← hy]
    group
  have h2 : (y⁻¹ * t * y) * ν = t := by
    have : y⁻¹ * (t * ν) * y = (y⁻¹ * t * y) * (y⁻¹ * ν * y) := by group
    rw [this, hνy] at h1
    exact h1
  exact eq_mul_inv_of_mul_eq h2

theorem conj_centralizer_of_central {t y ν : Y} (hν : ν ∈ Subgroup.center Y)
    (hy : y * t * y⁻¹ = t * ν) {g : Y} (hg : g ∈ Subgroup.centralizer ({t} : Set Y)) :
    y * g * y⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := by
  have hνiZ : ∀ a : Y, a * ν⁻¹ = ν⁻¹ * a :=
    Subgroup.mem_center_iff.mp ((Subgroup.center Y).inv_mem hν)
  have e1 := inv_conj_of_central hν hy
  have hyν : y * ν⁻¹ * y⁻¹ = ν⁻¹ := by
    rw [hνiZ y]
    group
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  calc y * g * y⁻¹ * t = y * g * (y⁻¹ * t * y) * y⁻¹ := by group
    _ = y * g * (t * ν⁻¹) * y⁻¹ := by rw [e1]
    _ = y * (g * t) * ν⁻¹ * y⁻¹ := by group
    _ = y * (t * g) * ν⁻¹ * y⁻¹ := by rw [hg]
    _ = y * t * (g * ν⁻¹) * y⁻¹ := by group
    _ = y * t * (ν⁻¹ * g) * y⁻¹ := by rw [hνiZ g]
    _ = (y * t * y⁻¹) * (y * ν⁻¹ * y⁻¹) * (y * g * y⁻¹) := by group
    _ = (t * ν) * ν⁻¹ * (y * g * y⁻¹) := by rw [hy, hyν]
    _ = t * (y * g * y⁻¹) := by group

theorem mem_normalizer_centralizer_of_central {t y ν : Y} (hν : ν ∈ Subgroup.center Y)
    (hy : y * t * y⁻¹ = t * ν) :
    y ∈ Subgroup.normalizer (Subgroup.centralizer ({t} : Set Y) : Set Y) := by
  have hy' : y⁻¹ * t * y⁻¹⁻¹ = t * ν⁻¹ := by
    rw [inv_inv]
    exact inv_conj_of_central hν hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact fun hn => conj_centralizer_of_central hν hy hn
  · intro hn
    have := conj_centralizer_of_central ((Subgroup.center Y).inv_mem hν) hy' hn
    rwa [show y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n by group] at this

variable [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {N : Subgroup Y} [N.Normal]

theorem normal_map_centralizer (hNc : N ≤ Subgroup.center Y) :
    (((Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N)).subgroupOf
      (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)))).Normal := by
  have hle : (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro c hc
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N c
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp hc
  have h2 : QuotientGroup.mk' N (y * t * y⁻¹) = QuotientGroup.mk' N t := by
    rw [map_mul, map_mul, map_inv, h1]
    group
  have h2' : (QuotientGroup.mk t : Y ⧸ N) = QuotientGroup.mk (y * t * y⁻¹) := h2.symm
  have hν : t⁻¹ * (y * t * y⁻¹) ∈ N := QuotientGroup.eq.mp h2'
  have hy : y * t * y⁻¹ = t * (t⁻¹ * (y * t * y⁻¹)) := by group
  have hn := mem_normalizer_centralizer_of_central (hNc hν) hy
  rw [mem_normalizer_iff_conjSub_eq, ← TwistQ.conjSub_map (N := N),
    mem_normalizer_iff_conjSub_eq.mp hn]

variable (hd : TightDatum R S t)
include hd

theorem normal_map_core_map_centralizer :
    (((tightCore R).map (QuotientGroup.mk' N)).subgroupOf
      ((Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N))).Normal := by
  have hle : (tightCore R).map (QuotientGroup.mk' N) ≤
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) :=
    Subgroup.map_mono hd.le_centralizer_core
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_normalizer_iff_conjSub_eq, ← TwistQ.conjSub_map (N := N),
    mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core hg)]

theorem isSubnormal_map_core (hNc : N ≤ Subgroup.center Y) :
    IsSubnormal ((tightCore R).map (QuotientGroup.mk' N))
      (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N))) := by
  have hle1 : (tightCore R).map (QuotientGroup.mk' N) ≤
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) :=
    Subgroup.map_mono hd.le_centralizer_core
  have hle2 : (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  exact IsSubnormal.step hle1 (normal_map_core_map_centralizer hd)
    (IsSubnormal.step hle2 (normal_map_centralizer hNc) (IsSubnormal.refl _))

theorem isSubnormal_tightCore_map (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    (htN : t ∉ N) :
    IsSubnormal (tightCore (R.map (QuotientGroup.mk' N)))
      (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N))) := by
  rw [← TwistQ.tightCore_map (TwistQ.inf_eq_bot hd hN2 htN)]
  exact isSubnormal_map_core hd hNc

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
