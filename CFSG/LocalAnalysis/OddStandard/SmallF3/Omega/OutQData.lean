module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQTrans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG

variable {G : Type} [Group G]

theorem aor_l34_comm {x y u : G} {X K I : Subgroup G} (hD : Sec3L34Data x X y K u I) :
    x * u = u * x := by
  obtain ⟨c, hc, rfl⟩ := hD.mem
  have hx : x * c = c * x :=
    mem_centralizer_iff.mp hc x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hy : x * y = y * x :=
    mem_centralizer_iff.mp (hD.pocket.component.1 hD.pocket.mem) x (Set.mem_singleton x)
  calc x * (c * y) = (x * c) * y := by rw [mul_assoc]
    _ = (c * x) * y := by rw [hx]
    _ = c * (x * y) := by rw [mul_assoc]
    _ = c * (y * x) := by rw [hy]
    _ = (c * y) * x := by rw [mul_assoc]

theorem aor_l34_le_centralizer_pair {x y u : G} {X K I : Subgroup G}
    (hD : Sec3L34Data x X y K u I) : K ≤ centralizer ({x, u} : Set G) := by
  obtain ⟨c, hc, rfl⟩ := hD.mem
  intro k hk
  have hkM : k ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) :=
    hD.pocket.pocket.2.1 hk
  have hkx : x * k = k * x :=
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp hkM).1 x (Set.mem_singleton x)
  have hky : y * k = k * y :=
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp hkM).2 y (Set.mem_singleton y)
  have hkc : c * k = k * c :=
    (mem_centralizer_iff.mp hc k (Subgroup.mem_sup_left (hD.pocket.le hk))).symm
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with rfl | rfl
  · exact hkx
  · calc (c * y) * k = c * (y * k) := by rw [mul_assoc]
      _ = c * (k * y) := by rw [hky]
      _ = (c * k) * y := by rw [mul_assoc]
      _ = (k * c) * y := by rw [hkc]
      _ = k * (c * y) := by rw [mul_assoc]

theorem aor_l34_subnormal {x y u : G} {X K I : Subgroup G} (hD : Sec3L34Data x X y K u I) :
    (K.subgroupOf (centralizer ({x, u} : Set G))).IsSubnormal := by
  obtain ⟨c, hc, rfl⟩ := hD.mem
  have hcg : ∀ g ∈ X, g * c = c * g := fun g hg =>
    mem_centralizer_iff.mp hc g (Subgroup.mem_sup_left hg)
  have hmem : ∀ g, g ∈ X →
      (g ∈ centralizer ({y} : Set G) ↔ g ∈ centralizer ({c * y} : Set G)) := by
    intro g hgX
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hgy
      calc g * (c * y) = (g * c) * y := by rw [mul_assoc]
        _ = (c * g) * y := by rw [hcg g hgX]
        _ = c * (g * y) := by rw [mul_assoc]
        _ = c * (y * g) := by rw [hgy]
        _ = (c * y) * g := by rw [mul_assoc]
    · intro hgu
      have h1 : c * (g * y) = c * (y * g) := by
        calc c * (g * y) = (c * g) * y := by rw [mul_assoc]
          _ = (g * c) * y := by rw [← hcg g hgX]
          _ = g * (c * y) := by rw [mul_assoc]
          _ = (c * y) * g := hgu
          _ = c * (y * g) := by rw [mul_assoc]
      exact mul_left_cancel h1
  have hCyCu : X ⊓ centralizer ({y} : Set G) = X ⊓ centralizer ({c * y} : Set G) := by
    ext g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr_right fun hgX => hmem g hgX
  have hXM : X ⊓ (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) =
      X ⊓ centralizer ({c * y} : Set G) := by
    rw [← inf_assoc, inf_eq_left.2 hD.pocket.component.1, hCyCu]
  have hpair : centralizer ({x, c * y} : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({c * y} : Set G) := by
    ext g
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨(h x (by simp)).symm, (h (c * y) (by simp)).symm⟩
    · rintro ⟨hx, hu⟩ h' hh'
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh'
      rcases hh' with rfl | rfl
      · exact hx.symm
      · exact hu.symm
  have hmain :
      (K.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({c * y} : Set G))).IsSubnormal :=
    aor_subnormal_pair hD.pocket.component.1 hD.pocket.le hD.pocket.pocket.2.1 inf_le_left
      hXM hD.pocket.component.2.2 hD.pocket.pocket.2.2.1
  rw [hpair]
  exact hmain

end CFSG.OddStandard.SmallF3.Omega
