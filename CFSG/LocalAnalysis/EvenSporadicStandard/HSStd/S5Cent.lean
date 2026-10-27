module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Aut

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type*} [Group G] {L : Subgroup G} {W X : Type*} [Group W] [Group X]
  (D : AutModelData L W X) {t : G}

@[expose] noncomputable def AutModelData.rhoC
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) :
    ↥(centralizer ({t} : Set G)) →* W :=
  D.rho.comp (Subgroup.inclusion hC)

theorem AutModelData.rhoC_apply (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (x : centralizer ({t} : Set G)) : D.rhoC hC x = D.rho ⟨x, hC x.2⟩ := rfl

theorem le_centralizer_of_mem_centralizer (ht : t ∈ centralizer (L : Set G)) :
    L ≤ centralizer ({t} : Set G) := fun l hl =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)

section Cent

variable (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
  (ht : t ∈ centralizer (L : Set G))
  (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
include hker

theorem rhoC_eq_one_iff (x : centralizer ({t} : Set G)) :
    D.rhoC hC x = 1 ↔ (x : G) ∈ zpowers t := by
  rw [D.rhoC_apply, D.rho_eq_one_iff, ← hker, mem_inf]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

omit hker in
theorem rhoC_of_mem (l : L) :
    D.rhoC hC ⟨l, le_centralizer_of_mem_centralizer ht l.2⟩ = D.ι (D.θ l) :=
  D.rho_of_mem l

include ht in
theorem rhoC_mem_range_iff (x : centralizer ({t} : Set G)) :
    D.rhoC hC x ∈ D.ι.range ↔ (x : G) ∈ L ⊔ zpowers t := by
  have hcomm : ∀ β ∈ L, Commute β t := fun β hβ => mem_centralizer_iff.1 ht β hβ
  have htk : ∀ j : ℤ, D.rhoC hC ⟨t ^ j, zpow_mem (mem_centralizer_singleton_iff.2 rfl) j⟩ = 1 :=
    fun j => (rhoC_eq_one_iff D hC hker _).2 (zpow_mem (mem_zpowers t) j)
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨l, rfl⟩ := D.θ.surjective y
    have h1 : D.rhoC hC (⟨l, le_centralizer_of_mem_centralizer ht l.2⟩⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, rhoC_of_mem D hC ht l, hy, inv_mul_cancel]
    have h2 := (rhoC_eq_one_iff D hC hker _).1 h1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
    have hx : (x : G) = (l : G) * t ^ j := by
      have : ((⟨l, le_centralizer_of_mem_centralizer ht l.2⟩⁻¹ * x : centralizer
          ({t} : Set G)) : G) = (l : G)⁻¹ * x := rfl
      rw [this] at hj
      calc (x : G) = (l : G) * ((l : G)⁻¹ * x) := by group
        _ = l * t ^ j := by rw [← hj]
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
      (Subgroup.mem_sup_right (zpow_mem (mem_zpowers t) j))
  · intro hx
    obtain ⟨β, hβ, j, hj⟩ := (mem_sup_zpowers_iff hcomm).1 hx
    have hmul : x = (⟨β, le_centralizer_of_mem_centralizer ht hβ⟩ : centralizer
        ({t} : Set G)) * ⟨t ^ j, zpow_mem (mem_centralizer_singleton_iff.2 rfl) j⟩ :=
      Subtype.ext hj
    rw [hmul, map_mul, htk, mul_one]
    exact ⟨D.θ ⟨β, hβ⟩, by rw [← rhoC_of_mem D hC ht ⟨β, hβ⟩]⟩

end Cent

end CFSG.EvenSporadicStandard.HSStd
