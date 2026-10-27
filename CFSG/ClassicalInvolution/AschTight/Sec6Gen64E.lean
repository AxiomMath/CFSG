module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64D

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

omit [Finite G] in
theorem le_oddCoreOf_of_normal {A X : Subgroup G} (hAX : A ≤ X)
    (hn : X ≤ Subgroup.normalizer (A : Set G)) (hodd : Odd (Nat.card A)) : A ≤ oddCoreOf X := by
  have hnorm : (A.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr hn
  have hcard : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have hle : A.subgroupOf X ≤ classicalInvolutionOddCore ↥X := le_sSup ⟨hnorm, hcard ▸ hodd⟩
  intro a ha
  exact mem_oddCoreOf_iff.mpr ⟨hAX ha, hle (show (⟨a, hAX ha⟩ : ↥X) ∈ A.subgroupOf X from ha)⟩

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {g : G} (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgj : g ∈ Subgroup.centralizer ({j} : Set G)) :
    g ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hgc : g ∈ Subgroup.normalizer ((Subgroup.centralizer ({j} : Set G) : Subgroup G) :
      Set G) := Subgroup.le_normalizer hgj
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hgK h).mp h1,
      (Subgroup.mem_normalizer_iff.mp hgc h).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hgK h).mpr h1,
      (Subgroup.mem_normalizer_iff.mp hgc h).mpr h2⟩

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

theorem V_le_centralizer_j : Subgroup.zpowers v ≤ Subgroup.centralizer ({j} : Set G) :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (AscL62.cyclic_comm inferInstance hx c.j_mem_V)

theorem CKj_le_normalizer :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
  inf_centralizer_le_normalizer c.hΩ c.hK c.hJ c.hKJ c.hj c.sylow_U inferInstance c.four_le_U
    c.hVJ c.symm.U_isPGroup c.symm.four_le_U c.symm.U_le_normalizer c.V_le_centralizer_j

theorem inf_normalizer_eq :
    K ⊓ Subgroup.normalizer (J : Set G) = K ⊓ Subgroup.centralizer ({j} : Set G) :=
  le_antisymm (le_inf inf_le_left (le_centralizer_of_le_normalizer' c.hj inf_le_right))
    (le_inf inf_le_left c.CKj_le_normalizer)

theorem X_eq : (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) =
    (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ (K ⊓ Subgroup.centralizer ({j} : Set G)) := by
  rw [c.inf_normalizer_eq, c.symm.inf_normalizer_eq]

omit [Finite G] in
theorem CKj_le_centralizer_z :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr (c.z_comm hx.1)

theorem X_le_centralizer_z :
    (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) ≤
      Subgroup.centralizer ({z} : Set G) := by
  rw [c.X_eq]
  exact sup_le inf_le_right c.CKj_le_centralizer_z

theorem X_le_centralizer_j :
    (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) ≤
      Subgroup.centralizer ({j} : Set G) := by
  rw [c.X_eq]
  exact sup_le c.symm.CKj_le_centralizer_z inf_le_right

theorem CJz_le_normalizer_CKj : J ⊓ Subgroup.centralizer ({z} : Set G) ≤
    Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_inf_centralizer (c.symm.CKj_le_normalizer hg)
    (c.symm.CKj_le_centralizer_z hg)

theorem X_eq_oddCore_sup {N₀K N₀J : Subgroup G}
    (hK0 : OddCompl (K ⊓ Subgroup.centralizer ({j} : Set G)) (Subgroup.zpowers u) N₀K)
    (hJ0 : OddCompl (J ⊓ Subgroup.centralizer ({z} : Set G)) (Subgroup.zpowers v) N₀J) :
    N₀K ≤ oddCoreOf ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔
        (K ⊓ Subgroup.normalizer (J : Set G))) ∧
      N₀J ≤ oddCoreOf ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔
        (K ⊓ Subgroup.normalizer (J : Set G))) ∧
      (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) =
        oddCoreOf ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔
          (K ⊓ Subgroup.normalizer (J : Set G))) ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
  set X := (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) with hX
  have hXe : X = (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔
      (K ⊓ Subgroup.centralizer ({j} : Set G)) := c.X_eq
  have hCKX : K ⊓ Subgroup.centralizer ({j} : Set G) ≤ X := hXe ▸ le_sup_right
  have hCJX : J ⊓ Subgroup.centralizer ({z} : Set G) ≤ X := hXe ▸ le_sup_left
  have hK1 : N₀K ≤ oddCoreOf X := by
    refine le_oddCoreOf_of_normal (hK0.le.trans hCKX) ?_ hK0.odd
    rw [hXe]
    exact sup_le (fun _ hg => hK0.le_normalizer (c.CJz_le_normalizer_CKj hg))
      hK0.H_le_normalizer
  have hJ1 : N₀J ≤ oddCoreOf X := by
    refine le_oddCoreOf_of_normal (hJ0.le.trans hCJX) ?_ hJ0.odd
    rw [hXe]
    exact sup_le hJ0.H_le_normalizer
      (fun _ hg => hJ0.le_normalizer (c.symm.CJz_le_normalizer_CKj hg))
  refine ⟨hK1, hJ1, le_antisymm ?_ (sup_le (oddCoreOf_le_self X) (sup_le ?_ ?_))⟩
  · rw [hXe]
    refine sup_le (fun h hh => ?_) (fun h hh => ?_)
    · obtain ⟨n, hn, w, hw, rfl⟩ := hJ0.dec h hh
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hXe ▸ hJ1 hn))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right hw))
    · obtain ⟨n, hn, w, hw, rfl⟩ := hK0.dec h hh
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hXe ▸ hK1 hn))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left hw))
  · exact (le_inf c.hUK c.U_le_centralizer).trans hCKX
  · exact (le_inf c.hVJ c.symm.U_le_centralizer).trans hCJX

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
