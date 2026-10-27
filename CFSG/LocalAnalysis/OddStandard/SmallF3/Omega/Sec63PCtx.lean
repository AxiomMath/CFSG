module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec63PCtx {G : Type} [Group G] (v y b : G) (V W Y Vb R I J : Subgroup G) : Prop where
  hv : orderOf v = 2
  hy : orderOf y = 2
  hb : orderOf b = 2
  hvb : v * b = b * v
  hyb : y * b = b * y
  hVc : IsComponentIn V (centralizer ({v} : Set G))
  hWc : IsComponentIn W (centralizer ({v} : Set G))
  hWne : W ≠ V
  hVF : InFStar V
  hWF : InFStar W
  hVY : V ≤ Y
  hYc : IsComponentIn Y (centralizer ({y} : Set G))
  hVbc : IsComponentIn Vb (Y ⊓ centralizer ({b} : Set G))
  huniq : ∀ K : Subgroup G, IsComponentIn K (Y ⊓ centralizer ({b} : Set G)) → K = Vb
  hbound : ∀ P : Subgroup G, IsPGroup 2 P →
    P ≤ V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) → Nat.card P ≤ 2
  hR2 : IsPGroup 2 R
  hRle : R ≤ V ⊓ centralizer ({b} : Set G)
  hR8 : Nat.card R = 8
  hRgen : R = Subgroup.closure {r : G | r ∈ R ∧ orderOf r = 2}
  hJc : IsComponentIn J (centralizer ({b} : Set G))
  hJF : InFStar J
  hWJ : W ≤ J ⊔ CFSG.conjugate J v
  hIc : IsComponentIn I (centralizer ({b} : Set G))
  hIF : InFStar I
  hVbI : Vb ≤ I ⊔ CFSG.conjugate I y
  hthird : ∀ K : Subgroup G, IsComponentIn K (centralizer ({b} : Set G)) → InFStar K →
    K = I ∨ K = CFSG.conjugate I y

variable {G : Type} [Group G]

theorem sec63P_key1 [Finite G] {v y b : G} {V W Y Vb R I J : Subgroup G}
    (c : Sec63PCtx v y b V W Y Vb R I J) {K : Subgroup G} {g : G}
    (hKc : IsComponentIn K (centralizer ({b} : Set G))) (hKF : InFStar K) (hgY : g ∈ Y)
    (hgb : g ∈ centralizer ({b} : Set G)) (hgK : K ≤ centralizer ({g} : Set G)) :
    Vb ≤ centralizer ({g} : Set G) := by
  have hyb' : y ∈ centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 c.hyb
  have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.1 (c.hYc.le hgY)
  by_cases hII' : CFSG.conjugate I y = I
  ·
    have hVbI : Vb ≤ I := by
      have hVbI' := c.hVbI
      have h : I ⊔ CFSG.conjugate I y = I := by rw [hII', sup_idem]
      rwa [h] at hVbI'
    have hKI : K = I := by
      rcases c.hthird K hKc hKF with h | h
      · exact h
      · rw [h, hII']
    rw [hKI] at hgK
    exact hVbI.trans hgK
  ·
    have hK2c : IsComponentIn (CFSG.conjugate K y) (centralizer ({b} : Set G)) :=
      hKc.conjugate hyb'
    have hKne : K ≠ CFSG.conjugate K y := by
      intro h
      rcases c.hthird K hKc hKF with hK | hK
      · rw [hK] at h
        exact hII' h.symm
      · rw [hK] at h
        rw [conjugate_conjugate_of_orderOf_eq_two c.hy] at h
        exact hII' h
    have hcomm : ∀ a ∈ K, ∀ a' ∈ CFSG.conjugate K y, a * a' = a' * a :=
      hKc.commute_of_ne hK2c hKne
    have hΔ : Vb ≤ K ⊔ CFSG.conjugate K y := by
      rcases c.hthird K hKc hKF with hK | hK
      · rw [hK]
        exact c.hVbI
      · rw [hK]
        rw [conjugate_conjugate_of_orderOf_eq_two c.hy, sup_comm]
        exact c.hVbI
    have hΔ2 : ¬ Vb ≤ CFSG.conjugate K y := by
      intro hle
      have hVbY : Vb ≤ Y := c.hVbc.le.trans inf_le_left
      have hVb_cent_y : Vb ≤ centralizer ({y} : Set G) := hVbY.trans c.hYc.le
      have hVbK : Vb ≤ K := by
        intro x hx
        have hx' : x ∈ CFSG.conjugate K y := hle hx
        rw [sec63P_mem_conjugate_iff] at hx'
        have hcomm_x : x * y = y * x :=
          Subgroup.mem_centralizer_singleton_iff.1 (hVb_cent_y hx)
        rwa [show y * x * y⁻¹ = x by rw [← hcomm_x]; group] at hx'
      have hle_cent : Vb ≤ centralizer (Vb : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro a' ha'
        exact (hcomm a (hVbK ha) a' (hle ha')).symm
      exact c.hVbc.not_le_centralizer hle_cent
    have hK2cent : CFSG.conjugate K y ≤ centralizer ({g} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [sec63P_mem_conjugate_iff] at hz
      have hk : Commute (y * z * y⁻¹) g :=
        Subgroup.mem_centralizer_singleton_iff.1 (hgK hz)
      have hy_comm : Commute g y := hgy
      have hz_eq : z = y⁻¹ * (y * z * y⁻¹) * y := by group
      rw [hz_eq]
      exact (((hy_comm.symm.inv_left).mul_left hk).mul_left hy_comm.symm).eq
    have hg2 : g ∈ normalizer (CFSG.conjugate K y : Set G) :=
      sec63P_conjugate_eq_iff.1 (conjugate_eq_self_of_le_centralizer hK2cent)
    have hgΔ : g ∈ normalizer (Vb : Set G) :=
      sec63P_conjugate_eq_iff.1 (c.huniq (CFSG.conjugate Vb g) (c.hVbc.conjugate ⟨hgY, hgb⟩))
    exact sec63_diag_D2 c.hVbc.isQuasisimple hcomm hΔ hΔ2 hgK hg2 hgΔ

end CFSG.OddStandard.SmallF3.Omega
