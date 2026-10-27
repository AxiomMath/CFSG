module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Extend

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G']

theorem extend_iso_cent {a t : G} {a' : G'} {α β : G → G'} {η : G → G}
    (hα : IsIsoOn (Gx a) (Gx a') α) (hαa : α a = a') (hat : a ∈ Gx t)
    (hβ : IsIsoOn (Gx t) (Gx (α t)) β) (hβa : β a = a') (hβt : β t = α t)
    (hdec : ∀ y ∈ Gxy a t, ∃ u ∈ Subgroup.closure ({a, t} : Set G),
      ∃ n ∈ derivedOf (Gxy a t), y = u * n)
    (hη : IsIsoOn (Gx t) (Gx t) η) (hηa : η a = a) (hηt : η t = t)
    (hηout : ¬ ∃ g ∈ derivedOf (Gxy a t), ∀ x ∈ derivedOf (Gxy a t), η x = g * x * g⁻¹)
    (hout : ∀ ψ₁ ψ₂ : G → G,
      IsIsoOn (derivedOf (Gxy a t)) (derivedOf (Gxy a t)) ψ₁ →
      IsIsoOn (derivedOf (Gxy a t)) (derivedOf (Gxy a t)) ψ₂ →
      (¬ ∃ g ∈ derivedOf (Gxy a t), ∀ x ∈ derivedOf (Gxy a t), ψ₁ x = g * x * g⁻¹) →
      (¬ ∃ g ∈ derivedOf (Gxy a t), ∀ x ∈ derivedOf (Gxy a t), ψ₂ x = g * x * g⁻¹) →
      ∃ g ∈ derivedOf (Gxy a t), ∀ x ∈ derivedOf (Gxy a t), ψ₁ (ψ₂ x) = g * x * g⁻¹) :
    ∃ β₁ : G → G', IsIsoOn (Gx t) (Gx (α t)) β₁ ∧ ∀ y ∈ Gxy a t, β₁ y = α y := by
  have ha_mem : a ∈ Gxy a t :=
    mem_Gxy.mpr ⟨self_mem_Gx a, mem_Gx.mpr (mem_Gx.mp hat)⟩
  have ht_mem : t ∈ Gxy a t :=
    mem_Gxy.mpr ⟨mem_Gx.mpr (mem_Gx.mp hat).symm, self_mem_Gx t⟩
  have hS : ({a, t} : Set G) ⊆ Gxy a t := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxa | hxt
    · rw [hxa]; exact ha_mem
    · rw [hxt]; exact ht_mem
  have hYM : Gxy a t ≤ Gx t := fun y hy => (mem_Gxy.mp hy).2
  have hZY : Subgroup.closure ({a, t} : Set G) ≤ Gxy a t :=
    (Subgroup.closure_le (Gxy a t)).mpr hS
  have hNY : derivedOf (Gxy a t) ≤ Gxy a t := derivedOf_le _
  have hZc : ∀ u ∈ Subgroup.closure ({a, t} : Set G), ∀ y ∈ Gxy a t, u * y = y * u := by
    have hle : Subgroup.closure ({a, t} : Set G) ≤
        Subgroup.centralizer (Gxy a t : Set G) :=
      (Subgroup.closure_le (Subgroup.centralizer (Gxy a t : Set G))).mpr (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hxa | hxt
        · rw [hxa]
          refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
          exact (mem_Gx.mp (mem_Gxy.mp hy).1).symm
        · rw [hxt]
          refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
          exact (mem_Gx.mp (mem_Gxy.mp hy).2).symm)
    intro u hu y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hu) y hy).symm
  have hα' : IsIsoOn (Gxy a t) (Gxy a' (α t)) α := by
    rw [Gxy_eq_inf a t, Gxy_eq_inf a' (α t)]
    exact hα.restrict_cent (mem_Gx.mpr (mem_Gx.mp hat).symm)
  have hβY : IsIsoOn (Gxy a t) (Gxy a' (α t)) β := by
    have h := hβ.restrict_cent (t := a) hat
    rw [hβa] at h
    rw [inf_comm (Gx t) (Gx a), inf_comm (Gx (α t)) (Gx a')] at h
    rw [← Gxy_eq_inf a t, ← Gxy_eq_inf a' (α t)] at h
    exact h
  have hZ : ∀ u ∈ Subgroup.closure ({a, t} : Set G), β u = α u :=
    IsIsoOn.agree_on_closure hβY hα' (S := {a, t}) hS (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxa | hxt
      · rw [hxa]; exact hβa.trans hαa.symm
      · rw [hxt]; exact hβt)
  have hNN : ∀ y' ∈ Gxy a' (α t),
      (∃ n ∈ derivedOf (Gxy a t), α n = y') ↔
        (∃ n ∈ derivedOf (Gxy a t), β n = y') := by
    intro y' hy'
    constructor
    · rintro ⟨n, hn, hn'⟩
      exact hβY.derived.surjOn y' (by rw [← hn']; exact hα'.derived.mem n hn)
    · rintro ⟨n, hn, hn'⟩
      exact hα'.derived.surjOn y' (by rw [← hn']; exact hβY.derived.mem n hn)
  have hId : IsIsoOn (Gx t) (Gx t) (id : G → G) :=
    ⟨fun _ _ _ _ => rfl, fun _ hx => hx, fun _ _ _ _ h => h, fun y hy => ⟨y, hy, rfl⟩⟩
  have hηZ : ∀ u ∈ Subgroup.closure ({a, t} : Set G), η u = u :=
    IsIsoOn.agree_on_closure hη hId (S := {a, t}) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxa | hxt
      · rw [hxa]; exact hat
      · rw [hxt]; exact self_mem_Gx t) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxa | hxt
      · rw [hxa]; exact hηa
      · rw [hxt]; exact hηt)
  have hηY : IsIsoOn (Gxy a t) (Gxy a t) η := by
    have h := hη.restrict_cent (t := a) hat
    rw [hηa] at h
    rw [inf_comm (Gx t) (Gx a), ← Gxy_eq_inf a t] at h
    exact h
  have hηN : IsIsoOn (derivedOf (Gxy a t)) (derivedOf (Gxy a t)) η := hηY.derived
  exact extend_iso (M := Gx t) (Y := Gxy a t) (N := derivedOf (Gxy a t))
    (Z := Subgroup.closure ({a, t} : Set G)) (M' := Gx (α t)) (Y' := Gxy a' (α t))
    hYM hZY hNY hdec hZc hα' hβ hβY.mem hβY.surjOn hZ hNN hη hηZ hηN hηout hout

end CFSG.EvenSporadicStandard.HNRecog.Section4
