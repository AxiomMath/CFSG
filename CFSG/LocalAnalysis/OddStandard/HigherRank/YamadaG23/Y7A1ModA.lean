module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem inv_mul_eq_of_commute {x y : G} (h : x * y = y * x) : x⁻¹ * y * x = y := by
  calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
    _ = x⁻¹ * (x * y) := by rw [← h]
    _ = y := by group

private theorem mem_sup_of_commute {A V : Subgroup G}
    (hc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) {x : G} (hx : x ∈ A ⊔ V) :
    ∃ a ∈ A, ∃ v ∈ V, x = a * v := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, V.one_mem, by simp⟩
      · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, V.one_mem, by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨a₁, ha₁, v₁, hv₁, rfl⟩ := ihx
      obtain ⟨a₂, ha₂, v₂, hv₂, rfl⟩ := ihy
      refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, v₁ * v₂, V.mul_mem hv₁ hv₂, ?_⟩
      calc (a₁ * v₁) * (a₂ * v₂) = a₁ * (v₁ * a₂) * v₂ := by group
        _ = a₁ * (a₂ * v₁) * v₂ := by rw [hc a₂ ha₂ v₁ hv₁]
        _ = (a₁ * a₂) * (v₁ * v₂) := by group
  | inv x hx ih =>
      obtain ⟨a, ha, v, hv, rfl⟩ := ih
      refine ⟨a⁻¹, A.inv_mem ha, v⁻¹, V.inv_mem hv, ?_⟩
      rw [mul_inv_rev, hc a⁻¹ (A.inv_mem ha) v⁻¹ (V.inv_mem hv)]

theorem y7a_commhom {A V W Z : Subgroup G} {t : G} [hZ : (Z.subgroupOf A).Normal]
    (hAV : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) (hVV : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v)
    (hAA : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ V) (hAVZ : A ⊓ V = Z)
    (hWAV : ∀ m ∈ W, ∀ x ∈ A ⊔ V, ⁅m, x⁆ ∈ V) (hmt : ∀ m ∈ W, ⁅m, t⁆ ∈ A ⊔ V) :
    ∃ f : ↥W →* ↥A ⧸ Z.subgroupOf A,
      (∀ (m : ↥W) (a : ↥A), (a : G)⁻¹ * ⁅(m : G), t⁆ ∈ V → f m = (a : ↥A ⧸ Z.subgroupOf A)) ∧
      ∀ m : ↥W, ∃ a : ↥A, (a : G)⁻¹ * ⁅(m : G), t⁆ ∈ V := by
  classical
  have hex : ∀ m : ↥W, ∃ a : ↥A, (a : G)⁻¹ * ⁅(m : G), t⁆ ∈ V := by
    intro m
    obtain ⟨a, ha, v, hv, huv⟩ := mem_sup_of_commute hAV (hmt (m : G) m.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have hv' : (a : G)⁻¹ * (a * v) = v := by group
    rw [huv, hv']
    exact hv
  have hex' := hex
  choose aM haM using hex
  have huniq : ∀ (m : ↥W) (a a' : ↥A),
      (a : G)⁻¹ * ⁅(m : G), t⁆ ∈ V → (a' : G)⁻¹ * ⁅(m : G), t⁆ ∈ V →
      (a : ↥A ⧸ Z.subgroupOf A) = (a' : ↥A ⧸ Z.subgroupOf A) := by
    intro m a a' ha ha'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmemV : (a : G)⁻¹ * (a' : G) ∈ V := by
      have h1 : ((a : G)⁻¹ * ⁅(m : G), t⁆) * ((a' : G)⁻¹ * ⁅(m : G), t⁆)⁻¹ ∈ V :=
        V.mul_mem ha (V.inv_mem ha')
      have h2 : ((a : G)⁻¹ * ⁅(m : G), t⁆) * ((a' : G)⁻¹ * ⁅(m : G), t⁆)⁻¹
          = (a : G)⁻¹ * (a' : G) := by group
      rwa [h2] at h1
    have hmemA : (a : G)⁻¹ * (a' : G) ∈ A :=
      A.mul_mem (A.inv_mem a.2) a'.2
    have hmemZ : (a : G)⁻¹ * (a' : G) ∈ Z := by
      rw [← hAVZ]
      exact ⟨hmemA, hmemV⟩
    simpa using hmemZ
  have hclass_comm : ∀ a a' : ↥A,
      ((a' * a : ↥A) : ↥A ⧸ Z.subgroupOf A) = ((a * a' : ↥A) : ↥A ⧸ Z.subgroupOf A) := by
    intro a a'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmemV : (a : G)⁻¹ * (a' : G)⁻¹ * (a : G) * (a' : G) ∈ V := by
      have hdV : (a' : G)⁻¹ * (a : G) * (a' : G) * (a : G)⁻¹ ∈ V := by
        have h1 : (a' : G)⁻¹ * (a : G) * (a' : G) * (a : G)⁻¹
            = (a' : G)⁻¹ * ⁅(a : G), (a' : G)⁆ * (a' : G) := by
          rw [commutatorElement_def]; group
        rw [h1, inv_mul_eq_of_commute (hAV a' a'.2 _ (hAA a a.2 a' a'.2))]
        exact hAA a a.2 a' a'.2
      have h2 : (a : G)⁻¹ * (a' : G)⁻¹ * (a : G) * (a' : G)
          = (a : G)⁻¹ * ((a' : G)⁻¹ * (a : G) * (a' : G) * (a : G)⁻¹) * (a : G) := by
        group
      rw [h2, inv_mul_eq_of_commute (hAV a a.2 _ hdV)]
      exact hdV
    have hmemA : (a : G)⁻¹ * (a' : G)⁻¹ * (a : G) * (a' : G) ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem (A.inv_mem a.2) (A.inv_mem a'.2)) a.2) a'.2
    have hmemZ : (a : G)⁻¹ * (a' : G)⁻¹ * (a : G) * (a' : G) ∈ Z := by
      rw [← hAVZ]
      exact ⟨hmemA, hmemV⟩
    simpa [mul_assoc] using hmemZ
  refine ⟨MonoidHom.mk' (fun m : ↥W => ((aM m : ↥A) : ↥A ⧸ Z.subgroupOf A)) ?_, ?_, hex'⟩
  · intro m m'
    have hprop : ((aM m' * aM m : ↥A) : G)⁻¹ * ⁅((m * m' : ↥W) : G), t⁆ ∈ V := by
      simp only [Subgroup.coe_mul]
      set a : G := (aM m : G) with ha_def
      set a' : G := (aM m' : G) with ha'_def
      set u : G := ⁅(m : G), t⁆ with hu_def
      set u' : G := ⁅(m' : G), t⁆ with hu'_def
      set w : G := ⁅(m : G), u'⁆ with hw_def
      set v : G := a⁻¹ * u with hv_def
      set v' : G := a'⁻¹ * u' with hv'_def
      have ha : a⁻¹ * u ∈ V := by simpa [ha_def, hu_def] using haM m
      have ha' : a'⁻¹ * u' ∈ V := by simpa [ha'_def, hu'_def] using haM m'
      have hv : v ∈ V := by simpa [hv_def] using ha
      have hv' : v' ∈ V := by simpa [hv'_def] using ha'
      have hmemA : a ∈ A := by simpa [ha_def] using (aM m).2
      have hmemA' : a' ∈ A := by simpa [ha'_def] using (aM m').2
      have hmemAV : u' ∈ A ⊔ V := by simpa [hu'_def] using hmt m' m'.2
      have hw : w ∈ V := by
        rw [hw_def]
        exact hWAV m m.2 u' hmemAV
      have hcomm1 : w * a' = a' * w := (hAV a' hmemA' w hw).symm
      have hcomm2 : v' * a = a * v' := (hAV a hmemA v' hv').symm
      have hcomm3 : w * a = a * w := (hAV a hmemA w hw).symm
      have hkey : ⁅(m : G) * (m' : G), t⁆ = w * a' * v' * a * v := by
        rw [hw_def, hv_def, hv'_def, hu_def, hu'_def, ha_def, ha'_def]
        simp only [commutatorElement_def]
        group
      have hkey2 : (a' * a)⁻¹ * (w * a' * v' * a * v) = w * v' * v := by
        calc (a' * a)⁻¹ * (w * a' * v' * a * v)
            = a⁻¹ * a'⁻¹ * (w * a') * v' * a * v := by group
          _ = a⁻¹ * a'⁻¹ * (a' * w) * v' * a * v := by rw [hcomm1]
          _ = a⁻¹ * a'⁻¹ * a' * w * (v' * a) * v := by group
          _ = a⁻¹ * a'⁻¹ * a' * w * (a * v') * v := by rw [hcomm2]
          _ = a⁻¹ * (w * a) * v' * v := by group
          _ = a⁻¹ * (a * w) * v' * v := by rw [hcomm3]
          _ = w * v' * v := by group
      have hgoal : (a' * a)⁻¹ * ⁅(m : G) * (m' : G), t⁆ ∈ V := by
        rw [hkey, hkey2]
        exact V.mul_mem (V.mul_mem hw hv') hv
      simpa [ha_def, ha'_def] using hgoal
    have h1 : ((aM (m * m') : ↥A) : ↥A ⧸ Z.subgroupOf A)
        = ((aM m' * aM m : ↥A) : ↥A ⧸ Z.subgroupOf A) :=
      huniq (m * m') (aM (m * m')) (aM m' * aM m) (haM (m * m')) hprop
    have h2 : ((aM m' * aM m : ↥A) : ↥A ⧸ Z.subgroupOf A)
        = ((aM m * aM m' : ↥A) : ↥A ⧸ Z.subgroupOf A) :=
      hclass_comm (aM m) (aM m')
    rw [h1, h2]
    rfl
  · intro m a ha
    exact huniq m (aM m) a (haM m) ha

end CFSG.OddStandard.HigherRank.YamadaG23
