module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutNOne

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F L1 : Subgroup G}

namespace OutOne

theorem normalizer_inf_centralizer_z_eq (h : OutOne L z F)
   
    (hnorm : ∀ n : G, (∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) →
      ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1)
    (hcz : ∀ x ∈ L1, z * x = x * z → x ∈ F) (hFL1 : F ≤ L1) :
    normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) =
      normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcX, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcz' : c * z = z * c := mem_centralizer_singleton_iff.1 hcC
    have hcX' := Subgroup.mem_normalizer_iff.1 hcX
    have hcF : ∀ x ∈ F, c * x * c⁻¹ ∈ F := by
      intro x hx
      refine hcz _ ((hcX' x).1 (hFL1 hx)) ?_
      have hzx : z * x = x * z := h.z_comm x (h.F_le hx)
      calc z * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by
            rw [show z * (c * x * c⁻¹) = (z * c) * x * c⁻¹ by group, ← hcz']; group
        _ = c * (x * z) * c⁻¹ := by rw [hzx]
        _ = (c * x * c⁻¹) * z := by
            rw [show c * (x * z) * c⁻¹ = c * x * (z * c⁻¹) by group,
              show z * c⁻¹ = c⁻¹ * z by
                rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcz', inv_mul_cancel_left]]
            group
    have hcF' := forall_mem_iff_of_forall_mem hcF
    have hcz'' : c * z * c⁻¹ = z * 1 := by
      rw [hcz', mul_one]; group
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2
      (mem_normalizer_sup h hcF' (Subgroup.one_mem F) hcz''), hcC⟩
  · intro c hc
    obtain ⟨hcE, hcC⟩ := Subgroup.mem_inf.1 hc
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2
      (hnorm c (Subgroup.mem_normalizer_iff.1 hcE)), hcC⟩

theorem centralizer_X_z_inf_C (h : OutOne L z F)
    (hnorm : ∀ n : G, (∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) →
      ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1)
    (hcz : ∀ x ∈ L1, z * x = x * z → x ∈ F) (hFL1 : F ≤ L1)
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x) (hcard : Nat.card L1 = 256)
    (hK : Ksub z F = L1 ⊔ zpowers z) (hznorm : ∀ x, x ∈ L1 ↔ z * x * z⁻¹ ∈ L1) :
    normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) ⊓ centralizer (L1 : Set G) = F := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcXz, hcC⟩ := Subgroup.mem_inf.1 hc
    rw [normalizer_inf_centralizer_z_eq h hnorm hcz hFL1] at hcXz
    obtain ⟨hcE, hczc⟩ := Subgroup.mem_inf.1 hcXz
    have hcz' : z * c = c * z := (mem_centralizer_singleton_iff.1 hczc).symm
    have hcL1 : ∀ x ∈ L1, x * c = c * x := fun x hx => mem_centralizer_iff.1 hcC x hx
    have hcK : c ∈ Ksub z F := by
      rw [mem_Ksub]
      exact ⟨Subgroup.mem_normalizer_iff.1 hcE, fun f hf => hcL1 f (hFL1 hf)⟩
    rw [hK] at hcK
    rcases mem_sup_zpowers_cases h.z_mul_self hznorm hcK with hcl | ⟨l, hl, rfl⟩
    · exact hcz c hcl hcz'
    · exfalso
      have hzx : ∀ x ∈ L1, z * x = x * z := by
        intro x hx
        have e := hcL1 x hx
        have e2 : l * x = x * l := hcomm l hl x hx
        have e3 : l * (z * x) = l * (x * z) := by
          calc l * (z * x) = (l * z) * x := by group
            _ = x * (l * z) := e.symm
            _ = (x * l) * z := by group
            _ = (l * x) * z := by rw [e2]
            _ = l * (x * z) := by group
        exact mul_left_cancel e3
      have hLF : L1 ≤ F := fun x hx => hcz x hx (hzx x hx)
      have := Subgroup.card_le_of_le hLF
      rw [hcard, h.F_card] at this
      omega
  · intro f hf
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (hFL1 hf), ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.2 (h.z_comm f (h.F_le hf)).symm
    · exact mem_centralizer_iff.2 fun x hx => hcomm x hx f (hFL1 hf)

end OutOne

end CFSG.EvenSporadicStandard.M22Std
