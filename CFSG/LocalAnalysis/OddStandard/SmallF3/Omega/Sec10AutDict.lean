module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameTrans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem QA45_cent_trivial {a : P45}
    (ha : a ∈ QA45.originalSubgroup) (h : ∀ x ∈ QP45.originalSubgroup, a * x = x * a) :
    a = 1 := by
  by_contra hne
  have h1 := List.all_eq_true.1 cent_ok a ((mem_elemsT QA45 QA45_ok a).2 ha)
  have hx : x45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : y45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  simp [h x45 hx, h y45 hy, hne] at h1

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

theorem conjA_unique {a b : P45}
    (ha : a ∈ QA45.originalSubgroup) (hb : b ∈ QA45.originalSubgroup)
    (h : ∀ l : ↥L, a * F.ψ l * a⁻¹ = b * F.ψ l * b⁻¹) : a = b := by
  have hc : b⁻¹ * a = 1 := by
    refine QA45_cent_trivial (QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.inv_mem hb) ha)
      fun x hx => ?_
    obtain ⟨l, rfl⟩ := F.ψ_surj hx
    calc b⁻¹ * a * F.ψ l = b⁻¹ * (a * F.ψ l * a⁻¹) * a := by group
      _ = b⁻¹ * (b * F.ψ l * b⁻¹) * a := by rw [h l]
      _ = F.ψ l * (b⁻¹ * a) := by group
  exact (inv_mul_eq_one.1 hc).symm

theorem exists_conjA (hL : IsPSp43 L) (σ : MulAut ↥L) :
    ∃ a ∈ QA45.originalSubgroup, ∀ l : ↥L, F.ψ (σ l) = a * F.ψ l * a⁻¹ := by
  obtain ⟨e0⟩ := PSp43.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := PSp43.exists_model e0
  have hψM : ∀ l : ↥L, F.ψ l ∈ M.P := fun l => hMP ▸ F.ψ_mem l
  let ψe : ↥L ≃* ↥M.P := MulEquiv.ofBijective (F.ψ.codRestrict M.P hψM)
    ⟨fun l l' h => F.ψ_injective (congrArg Subtype.val h), fun p => by
      obtain ⟨l, hl⟩ := F.ψ_surj (p := p) (by rw [← hMP]; exact p.2)
      exact ⟨l, Subtype.ext hl⟩⟩
  let ν : MulAut ↥L := ψe.trans M.e.symm
  let φ' : MulAut ↥L := ν.symm.trans (σ.trans ν)
  have hν : ∀ l : ↥L, ((M.e (ν l) : ↥M.P) : P45) = F.ψ l := by
    intro l
    have h : M.e (ν l) = ψe l := by simp [ν]
    rw [h]
    rfl
  refine ⟨(M.Φ φ' : P45), hMA ▸ (M.Φ φ').2, fun l => ?_⟩
  have hs := M.spec φ' (ν l)
  have h1 : φ' (ν l) = ν (σ l) := by simp [φ']
  rw [h1, hν, hν] at hs
  exact hs

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
