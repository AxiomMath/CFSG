module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.IVK
open scoped commutatorElement

namespace OrdOut

theorem commutator_mem_of_zpowers_cyclic {G : Type} [Group G] (I : Subgroup G) [I.Normal] (t : G)
    (Φ : Subgroup G) (hcyc : IsCyclic ↥Φ) (htop : I ⊔ Subgroup.zpowers t ⊔ Φ = ⊤)
    (hcomm : ∀ x ∈ Φ, ∀ y ∈ I ⊔ Subgroup.zpowers t, ⁅x, y⁆ ∈ I) (α β : G) :
    ⁅α, β⁆ ∈ I := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Φ).mp hcyc
  let π : G →* G ⧸ I := QuotientGroup.mk' I
  have hgΦ : g ∈ Φ := hg ▸ Subgroup.mem_zpowers g
  have htM : t ∈ I ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcommute : Commute (π g) (π t) := by
    have h1 : ⁅g, t⁆ ∈ I := hcomm g hgΦ t htM
    have h2 : π ⁅g, t⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hle : I ⊔ Subgroup.zpowers t ⊔ Φ ≤
      (Subgroup.closure ({π t, π g} : Set (G ⧸ I))).comap π := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show π x ∈ Subgroup.closure ({π t, π g} : Set (G ⧸ I))
      rw [h1]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le]
      show π t ∈ Subgroup.closure ({π t, π g} : Set (G ⧸ I))
      exact Subgroup.subset_closure (by simp)
    · rw [← hg, Subgroup.zpowers_le]
      show π g ∈ Subgroup.closure ({π t, π g} : Set (G ⧸ I))
      exact Subgroup.subset_closure (by simp)
  have hmem : ∀ a : G, π a ∈ Subgroup.closure ({π t, π g} : Set (G ⧸ I)) :=
    fun a => hle (htop ▸ Subgroup.mem_top a)
  have hcommClosure : ∀ x y : G ⧸ I, x ∈ Subgroup.closure ({π t, π g} : Set (G ⧸ I)) →
      y ∈ Subgroup.closure ({π t, π g} : Set (G ⧸ I)) → Commute x y := by
    intro x y hx hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact hcommute.symm
      · exact hcommute
      · exact Commute.refl _
    | one_left x _ => exact Commute.one_left _
    | one_right x _ => exact Commute.one_right _
    | mul_left x y z _ _ _ hxz hyz => exact hxz.mul_left hyz
    | mul_right y z x _ _ _ hxy hxz => exact hxy.mul_right hxz
    | inv_left x y _ _ h => exact h.inv_left
    | inv_right x y _ _ h => exact h.inv_right
  have hαβ : Commute (π α) (π β) := hcommClosure _ _ (hmem α) (hmem β)
  have h3 : π ⁅α, β⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hαβ
  exact (QuotientGroup.eq_one_iff _).mp h3

end OrdOut

theorem out_abelian {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] [Finite K]
    (e : K ≃* L2 F) (α β : MulAut K) : ⁅α, β⁆ ∈ innAut K := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 (MulAut K)) := inferInstance
  obtain ⟨e', N, -⟩ := ivk_1_2a_exists F hF K e T
  obtain ⟨htop, hcyc, -, hcomm⟩ := ivk_1_2a_struct F hF K e' N
  exact OrdOut.commutator_mem_of_zpowers_cyclic (innAut K) N.t (fieldAutSub e') hcyc htop hcomm α β

end CFSG.GH74.GLS.SP.Local
