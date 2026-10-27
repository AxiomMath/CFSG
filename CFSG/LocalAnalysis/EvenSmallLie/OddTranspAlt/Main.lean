module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Build
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Connect

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

namespace Cfg

variable {G : Type} [Group G] [Finite G] {n : ℕ} (c : Cfg G n)

theorem exists_equiv :
    ∃ φ : Subgroup.closure (cls c.t) ≃* Perm (Fin (n + 2)),
      ∀ x : Subgroup.closure (cls c.t), (x : G) ∈ cls c.t ↔ (φ x).IsSwap := by
  obtain ⟨emb⟩ := c.nonempty_embedding
  have hot : ∀ x ∈ cls c.t, ∀ y ∈ cls c.t, Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2 :=
    fun x hx y hy => c.ot_cls hx hy
  have hsub := cls_subset_of_nbr c.ht hot (m := n + 2) (by have := c.hn; omega) emb.ψ emb.inj
    emb.swap_mem emb.nbr
  have hrange : emb.ψ.range = Subgroup.closure (cls c.t) := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨σ, hσ, rfl⟩
      exact emb.swap_mem σ hσ
    · rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨τ, _, rfl⟩ := hsub x hx
      exact ⟨τ, rfl⟩
  let e : Perm (Fin (n + 2)) ≃* Subgroup.closure (cls c.t) :=
    (MonoidHom.ofInjective emb.inj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨e.symm, fun x => ?_⟩
  obtain ⟨σ, rfl⟩ : ∃ σ, e σ = x := ⟨e.symm x, e.apply_symm_apply x⟩
  rw [e.symm_apply_apply]
  have hval : ((e σ : Subgroup.closure (cls c.t)) : G) = emb.ψ σ := by
    simp [e, MonoidHom.ofInjective_apply]
  rw [hval]
  refine ⟨fun hx => ?_, fun hσ => emb.swap_mem σ hσ⟩
  obtain ⟨τ, hτ, hψτ⟩ := hsub _ hx
  rw [← emb.inj hψτ]
  exact hτ

end Cfg

theorem oddTranspAlt {G : Type} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    (hot : ∀ x ∈ cls t, ∀ y ∈ cls t, Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2)
    {n : ℕ} (hn : 7 ≤ n) {Y : Subgroup G}
    (hY : IsComponentOf Y (Subgroup.centralizer ({t} : Set G)))
    (hYle : Y ≤ Subgroup.closure (cls t)) (hYA : Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hk2 : ∀ e ∈ cls t, e ≠ t → t * e = e * t → e ∉ Subgroup.centralizer (Y : Set G)) :
    ∃ φ : Subgroup.closure (cls t) ≃* Perm (Fin (n + 2)),
      ∀ x : Subgroup.closure (cls t), (x : G) ∈ cls t ↔ (φ x).IsSwap := by
  obtain ⟨ε⟩ := hYA
  have ot : ∀ e : G, orderOf (t * (e * t * e⁻¹)) = 1 ∨ orderOf (t * (e * t * e⁻¹)) = 2 ∨
      Odd (orderOf (t * (e * t * e⁻¹))) := by
    intro e
    rcases hot t self_mem_cls (e * t * e⁻¹) (conj_mem_cls self_mem_cls e) with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  exact (⟨t, ht, ot, hn, Y, hY, hYle, ε, hk2⟩ : Cfg G n).exists_equiv

end CFSG.EvenSmallLie.OddTranspAlt
