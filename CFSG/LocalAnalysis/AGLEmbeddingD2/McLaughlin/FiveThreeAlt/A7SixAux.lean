module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixBlock

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.HardMathSupport.Cooperstein.Coordinator

theorem altHeart_seven_fixed (v : altHeart 7)
    (hv : ∀ σ ∈ alternatingGroup (Fin 7), altAct σ v = v) : v = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  exact altHeart_fixed_eq_zero (by norm_num) x fun σ hσ => hv σ hσ

theorem eq_of_equivariant {N G0 : Type} [Group N] (r : G0 → N → N) (α : G0 → Perm (Fin 7))
    (hα : ∀ σ ∈ alternatingGroup (Fin 7), ∃ k, α k = σ)
    (φ φ' : N →* Multiplicative (altHeart 7)) (hφb : Function.Bijective φ)
    (hφ'i : Function.Injective φ')
    (e1 : ∀ k u, Multiplicative.toAdd (φ (r k u)) = altAct (α k) (Multiplicative.toAdd (φ u)))
    (e2 : ∀ k u, Multiplicative.toAdd (φ' (r k u)) =
      altAct (α k) (Multiplicative.toAdd (φ' u))) :
    φ' = φ := by
  let eφ : N ≃* Multiplicative (altHeart 7) := MulEquiv.ofBijective φ hφb
  have heφ : ∀ u, eφ u = φ u := fun u => rfl
  let ε : altHeart 7 →+ altHeart 7 :=
    { toFun := fun v => Multiplicative.toAdd (φ' (eφ.symm (Multiplicative.ofAdd v)))
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hε : ∀ u, ε (Multiplicative.toAdd (φ u)) = Multiplicative.toAdd (φ' u) := fun u => by
    show Multiplicative.toAdd (φ' (eφ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (φ u))))) = _
    rw [ofAdd_toAdd, ← heφ, MulEquiv.symm_apply_apply]
  have hcomm : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v, ε (altAct σ v) = altAct σ (ε v) := by
    intro σ hσ v
    obtain ⟨k, hk⟩ := hα σ hσ
    obtain ⟨u, hu⟩ := hφb.2 (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (φ u) := by rw [hu]; rfl
    subst hv
    rw [← hk, ← e1 k u, hε, hε, e2 k u]
  rcases altHeart_endo_eq_zero_or_id (by norm_num) ε hcomm with h0 | h1
  · exfalso
    have hsub : ∀ u, φ' u = 1 := fun u => by
      have := hε u
      rw [h0] at this
      exact Multiplicative.toAdd.injective this.symm
    obtain ⟨a, ha⟩ := exists_ne_zero_altHeart
    obtain ⟨u, hu⟩ := hφb.2 (Multiplicative.ofAdd a)
    have h2 : u = 1 := hφ'i ((hsub u).trans (map_one φ').symm)
    rw [h2, map_one] at hu
    exact ha (congrArg Multiplicative.toAdd hu.symm)
  · ext u
    have := hε u
    rw [h1] at this
    exact Multiplicative.toAdd.injective this.symm

theorem exists_conj_of_surjective {L : Type*} [Group L] (eL : L ≃* alternatingGroup (Fin 7))
    (g : L →* alternatingGroup (Fin 7)) (hg : Function.Surjective g) :
    ∃ c : Perm (Fin 7), ∀ l : L,
      ((g l : alternatingGroup (Fin 7)) : Perm (Fin 7)) = c * (eL l : Perm (Fin 7)) * c⁻¹ := by
  have hs := isSimpleGroupAlt7
  let g' : alternatingGroup (Fin 7) →* alternatingGroup (Fin 7) := g.comp eL.symm.toMonoidHom
  have hg's : Function.Surjective g' := hg.comp eL.symm.surjective
  have hg'i : Function.Injective g' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g'.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff g').1 h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne_one_alt7
      obtain ⟨b, hb⟩ := hg's a
      have : b ∈ g'.ker := h ▸ Subgroup.mem_top b
      rw [MonoidHom.mem_ker] at this
      exact ha (hb.symm.trans this)
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  let α : MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective g' ⟨hg'i, hg's⟩
  refine ⟨cEquiv.symm α, fun l => ?_⟩
  have h1 : MulAut.conjNormal (cEquiv.symm α) = α := cEquiv.apply_symm_apply α
  have h2 := congrArg (fun f : MulAut (alternatingGroup (Fin 7)) =>
    ((f (eL l) : alternatingGroup (Fin 7)) : Perm (Fin 7))) h1
  simp only [MulAut.conjNormal_apply] at h2
  rw [h2]
  have h3 : α (eL l) = g l := by
    show g' (eL l) = g l
    simp [g']
  rw [h3]

theorem mem_sup_of_commute {X : Type*} [Group X] {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hx
    obtain ⟨a2, ha2, b2, hb2, rfl⟩ := hy
    refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
    have := h a2 ha2 b1 hb1
    calc a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by group
      _ = a1 * (a2 * b1) * b2 := by rw [this]
      _ = a1 * a2 * (b1 * b2) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a ha b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = a⁻¹ * b⁻¹ := by
        have h1 : a * b = b * a := this
        rw [← mul_inv_rev, ← mul_inv_rev, h1]

theorem span_subset_addClosure {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (S : Set M) :
    (Submodule.span (ZMod 2) S : Set M) ⊆ AddSubgroup.closure S := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact AddSubgroup.subset_closure hy
  | zero => exact AddSubgroup.zero_mem _
  | add y z _ _ hy hz => exact AddSubgroup.add_mem _ hy hz
  | smul c y _ hy =>
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]; exact AddSubgroup.zero_mem _
    · rw [one_smul]; exact hy

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
