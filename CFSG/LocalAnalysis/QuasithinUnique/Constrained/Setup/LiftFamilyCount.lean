module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDeleted

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
open scoped LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Count

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem card_V_eq_prod (ctx : FamilyCtx H T n F r Lc) :
    Nat.card V = Nat.card ↥(fixGL (oddGen H)) *
      ∏ i, Nat.card (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) := by
  classical
  set C : Submodule (ZMod 2) V := fixGL (oddGen H) with hC
  let S' : (∀ i, ↥(commGL (Lc i) ⊤)) →ₗ[ZMod 2] V :=
    ∑ i, (commGL (Lc i) ⊤).subtype ∘ₗ LinearMap.proj i
  have hS' : ∀ x, S' x = ∑ i, (x i : V) := fun x => by
    simp [S', LinearMap.sum_apply]
  let Ψ : (∀ i, ↥(commGL (Lc i) ⊤)) →ₗ[ZMod 2] (V ⧸ C) := C.mkQ ∘ₗ S'
  have hsurj : Function.Surjective Ψ := by
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective C q
    have hv : v ∈ (⨆ i, commGL (Lc i) ⊤) ⊔ C := by
      rw [V_sum ctx]
      trivial
    obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨x, hx, rfl⟩ := mem_iSup_exists_sum _ hy
    refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
    show C.mkQ (S' _) = Submodule.Quotient.mk _
    rw [hS', Submodule.mkQ_apply, Submodule.Quotient.eq]
    simpa using C.neg_mem hc
  have hker : LinearMap.ker Ψ =
      Submodule.pi Set.univ (fun i => fixIn (Lc i) (commGL (Lc i) ⊤)) := by
    ext x
    rw [LinearMap.mem_ker]
    show C.mkQ (S' x) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hS']
    constructor
    · intro hs
      exact Submodule.mem_pi.2 fun i _ => sum_direct ctx (fun i => (x i : V)) (fun i => (x i).2) hs i
    · intro hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : (x i : V) ∈ commGL (Lc i) ⊤ ⊓ fixGL (Lc i) :=
        ⟨(x i).2, Submodule.mem_pi.1 hx i (Set.mem_univ i)⟩
      rw [← I_inf_C ctx i] at h1
      exact h1.2
  have hc1 := natCard_eq_ker_mul_range Ψ
  rw [LinearMap.range_eq_top.2 hsurj, Nat.card_congr (Submodule.topEquiv (R := ZMod 2)
    (M := V ⧸ C)).toEquiv, hker, Nat.card_pi] at hc1
  have hkcard : Nat.card ↥(Submodule.pi Set.univ
      (fun i => fixIn (Lc i) (commGL (Lc i) ⊤))) =
      ∏ i, Nat.card ↥(fixIn (Lc i) (commGL (Lc i) ⊤)) := by
    rw [← Nat.card_pi]
    refine Nat.card_congr
      { toFun := fun x => fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
        invFun := fun f => ⟨fun i => (f i : ↥(commGL (Lc i) ⊤)), fun i _ => (f i).2⟩
        left_inv := fun x => rfl
        right_inv := fun f => rfl }
  rw [hkcard] at hc1
  have hI : ∀ i, Nat.card ↥(commGL (Lc i) ⊤) =
      Nat.card ↥(fixIn (Lc i) (commGL (Lc i) ⊤)) *
        Nat.card (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) := fun i =>
    Submodule.card_eq_card_quotient_mul_card _
  simp only [hI, Finset.prod_mul_distrib] at hc1
  have hpos : 0 < ∏ i, Nat.card ↥(fixIn (Lc i) (commGL (Lc i) ⊤)) :=
    Finset.prod_pos fun i _ => Nat.card_pos
  have hVC : Nat.card (V ⧸ C) = ∏ i, Nat.card (↥(commGL (Lc i) ⊤) ⧸
      fixIn (Lc i) (commGL (Lc i) ⊤)) := by
    exact Nat.eq_of_mul_eq_mul_left hpos hc1.symm
  rw [← hVC]
  exact Submodule.card_eq_card_quotient_mul_card C

end Count

end CFSG.QuasithinUnique.Setup.Lift
