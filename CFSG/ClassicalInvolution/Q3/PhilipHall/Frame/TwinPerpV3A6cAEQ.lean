module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cConj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr

section Vec

variable {n : ℕ}

theorem permQ_zBar (α : Finset (Fin n)) (h : α.card = 4) : TC.Thin.permQ n (zBar α h) = 1 := by
  rw [zBar_eq]
  rfl

theorem exists_vec_of_perm_one {x : AEQ n} (hx : TC.Thin.permQ n x = 1) :
    ∃ v : Fin n → ZMod 2, x = mkQ n (ofVec v) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨a.vec, ?_⟩
  have hp : a.perm = 1 := hx
  have : a = ofVec a.vec := Wr.ext rfl hp
  exact congrArg (mkQ n) this

theorem V_comm {x y : AEQ n} (hx : TC.Thin.permQ n x = 1) (hy : TC.Thin.permQ n y = 1) : x * y = y * x := by
  obtain ⟨f, rfl⟩ := exists_vec_of_perm_one hx
  obtain ⟨g, rfl⟩ := exists_vec_of_perm_one hy
  rw [← ofVec_add, ← ofVec_add, add_comm]

theorem V_sq {x : AEQ n} (hx : TC.Thin.permQ n x = 1) : x * x = 1 :=
  TC.Thin.mul_self_of_mem_ker_permQ (MonoidHom.mem_ker.mpr hx)

end Vec

section U

@[expose] def InU (x : AEQ 6) : Prop := x ∈ TL4.aeModel 6 ∧ TC.Thin.permQ 6 x = 1

theorem inU_iff {x : AEQ 6} : InU x ↔ ∃ v : Fin 6 → ZMod 2, ∑ i, v i = 0 ∧ x = mkQ 6 (ofVec v) := by
  constructor
  · rintro ⟨hx, hp⟩
    obtain ⟨a, ha, rfl⟩ := hx
    have hpa : a.perm = 1 := hp
    refine ⟨a.vec, (mem_aeSub.mp ha).1, ?_⟩
    have : a = ofVec a.vec := Wr.ext rfl hpa
    exact congrArg (mkQ 6) this
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨ofVec v, mem_aeSub.mpr ⟨hv, ?_⟩, rfl⟩, rfl⟩
    show Equiv.Perm.sign (1 : Equiv.Perm (Fin 6)) = 1
    exact Equiv.Perm.sign_one

theorem inU_zBar (α : Finset (Fin 6)) (h : α.card = 4) : InU (zBar α h) :=
  ⟨zBar_mem_aeModel α h, permQ_zBar α h⟩

theorem sixteen_le_card_U : 16 ≤ Nat.card {x : AEQ 6 // InU x} := by
  classical
  let D := {v : Fin 6 → ZMod 2 // ∑ i, v i = 0 ∧ v 0 = 0}
  have hD : Nat.card D = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let f : D → {x : AEQ 6 // InU x} := fun v => ⟨mkQ 6 (ofVec v.1), inU_iff.mpr ⟨v.1, v.2.1, rfl⟩⟩
  have hf : Function.Injective f := by
    intro v v' hvv
    have h1 : mkQ 6 (ofVec v.1) = mkQ 6 (ofVec v'.1) := congrArg Subtype.val hvv
    have hv1 : mkQ 6 (ofVec v.1) * mkQ 6 (ofVec v.1) = 1 := V_sq rfl
    have h2 : mkQ 6 (ofVec (v.1 + v'.1)) = 1 := by
      rw [ofVec_add, ← h1]
      exact hv1
    have h3 : ofVec (v.1 + v'.1) ∈ piSub 6 := (QuotientGroup.eq_one_iff _).mp h2
    rcases mem_piSub.mp h3 with h4 | h4
    · apply Subtype.ext
      funext i
      have := congrFun (congrArg Wr.vec h4) i
      have h5 : v.1 i + v'.1 i = 0 := this
      have h6 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h6 _ _ h5
    · exfalso
      have := congrFun (congrArg Wr.vec h4) 0
      have h5 : v.1 0 + v'.1 0 = 1 := this
      rw [v.2.2, v'.2.2] at h5
      exact absurd h5 (by decide)
  have := Nat.card_le_card_of_injective f hf
  rwa [hD] at this

theorem centV (g : AEQ 6) (hg : ∀ x : AEQ 6, InU x → g * x = x * g) : TC.Thin.permQ 6 g = 1 := by
  obtain ⟨v, rfl⟩ := eq_vec_of_comm_zBar (by norm_num) g fun α h => hg _ (inU_zBar α h)
  rfl

end U

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
