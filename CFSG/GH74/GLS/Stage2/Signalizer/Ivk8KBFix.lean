module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cert
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gGraph

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.PSL3Four

theorem fixSub_congr {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y') (α : MulAut Y) :
    (fixSub α).map ψ.toMonoidHom = fixSub (MulAut.congr ψ α) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub]
  constructor
  · intro h
    have : MulAut.congr ψ α y = ψ (α (ψ.symm y)) := rfl
    rw [this, h, MulEquiv.apply_symm_apply]
  · intro h
    have h1 : ψ (α (ψ.symm y)) = y := h
    have h2 := congrArg ψ.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2

theorem card_of_unitaryFix {Y : Type} [Group Y] {α : MulAut Y} (h : UnitaryFix α) :
    Nat.card (fixSub α) = 72 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h : Nat.card (StatedProj (StatedSU 3 (2 ^ 1) F)) = _ :=
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) (p := 2) (f := 1)
      (n := 3) Nat.prime_two le_rfl (by rw [hF]; norm_num) (by norm_num)
  have h' : Nat.card (StatedProj (StatedSU 3 2 F)) = _ := h
  rw [h']
  decide

@[expose] def Rinc (s : ↥S) : ↥R := ⟨(s : Equiv.Perm (Fin 42)), S_le_R s.2⟩

theorem conjIso_Rinc (s : ↥S) :
    Cls3.conjIso (Rinc s) = MulAut.conj s := MulEquiv.ext fun _ => Subtype.ext rfl

theorem conjIso_symm_conj (s : ↥S) :
    Cls3.conjIso.symm (MulAut.conj s) = Rinc s := by
  rw [MulEquiv.symm_apply_eq, conjIso_Rinc]

theorem congr_trans {A B C : Type} [Group A] [Group B] [Group C] (ψ : A ≃* B) (β : B ≃* C)
    (α : MulAut A) : MulAut.congr (ψ.trans β) α = MulAut.congr β (MulAut.congr ψ α) := rfl

theorem exists_mulEquiv_r₄ {Y : Type} [Group Y] [Finite Y]
    (ψ : Y ≃* ↥S) {α : MulAut Y} (h2 : α * α = 1) (h72 : Nat.card (fixSub α) = 72) :
    ∃ χ : Y ≃* ↥S, MulAut.congr χ α = Cls3.conjIso (rrR 3) := by
  set α' : MulAut ↥S := MulAut.congr ψ α with hα'
  have h2' : α' * α' = 1 := by rw [hα', ← map_mul, h2, map_one]
  have h72' : Nat.card (fixSub α') = 72 := by
    rw [← h72]
    exact P85.card_fixSub_congr ψ α
  have h1' : α' ≠ 1 := by
    intro h
    rw [h] at h72'
    have : fixSub (1 : MulAut ↥S) = ⊤ := by ext y; simp [mem_fixSub]
    rw [this, Subgroup.card_top, card_S] at h72'
    omega
  obtain ⟨i, β, hβ⟩ := exists_class_rep h2' h1'
  have hi : i = 3 := by
    have hc : Nat.card (CC i) = 72 := by
      rw [← P85.card_fixSub_conjIso, ← hβ]
      exact (P85.card_fixSub_congr β α').trans h72'
    rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) i with rfl | rfl | rfl | rfl
    · rw [CC_zero, card_C₁] at hc; omega
    · rw [CC_one, card_C₂] at hc; omega
    · rw [CC_two, card_C₃] at hc; omega
    · rfl
  subst hi
  exact ⟨ψ.trans β, by rw [congr_trans]; exact hβ⟩



theorem map_fixSub_r₄ {Y : Type} [Group Y] {α : MulAut Y}
    (χ : Y ≃* ↥S) (hχ : MulAut.congr χ α = Cls3.conjIso (rrR 3)) :
    (fixSub α).map χ.toMonoidHom = C₄.subgroupOf S := by
  rw [fixSub_congr, hχ]
  exact P85.fixSub_conjIso 3

@[expose] noncomputable def toR {Y : Type} [Group Y]
    (ψ : Y ≃* ↥S) : MulAut Y ≃* ↥R :=
  (MulAut.congr ψ).trans Cls3.conjIso.symm

theorem toR_conj {Y : Type} [Group Y] (ψ : Y ≃* ↥S) (y : Y) :
    toR ψ (MulAut.conj y) = Rinc (ψ y) := by
  show Cls3.conjIso.symm (MulAut.congr ψ (MulAut.conj y)) = _
  rw [congr_conj, conjIso_symm_conj]


theorem pRank_eq_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    CFSG.pRank p X = CFSG.pRank p Y := by
  have key : ∀ {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (r : ℕ),
      (∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = p ^ r) →
      ∃ A : Subgroup Y, IsElementaryAbelian p A ∧ Nat.card A = p ^ r := by
    intro X Y _ _ e r ⟨A, hA, hc⟩
    exact ⟨A.map e.toMonoidHom, Transport.isElementaryAbelian_of_mulEquiv
      (A.equivMapOfInjective e.toMonoidHom e.injective) hA,
      by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  unfold CFSG.pRank
  congr 1
  ext r
  exact ⟨key e r, key e.symm r⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
