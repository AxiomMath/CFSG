module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Frame

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm Classical

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

theorem pairEW_sub_pairEW (i j k : Fin N) :
    (pairEW i k : evenWeight N) - pairEW j k = pairEW i j := by
  apply Subtype.ext
  funext p
  simp only [AddSubgroup.coe_sub, Pi.sub_apply, pairEW_apply]
  have h : ∀ A B C : ZMod 2, A + C - (B + C) = A + B := by decide
  exact h _ _ _

namespace E0Frame

variable (E : E0Frame θ ρ U π L S P ω Δ₀ Y)
include E

theorem exists_off : ∃ x : Fin N, x ∉ Δ₀ := by
  classical
  by_contra h
  push Not at h
  have : (Finset.univ : Finset (Fin N)) ⊆ Δ₀ := fun x _ => h x
  have h1 := Finset.card_le_card this
  rw [Finset.card_univ, Fintype.card_fin, E.shape.card] at h1
  have := E.hN
  omega

theorem exists_in : ∃ a : Fin N, a ∈ Δ₀ := by
  have h4 := E.shape.card
  have : 0 < Δ₀.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 this
  exact ⟨a, ha⟩

theorem quad_ne_zero {a x₀ : Fin N} (ha : a ∈ Δ₀) (hx₀ : x₀ ∉ Δ₀) {h p : Perm (Fin N)}
    (hh : h ∈ P) (hp : p ∈ P) (hh1 : h ≠ 1) (hp1 : p ≠ 1) (hph : p ≠ h)
    {ε : Perm (Fin N)} (hε : ∀ y ∈ Δ₀, ε y = p y) :
    altAct ε (pairEW (h a) a : altHeart N) - (pairEW (h a) a : altHeart N) ≠ 0 := by
  have hha : h a ∈ Δ₀ := E.shape.P_mem hh ha
  have hpa : p a ∈ Δ₀ := E.shape.P_mem hp ha
  have h1 : p a ≠ a := fun e => hp1 (E.shape.reg hp ha e)
  have h2 : h a ≠ a := fun e => hh1 (E.shape.reg hh ha e)
  have h3 : p (h a) ≠ a := by
    intro e
    have hph1 : p * h ∈ P := mul_mem hp hh
    have : (p * h) a = a := by simpa [Perm.mul_apply] using e
    have h4 := E.shape.reg hph1 ha this
    apply hph
    have hhh : h * h = 1 := E.shape.Psq h hh
    calc p = p * (h * h) := by rw [hhh, mul_one]
      _ = (p * h) * h := by rw [mul_assoc]
      _ = h := by rw [h4, one_mul]
  rw [altAct_mk, evenWeightPerm_pairEW, hε _ hha, hε _ ha]
  intro hzero
  obtain ⟨r, hr⟩ := E.exists_off
  have := congrArg (fun v => altHeartCoord x₀ v a) (sub_eq_zero.1 hzero)
  simp only [altHeartCoord_mk, pairEW_apply] at this
  have hx1 : x₀ ≠ p (h a) := fun e => hx₀ (e ▸ E.shape.P_mem hp hha)
  have hx2 : x₀ ≠ p a := fun e => hx₀ (e ▸ hpa)
  have hx3 : x₀ ≠ h a := fun e => hx₀ (e ▸ hha)
  have hx4 : x₀ ≠ a := fun e => hx₀ (e ▸ ha)
  simp [hx1, hx2, hx3, hx4, h1.symm, h2.symm, Ne.symm h3] at this
  revert this
  decide

theorem exists_u {a x₀ : Fin N} (hx₀ : x₀ ∉ Δ₀) {h : Perm (Fin N)} (hh : h ∈ P) :
    ∃ u ∈ Y, ∃ hu : u ∈ U, π ⟨u, hu⟩ = (pairEW (h a) a : altHeart N) := by
  obtain ⟨v, hv⟩ := E.F.surj (pairEW a x₀ : altHeart N)
  obtain ⟨s, hs, hθs⟩ := (E.img h).2 (E0Shape.P_le_E0grp hh)
  refine ⟨ρ s v - v, E.hY1 s hs v, E.F.sub_mem_U s v.2, ?_⟩
  have := E.F.pi_sub s v
  rw [hθs, hv, altAct_mk, evenWeightPerm_pairEW, E.shape.Pfix h hh x₀ hx₀] at this
  have e : (⟨ρ s v - v, E.F.sub_mem_U s v.2⟩ : U) = ⟨ρ s ↑v - ↑v, E.F.sub_mem_U s v.2⟩ := rfl
  rw [e, this, ← QuotientAddGroup.mk_sub, pairEW_sub_pairEW]

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
