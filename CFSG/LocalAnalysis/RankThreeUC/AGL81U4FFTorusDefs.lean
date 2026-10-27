module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin Subgroup

class IsF2Space (V : Type*) [CommGroup V] : Prop where
  sq_eq_one : ∀ v : V, v ^ 2 = 1

variable {V : Type} [CommGroup V]

theorem IsF2Space.two_nsmul_eq_zero [IsF2Space V] (x : Additive V) : 2 • x = 0 := by
  have h : (Additive.toMul x) ^ 2 = 1 := IsF2Space.sq_eq_one _
  apply Additive.toMul.injective
  simpa [toMul_nsmul] using h

@[expose, reducible] def f2Module [IsF2Space V] : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (n := 2) IsF2Space.two_nsmul_eq_zero

attribute [local instance] f2Module

@[expose] noncomputable def linOf [IsF2Space V] (θ : MulAut V) : Module.End (ZMod 2) (Additive V) :=
  AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive θ).toAddMonoidHom

theorem linOf_apply [IsF2Space V] (θ : MulAut V) (x : V) :
    linOf θ (Additive.ofMul x) = Additive.ofMul (θ x) := rfl

@[expose] noncomputable def polyAct [IsF2Space V] (θ : MulAut V) (m : Polynomial (ZMod 2)) (x : V) :
    V :=
  Additive.toMul ((Polynomial.aeval (linOf θ) m) (Additive.ofMul x))

@[expose] def Rsub (Θ Θ' : Subgroup (MulAut V)) (M : Subgroup V) : Subgroup V :=
  commSub M Θ ⊓ fixV Θ'

@[expose] noncomputable def EE [Finite V] {c : ℕ} (Θi : Fin c → Subgroup (MulAut V)) : V →* V :=
  ∏ i, avgMap (Θi i)

structure IsTorusData (L : Subgroup (MulAut V)) (c : ℕ) (Θ : Subgroup (MulAut V))
    (Θi : Fin c → Subgroup (MulAut V)) (w θ₀ : MulAut V) (π : Equiv.Perm (Fin c)) : Prop where
  le_L : Θ ≤ L
  odd : Odd (Nat.card Θ)
  comm : ∀ a ∈ Θ, ∀ b ∈ Θ, a * b = b * a
  ne_bot : Θ ≠ ⊥
  Θi_le : ∀ i, Θi i ≤ Θ
  Θi_sup : ∀ i j, i ≠ j → Θi i ⊔ Θi j = Θ
  w_mem : w ∈ L
  w_Θ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ ∧ w⁻¹ * θ * w ∈ Θ
  w_Θi : ∀ i, (∀ g ∈ Θi i, w * g * w⁻¹ ∈ Θi (π i)) ∧ ∀ g ∈ Θi (π i), w⁻¹ * g * w ∈ Θi i
  π_trans : ∀ i j : Fin c, ∃ k : ℕ, (π ^ k) i = j
  θ₀_mem : θ₀ ∈ Θ

end CFSG.LocalAnalysis.RankThreeUC
