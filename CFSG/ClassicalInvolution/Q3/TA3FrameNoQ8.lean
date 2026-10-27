module

public import CFSG.ClassicalInvolution.Q3.TA3FrameBase
public import CFSG.ClassicalInvolution.Q3.Q3SEven
public import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2
public import CFSG.GH74.Generic.S1.Exo.Q3SingleSz8
public import CFSG.GH74.Generic.BProg.B2.PumpupTableRee

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS
open scoped MatrixGroups

section Member

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem false_of_noQ8 [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) (hT : ∀ ψ : QuaternionGroup 2 →* T, ¬ Function.Injective ψ) :
    False := by
  obtain ⟨φ, hφ, hφLT⟩ := exists_q8 hL hTL h3
  exact hT (φ.codRestrict T fun x => (hφLT x).2) fun x y hxy => hφ (congrArg Subtype.val hxy)

end Member

variable {X : Type} [Group X]

theorem noQ8_psl2_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p f) :
    ∀ ψ : QuaternionGroup 2 →* X, ¬ Function.Injective ψ :=
  fun ψ hψ => GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2 h ψ hψ

theorem noQ8_psl2_even {f : ℕ} (hf : 2 ≤ f) (h : LieModel X .PSL 2 2 f) :
    ∀ ψ : QuaternionGroup 2 →* X, ¬ Function.Injective ψ := by
  intro ψ hψ
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q3.statedClassicalModel_of_lieModel_psl h (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e' := e.trans (ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK)
  refine Q3.orderOf_ne_four_psl_two hf (e' (ψ (QuaternionGroup.a 1))) ?_
  rw [MulEquiv.orderOf_eq, orderOf_injective ψ hψ, QuaternionGroup.orderOf_a_one]

theorem noQ8_sz8 (h : LieModel X .twistedB2 0 2 3) :
    ∀ ψ : QuaternionGroup 2 →* X, ¬ Function.Injective ψ :=
  fun ψ hψ => GH74.Generic.S1.Exo.no_q8_of_twistedB2 h ⟨ψ, hψ⟩

theorem noQ8_ree [Finite X] {f : ℕ} (h : LieModel X .twistedG2 0 3 f) :
    ∀ ψ : QuaternionGroup 2 →* X, ¬ Function.Injective ψ :=
  fun ψ hψ => GH74.Generic.BProg.B2.PumpupTableRee.ree_no_q8
    (GH74.Generic.BProg.B1.reeTitsModel_of_lieModel_twistedG2 h) ψ hψ

end CFSG.ClassicalInvolution.Q3.TA3.Frame
