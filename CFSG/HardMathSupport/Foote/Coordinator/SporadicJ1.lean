module

public import CFSG.HardMathSupport.Foote.Coordinator.SporadicBase
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen
public import CFSG.Walter.J1Props.Factor

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.Blueprint

theorem InnerComp5.false_of_abelian_sylow {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    {w : Q} {K : Subgroup Q} (h : InnerComp5 Q w K) (φ : Q →* Q') (hφ : Function.Injective φ)
    (hab : CFSG.Walter.HasAbelianSylowTwo Q') : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := h.sl5
  obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.sl2_exists_quaternion (F := ZMod 5) (by rw [Nat.card_zmod]; decide)
  let ι : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* Q' :=
    φ.comp (K.subtype.comp e.symm.toMonoidHom)
  have hι : Function.Injective ι := hφ.comp (K.subtype_injective.comp e.symm.injective)
  obtain ⟨P, hP⟩ := (hH2.map ι).exists_le_sylow
  have hc := (hab P).is_comm.comm ⟨ι x, hP ⟨x, hx, rfl⟩⟩ ⟨ι y, hP ⟨y, hy, rfl⟩⟩
  apply hxy
  apply hι
  rw [map_mul, map_mul]
  exact congrArg Subtype.val hc

theorem end415K_J1 {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.J1) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  let φ : Q ≃* ↥CFSG.Open.walterJ1 := eQ.trans CFSG.Walter.walterJ1EquivNative.symm
  exact h.false_of_abelian_sylow φ.toMonoidHom φ.injective CFSG.Walter.J1Props.hasAbelianSylowTwo

end CFSG.HardMathSupport.Foote.Coordinator
