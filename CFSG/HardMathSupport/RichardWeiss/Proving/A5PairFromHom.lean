module

public import CFSG.HardMathSupport.RichardWeiss.Proving.PairGenBridge
public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFiveGeneration

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.CGT.PushingUpLit.CGT6

theorem pairGen_eq_range_of_hom {S : Type} [Group S] {Y : Subgroup S} {g h : S}
    (φ : alternatingGroup (Fin 5) →* S)
    (hYa : Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (φ altFiveU))
    (hYb : Y.map (MulAut.conj h).toMonoidHom = Subgroup.zpowers (φ altFiveV)) :
    pairGen Y g h = φ.range := by
  rw [pairGen_eq_closure hYa hYb, MonoidHom.range_eq_map, ← altFive_closure_pair_eq_top,
    MonoidHom.map_closure, Set.image_pair]

theorem exists_pair_A5_of_injective_hom {S : Type} [Group S] {Y : Subgroup S} {g h : S}
    (φ : alternatingGroup (Fin 5) →* S) (hφ : Function.Injective φ)
    (hYa : Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (φ altFiveU))
    (hYb : Y.map (MulAut.conj h).toMonoidHom = Subgroup.zpowers (φ altFiveV)) :
    Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) :=
  ⟨(MulEquiv.subgroupCongr (pairGen_eq_range_of_hom φ hYa hYb)).trans
    (MonoidHom.ofInjective hφ).symm⟩

end CFSG.HardMathSupport.RichardWeiss.Proving

end
