module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open CFSG.Open

noncomputable abbrev commGroupOfIsElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : CommGroup E :=
  { (inferInstance : Group E) with
    mul_comm := fun a b => hE.1.is_comm.comm a b }

theorem mulAut_injective_toGL {V : Type*} [CommGroup V] [Module (ZMod 3) (Additive V)]
    [Module.Finite (ZMod 3) (Additive V)] :
    ∃ φ : MulAut V →* Matrix.GeneralLinearGroup
        (Fin (Module.finrank (ZMod 3) (Additive V))) (ZMod 3),
      Function.Injective φ := by
  let b := Module.finBasis (ZMod 3) (Additive V)
  let lin : MulAut V →* (Additive V →ₗ[ZMod 3] Additive V) :=
    { toFun := fun f => (MulEquiv.toAdditive f).toAddMonoidHom.toZModLinearMap 3
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hlin : Function.Injective lin := by
    intro f g h
    have h1 : (MulEquiv.toAdditive f).toAddMonoidHom = (MulEquiv.toAdditive g).toAddMonoidHom :=
      AddMonoidHom.toZModLinearMap_injective 3 h
    exact MulEquiv.toAdditive.injective (AddEquiv.toAddMonoidHom_injective h1)
  let ψ : MulAut V →* Matrix (Fin (Module.finrank (ZMod 3) (Additive V)))
      (Fin (Module.finrank (ZMod 3) (Additive V))) (ZMod 3) :=
    (((LinearMap.toMatrixAlgEquiv b).toRingEquiv).toMonoidHom).comp lin
  have hψ : Function.Injective ψ :=
    (LinearMap.toMatrixAlgEquiv b).injective.comp hlin
  have hψ' : Function.Injective ψ.toHomUnits := by
    intro f g h
    apply hψ
    have := congrArg Units.val h
    simpa using this
  exact ⟨ψ.toHomUnits, hψ'⟩

theorem mulAut_solvable_of_exp_three {V : Type*} [CommGroup V] [Finite V]
    (hexp : ∀ x : V, x ^ 3 = 1) (hcard : Nat.card V ≤ 9) :
    Group.IsSolvable (MulAut V) := by
  let : Module (ZMod 3) (Additive V) := AddCommGroup.zmodModule (fun x => by
    show Additive.ofMul (x.toMul ^ 3) = Additive.ofMul 1
    rw [hexp])
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 3) (Additive V) := inferInstance
  have hfr : Module.finrank (ZMod 3) (Additive V) ≤ 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive V)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive V) ≤ 9 := hcard
    by_contra hlt
    have h3 : 3 ^ 3 ≤ 3 ^ Module.finrank (ZMod 3) (Additive V) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← h1] at h3
    norm_num at h3
    omega
  have := CFSG.RankThree.PartTwo.Sec4.Census.isSolvable_GL_zmod_three hfr
  obtain ⟨φ, hφ⟩ := mulAut_injective_toGL (V := V)
  exact Group.isSolvable_of_isSolvable_injective (f := φ) hφ

theorem mulAut_elemAbelian_three_solvable {G : Type*} [Group G] {E : Subgroup G}
    [Finite E] (hE : IsElemAbelian 3 E) (hcard : Nat.card E ≤ 9) :
    Group.IsSolvable (MulAut E) := by
  have hexp : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x.1 x.2)
  let : CommGroup E := commGroupOfIsElemAbelian hE
  exact mulAut_solvable_of_exp_three hexp hcard

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
