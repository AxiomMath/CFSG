module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzDefs

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

section Quasi

variable {Q : Type} [Group Q] [Finite Q]

theorem isPGroup_inf_centralizer_self {p : ℕ} (C : Subgroup Q)
    (h : IsPGroup p ↥(Subgroup.center ↥C)) :
    IsPGroup p ↥(C ⊓ Subgroup.centralizer (C : Set Q)) := by
  let f : ↥(C ⊓ Subgroup.centralizer (C : Set Q)) →* ↥(Subgroup.center ↥C) :=
    { toFun := fun z => ⟨⟨z, z.2.1⟩, by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 z.2.2 g g.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun z w hzw => by
    have := congrArg (fun y : ↥(Subgroup.center ↥C) => ((y : ↥C) : Q)) hzw
    exact Subtype.ext this
  exact h.of_injective f hf

theorem splitShapeAt_of_centralizer_equiv {k : Q} {T : Type} [Group T]
    (e : ↥(Subgroup.centralizer ({k} : Set Q)) ≃* T) (hq : CFSG.Open.IsQuasisimple T)
    (hZ : IsPGroup 3 ↥(Subgroup.center T)) (hp : 3 ∣ Nat.card T)
    (hleaf : LeafType 3 (T ⧸ Subgroup.center T)) : SplitShapeAt 3 k := by
  set C := Subgroup.centralizer ({k} : Set Q) with hC
  have hq' : CFSG.Open.IsQuasisimple ↥C := isQuasisimple_of_mulEquiv' e.symm hq
  have ec : ↥(Subgroup.center ↥C) ≃* ↥(Subgroup.center T) :=
    ((Subgroup.center ↥C).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_center_eq e))
  have hZ' : IsPGroup 3 ↥(Subgroup.center ↥C) := hZ.of_equiv ec.symm
  have hp' : 3 ∣ Nat.card ↥C := by
    rw [Nat.card_congr e.toEquiv]
    exact hp
  have eq : (↥C ⧸ Subgroup.center ↥C) ≃* (T ⧸ Subgroup.center T) :=
    QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center T) e (Subgroup.map_center_eq e)
  have hleaf' : LeafType 3 (↥C ⧸ Subgroup.center ↥C) := LeafType.of_equiv eq.symm hleaf
  right
  have hLn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (C : Set Q)) :=
    isPGroup_inf_centralizer_self C hZ'
  have hcore : GLAPPrimeCore 3 ↥C = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three le_rfl hLn hq' hp' hcent
  refine ⟨C, glaPComponent_of_normal_quasisimple le_rfl hLn hq' hcore,
    fun I hI => eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three le_rfl hLn hq' hcore
      hcent hI, Or.inl ?_⟩
  exact LeafType.of_equiv (pSimpleEquivCenterQuot C hcore).symm hleaf'

end Quasi

end CFSG.HardMathSupport.Dickson.I271
