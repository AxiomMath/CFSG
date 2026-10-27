module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiScalar
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.Sporadic.Bridge.Fi22Surj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Monster.B.Fischer

theorem fi22CoverFive_holds :
    Fi22CoverFive := by
  intro Y _ _ hq hFi hcore
  have hZ := isPGroup_center_of_pPrimeCore_eq_bot Nat.prime_five hcore
  obtain ⟨e₀⟩ := hFi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b
  let θ : (Y ⧸ Subgroup.center Y) ≃* fi22P := (e₀.trans b'.symm).trans fi22PermEquiv
  let f : Y →* fi22P := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hf : Function.Surjective f := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center Y := by
    ext y
    simp only [f, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  obtain ⟨S, hcomm, hexp, g₀, hg₀⟩ := fi22P_sylow_five_scalar
  have hcen : Subgroup.center Y = ⊥ :=
    center_eq_bot_of_sylow_scalar hq.1 hZ f hf hker S hcomm hexp hg₀
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcen.symm)).trans
    e₀⟩

end CFSG.HardMathSupport.Solomon.Coordinator
