module

public import CFSG.Assembly.E6FourCentReduce
public import CFSG.Assembly.E6FourCentSpec
public import CFSG.Assembly.E6FourCentFineA
public import CFSG.Assembly.E6FourCentFineD
public import CFSG.Assembly.E6FourCentMark

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Subgroup


theorem e6FourCentFive_holds : E6FourCentFive := by
  classical
  intro J _ _ hJ hZ A hA s hsA hs1 X hX hAX hC
  obtain ⟨L, _, _, S, ζ, v, i, hq, hρ, hΦ, hζ, hv, hv0, hT, ⟨e⟩, hle⟩ :=
    e6FourCent_reduce hJ hZ hA hsA hs1 hX hAX hC
  have hperf : commutator ↥X = ⊤ := hX.2.2.1
  have hζ5 : ζ ^ 5 = 1 := Units.ext (by simpa using hζ.pow_eq_one)
  have hap : ∀ j, (ζ ^ (v j).val) ^ 5 = 1 := fun j => by
    rw [← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  have h1 : rootDiagUnit Tag.E6 (fun j => ζ ^ (v j).val) ≠ 1 := by
    intro h
    apply hv0
    funext j
    have hj : ζ ^ (v j).val = 1 :=
      congrFun (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)) j
    have hj' : (ζ : L) ^ (v j).val = 1 := by simpa using congrArg Units.val hj
    have hd : 5 ∣ (v j).val := (hζ.pow_eq_one_iff_dvd _).1 hj'
    have h0 : (v j).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt (v j))
    exact (ZMod.val_eq_zero (v j)).1 h0
  have hker : e.toMonoidHom.ker ≤ Subgroup.center ↥X := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  obtain ⟨e2⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hperf e.toMonoidHom e.surjective hker
  rcases e6Four_table_spec S.ρ hρ ζ hζ hv hv0 i hle with ⟨hr, hn, hs, hin⟩ | ⟨hr, hn, hs, hout⟩
  · exact e6FourSubcompMark_of_psl6 hperf
      (LieModel.of_mulEquiv e2.symm (e6Four_A5_fine S hq hT hap h1 i hr hn hs hin))
  · exact e6FourSubcompMark_of_pomegaMinus4 hperf
      (LieModel.of_mulEquiv e2.symm (e6Four_D4_fine S hq (e6Four_rho_sq_of_table S hρ) hΦ hT
        hap h1 i hr hn hs hout))

end CFSG.Assembly

end
