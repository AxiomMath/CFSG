module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIMain
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Local

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA

theorem cfgIRank_ly_three :
    CfgIRankRow 3 S8.Row.ly := by
  intro Q _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hi' : i = TauCeti.CFSGIndex.sporadic .McL := hi
  subst hi'
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let φ : (TauCeti.CFSGIndex.sporadic .McL).Group ≃* CFSG.Sporadic.Schreier.mclP :=
    b.symm.trans CFSG.Sporadic.Schreier.mclPermEquiv
  let ρ : Q →* CFSG.Sporadic.Schreier.mclP :=
    (e.trans φ).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hρ : Function.Surjective ρ := (e.trans φ).surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : ρ.ker = Subgroup.center Q := by
    ext q
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1 := by
    intro z hz
    rw [hkerZ] at hz
    have hd := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center Q))
    have hZ' : Nat.card ↥(Subgroup.center Q) = 3 := hZ
    rw [hZ'] at hd
    simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 hd)
  obtain ⟨E, hE, h81, -⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9.exists_lift_e81 ρ hρ
    hkerZ.le hZ3 (u := 1) (one_pow 3)
  refine ⟨E, hE, ?_⟩
  have hle : Nat.card ↥(E ⊓ Subgroup.center Q) ≤ 3 := by
    rw [← (show Nat.card ↥(Subgroup.center Q) = 3 from hZ)]
    exact Subgroup.card_le_of_le inf_le_right
  show 3 ^ (4 - 1) * Nat.card ↥(E ⊓ Subgroup.center Q) ≤ Nat.card E
  omega

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
