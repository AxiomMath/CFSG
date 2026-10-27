module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIMain
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.NineCover
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.Multipliers.U43 CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.RankThree.PartTwo.Sec4.Census

theorem exists_elemAbelian_of_U43 {Q : Type} [Group Q] [Finite Q]
    (e : Q ⧸ Subgroup.center Q ≃* X₀) :
    ∃ E : Subgroup Q, IsElemAbelian 3 E ∧
      3 ^ 4 * Nat.card (E ⊓ Subgroup.center Q : Subgroup Q) ≤ Nat.card E := by
  classical
  let φ : Q →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : φ.ker = Subgroup.center Q := by
    ext q
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : φ.ker ≤ Subgroup.center Q := hkerZ.le
  have hcomm : ∀ x ∈ U43Six.thetaBar.range.comap φ, ∀ y ∈ U43Six.thetaBar.range.comap φ,
      x * y = y * x :=
    fun x hx y hy => U43Six.commute_of_mem_range hφ hker hx hy
  set U := TripleCoverLift.powOneSubgroup φ U43Six.thetaBar.range 3 hcomm with hUdef
  have hUab : IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  refine ⟨U, hUab, ?_⟩
  set ψ : ↥U →* X₀ := φ.comp U.subtype with hψ
  have hψr : ψ.range = U43Six.thetaBar.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp y.2).1
    · intro hx
      obtain ⟨y, hy, hyp⟩ := U43Six.exists_lift_of_mem_range hφ hker hx
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ hx, hyp⟩⟩, hy⟩
  have hkerψ : Nat.card ψ.ker = Nat.card ↥(U ⊓ φ.ker) := by
    rw [hψ, ← MonoidHom.comap_ker, ← Subgroup.card_map_of_injective U.subtype_injective]
    change Nat.card ((φ.ker.subgroupOf U).map U.subtype) = _
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hkerψ, hψr, U43Six.card_range_thetaBar, hkerZ] at hmul
  rw [← hmul, mul_comm]

theorem cfgIRank_U43_three {row : S8.Row} (hIq : row.Iq = S8.isU4of 3) (hrank : row.rank = 4) :
    CfgIRankRow 3 row := by
  intro Q _ _ hcat _
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [hIq] at hi
  rw [hrank]
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA n q =>
      by_cases hn : n = 3
      · subst hn
        have hq : q.card = 3 := hi
        obtain ⟨b⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.u43_group_equiv hv hq
        obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_of_U43 (e.trans b)
        refine ⟨E, hE, le_trans ?_ hEc⟩
        exact Nat.mul_le_mul_right _ (by norm_num)
      · exfalso
        revert hi
        rcases n with _ | _ | _ | _ | n <;> simp_all [S8.isU4of, onLie]
    | _ => exact False.elim hi

theorem cfgIRank_suz_three : CfgIRankRow 3 S8.Row.suz :=
  cfgIRank_U43_three rfl rfl

theorem cfgIRank_suzh_three : CfgIRankRow 3 S8.Row.suzh :=
  cfgIRank_U43_three rfl rfl

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
