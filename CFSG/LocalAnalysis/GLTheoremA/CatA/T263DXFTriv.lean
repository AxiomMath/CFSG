module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTriv
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem twE6CompTriv_holds :
    TwE6CompTriv := by
  intro f hf4 K _ _ hK σ hσ p hp hp2 hpq r hrp hr1 w hw hwp J hJ hJp
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · norm_num at hf4
    · exact h
  have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have h4 : ((2 : ℕ) ^ f) ^ 2 = 4 ^ f := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4]
    exact Nat.sub_one_dvd_pow_sub_one 4 f
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hpq h3
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have : p = 4 := by omega
    subst this
    exact absurd hp (by decide)
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hM : ChevalleyExceptionalModel ↥(twistedE6RootGroup K σ) .twistedE6 2 f :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.chevalleyExceptionalModel_twistedE6_of_equiv
      Nat.prime_two hf hK σ hσ (MulEquiv.refl _)
  obtain ⟨-, hs⟩ := CFSG.LieType.Simplicity.fam_2e6_simplicity _ 2 f hM
  have hnc : ∃ a b : ↥(twistedE6RootGroup K σ), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊤ :=
      (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => hcon b a
    rw [hZ] at hc
    obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(twistedE6RootGroup K σ)
    have hx : x ∈ (⊥ : Subgroup ↥(twistedE6RootGroup K σ)) := hc ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup ↥(twistedE6RootGroup K σ)) := hc ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)
  have hchev : IsChevSimple 2 ↥(twistedE6RootGroup K σ) := by
    obtain ⟨d, hd, e⟩ := CFSG.LocalAnalysis.GLTheoremA.index_of_chevalleyExceptional
      (by simp [chevalleyExceptionalTags]) hM
    exact Or.inl ⟨TauCeti.CFSGIndex.lie d, hd, e⟩
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβ1 : MulAut.conj r ≠ 1 := conj_ne_one_of_center_eq_bot hZ hr1
  have hβmem : MulAut.conj r ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨r, rfl⟩
  have hCN := CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_twistedE6 Nat.prime_two hf hK σ hσ
    hp hp2 hp3 hp2 (MulAut.conj r) hβmem hβp hβ1
  have hJfix : IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj r)) := by
    rw [hfix]
    exact hJ
  have hwfix : w ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj r) := by
    rw [hfix]
    exact hw
  have hstab := conj_mem_subgroupStabAut_of_mem_normalizer (hCN J hJfix hwfix)
  have hJcomp : IsComponentOf J (CFSG.LocalAnalysis.GLTheoremA.I142.centFix
      (Subgroup.zpowers (MulAut.conj r))) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.I142C.centFix_zpowers', hfix]
    exact hJ
  have hJchev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremA.I142M.Three.chevCompTypes_holds _ hs hnc hchev p hp hp2
      (MulAut.conj r) hβp hβ1 J hJcomp
  refine mem_centralizer_of_isChevSimple_two hJ.2.2 hp hp5 hJchev hJp hwp hstab ?_
  intro h360
  have hcomm : r * w = w * r := (Subgroup.mem_centralizer_singleton_iff.1 hw).symm
  have hJA : CFSG.Assembly.IsComponentOf J
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj r)) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hJfix
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6ComponentAction_holds
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.excKernelCompAction_holds
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6CentralizerConnOdd_holds hp hp2
    (q := ⟨2, f, Nat.prime_two, hf⟩) rfl σ hK hσ (fun h => absurd h hp3) r w hr1 hrp hcomm J hJA
    hstab h360

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
