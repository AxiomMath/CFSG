module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTriv
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem adjCompTrivTwo_of (hA : CFSG.LocalAnalysis.GLTheoremA.T171Sh.ExcAdjCompInnAut) :
    ∀ {τ : Tag}, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
        ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K ^ 2 - 1 → CompTriv p ↥(adjointGroup τ K) := by
  intro τ hτ K _ _ hK p hp hp2 hpq r hrp hr1 w hw hwp J hJ hJp
  have hK2 : ringChar K = 2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.ringChar_eq_two_of_card hK
  haveI : CharP K 2 := ringChar.of_eq hK2
  obtain ⟨hpK, hp5⟩ := not_dvd_card_and_five_le_of_not_dvd_sq_sub_one hK2 hp hp2 hpq
  have hp3 : p ≠ 3 := by omega
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hG2 : τ ≠ .G2 := by rcases hτ with h | h | h <;> rw [h] <;> decide
  obtain ⟨hs, hnc, hchev, -⟩ :=
    adjointGroup_facts_exc hτ' le_rfl (fun h => absurd h hG2) (hK.trans (pow_one 2).symm)
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβ1 : MulAut.conj r ≠ 1 := conj_ne_one_of_center_eq_bot hZ hr1
  have hJcomp : IsComponentOf J (CFSG.LocalAnalysis.GLTheoremA.I142.centFix
      (Subgroup.zpowers (MulAut.conj r))) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.I142C.centFix_zpowers', hfix]
    exact hJ
  have hJchev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremA.I142M.Three.chevCompTypes_holds _ hs hnc hchev p hp hp2
      (MulAut.conj r) hβp hβ1 J hJcomp
  have hβmem : MulAut.conj r ∈ innAutDerived ↥(adjointGroup τ K) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨r, rfl⟩
  have hCN := CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_adjointGroup hτ'
    (fun h => absurd h hG2) hp hp2 hpK (fun _ => hp3) (MulAut.conj r) hβmem hβp hβ1
  have hJfix : IsComponentOf J (fixSubgroup (MulAut.conj r)) := by rw [hfix]; exact hJ
  have hwfix : w ∈ fixSubgroup (MulAut.conj r) := by rw [hfix]; exact hw
  have hwN : w ∈ Subgroup.normalizer (J : Set ↥(adjointGroup τ K)) := hCN J hJfix hwfix
  have hstab := conj_mem_subgroupStabAut_of_mem_normalizer hwN
  have hcomm : r * w = w * r := (Subgroup.mem_centralizer_singleton_iff.1 hw).symm
  have hJA : CFSG.Assembly.IsComponentOf J
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj r)) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hJfix
  exact mem_centralizer_of_isChevSimple_two hJ.2.2 hp hp5 hJchev hJp hwp hstab fun h360 =>
    hA hτ' K p hp hp2 (fun h => absurd h hG2) (fun _ h3 => absurd h3 hp3) r w hr1 hrp hwp hcomm J
      hJA h360 hstab

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
