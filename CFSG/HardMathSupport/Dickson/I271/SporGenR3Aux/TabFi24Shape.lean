module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Grp

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

theorem shapeRkAt_of_simple_pindex {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    {t : Q} (L : Subgroup Q) (hLC : L ≤ Subgroup.centralizer ({t} : Set Q))
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    {k : ℕ} (hk : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) = Nat.card ↥L * p ^ k)
    (hfac : (p ^ k).factorial < Nat.card ↥(Subgroup.centralizer ({t} : Set Q)))
    (hG : Good ↥L) (hR : Rk ↥L) : ShapeRkAt p Good Rk t := by
  set C : Subgroup Q := Subgroup.centralizer ({t} : Set Q) with hCdef
  let E : Subgroup ↥C := L.subgroupOf C
  have eL : ↥E ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  have hEmap : E.map C.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLC
  have eE : ↥(E.map C.subtype) ≃* ↥L := MulEquiv.subgroupCongr hEmap
  haveI hsE' : IsSimpleGroup ↥E := eL.isSimpleGroup_congr.2 hs
  have hcardE : Nat.card ↥E = Nat.card ↥L := Nat.card_congr eL.toEquiv
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hidx : E.index = p ^ k := by
    have h1 : E.index * Nat.card ↥E = Nat.card ↥C := Subgroup.index_mul_card E
    rw [hcardE, hk] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  haveI hEn : E.Normal := normal_of_isSimple_of_index E hidx (pow_ne_zero k hp.ne_zero) hfac
  have hsE : IsSimpleGroup ↥(E.map C.subtype) := eE.isSimpleGroup_congr.2 hs
  have hnabE : ∃ a b : ↥(E.map C.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eE.symm a, eE.symm b, fun h => hab (by simpa using congrArg eE h)⟩
  have hpE : p ∣ Nat.card ↥(E.map C.subtype) := by
    rw [Nat.card_congr eE.toEquiv]
    exact hpL
  have hq : IsPGroup p (↥C ⧸ E) := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact IsPGroup.of_card (n := k) hidx
  have hZE : Subgroup.center ↥(E.map C.subtype) = ⊥ := by
    haveI := hsE
    exact center_eq_bot_of_simple_nonab hnabE
  have hcoreE : GLAPPrimeCore p ↥(E.map C.subtype) = ⊥ := by
    haveI := hsE
    exact glaPPrimeCore_eq_bot_of_simple hp hpE
  refine shapeRkAt_of_normal_pindex hp E hsE hnabE hpE hq ?_ ?_
  · exact hGood ↥L _ ((pSimpleEquivSelf (E.map C.subtype) hcoreE hZE).trans eE).symm hG
  · exact hRk ↥L _ ((pQuotEquivSelf (E.map C.subtype) hcoreE).trans eE).symm hR

end CFSG.HardMathSupport.Dickson.I271
