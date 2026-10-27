module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Red
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.PartI.U42

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem E9Solv_u42 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    E9Solv (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
  intro E hE hcard
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨α, hα1⟩ := exists_ne (1 : E)
  have hα3 : (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) ^ 3 = 1 :=
    hE.2 α.1 α.2
  have hsub : i269Fix E ≤ fixSubgroup (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) := by
    intro x hx
    exact (mem_i269Fix.1 hx) α.1 α.2
  have hfix : Group.IsSolvable ↥(fixSubgroup (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)) :=
    u42_fixSubgroup_solvable q hv hq (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
      hα3 (fun h => hα1 (Subtype.ext h))
  haveI := hfix
  exact isSolvable_of_le_isSolvable hsub

theorem layer_eq_bot_of_u42 {G : Type} [Group G] [Finite G]
    {X L D : Subgroup G} (hL : GLAPComponent 3 X L)
    (hcat : catalogIs (PSimple 3 L) S9.isU4two)
    (hDN : D ≤ Subgroup.normalizer (L : Set G)) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L)) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥ := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two hcat
  exact layer_eq_bot_of_E9 hL ((E9Solv_u42 q hv hq).of_mulEquiv e) hDN hD hcard

end CFSG.LocalAnalysis.GLTheoremA

end
