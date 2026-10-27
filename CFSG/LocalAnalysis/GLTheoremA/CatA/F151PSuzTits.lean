module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcSmall
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.I171
open CFSG.LocalAnalysis.GLTheoremA.K155X
  (l154ExcSuz l154_suzukiModel_of_catalogIs l154_false_of_suzuki_centralizer)
open CFSG.RankThree.PartOne.CTP (reeTitsModel_tits)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Sporadic.Schreier.Tits (titsD titsModelEquiv)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (isSolvable_centralizer_titsD)

private theorem false_of_glaPComponent_of_isSolvable {G : Type} [Group G] [Finite G] {p : ℕ}
    {X J : Subgroup G} (hX : Group.IsSolvable ↥X) (hJ : GLAPComponent p X J) : False := by
  haveI : Group.IsSolvable ↥X := hX
  have hJX : J ≤ X := hJ.1
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  haveI : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJX)
      (Subgroup.inclusion_injective hJX)
  haveI : Nontrivial ↥J :=
    (Subgroup.nontrivial_iff_ne_bot J).2
      (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ)
  exact Group.IsPerfect.not_isSolvable (G := ↥J) inferInstance

private theorem shapeModel_suzuki {S : Type} [Group S] [Finite S] (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hSz : ∃ f : ℕ, CFSG.Blueprint.SuzukiModel S 2 f)
    (x : S) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (J : Subgroup S) (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set S)) J) : False := by
  obtain ⟨f, hSzf⟩ := hSz
  have hperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hne : J ≠ ⊥ := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ
  have hcent : ∀ t ∈ J, t * x = x * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 ht)
  exact l154_false_of_suzuki_centralizer hSzf hp hp2 hxp hx1 hperf hne hcent

private theorem shapeModel_tits {S : Type} [Group S] [Finite S]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {hv : TauCeti.LieTypeIndex.tits.Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)
    (x : S) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (J : Subgroup S) (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set S)) J) : False := by
  have hiso : IsoLie S .tits := ⟨hv, ⟨e⟩⟩
  have hmodel := reeTitsModel_tits hiso
  obtain ⟨eTD⟩ := titsModelEquiv S 2 1 hmodel
  have hx'p : eTD x ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hx'1 : eTD x ≠ 1 := fun h => hx1 (eTD.injective (by rw [h, map_one]))
  have hsolv' : Group.IsSolvable ↥(Subgroup.centralizer ({eTD x} : Set titsD)) :=
    isSolvable_centralizer_titsD hp hp2 hx'p hx'1
  let f : ↥(Subgroup.centralizer ({x} : Set S)) →*
      ↥(Subgroup.centralizer ({eTD x} : Set titsD)) :=
  { toFun := fun y =>
      ⟨eTD y, by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        have hxy : x * y = y * x :=
          (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
        rw [hh, ← map_mul, ← map_mul, hxy]⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intro a b; apply Subtype.ext; simp }
  have hfinj : Function.Injective f := fun a b hab =>
    Subtype.ext (eTD.injective (Subtype.ext_iff.mp hab))
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set S)) := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({eTD x} : Set titsD)) := hsolv'
    exact Group.isSolvable_of_isSolvable_injective (f := f) hfinj
  exact false_of_glaPComponent_of_isSolvable hsolv hJ

theorem simpleModel_suzTits_holds :
    SimpleModel (CharTwoOf isSuzTitsIdx) :=
  fun S _ _ p hp hp2 hcat _hshape =>
    fun x y hx1 hxp _hyp _hcomm J hJ => by
      exfalso
      obtain ⟨i, hi, ⟨e⟩⟩ := hcat
      cases i with
      | cyclic n hn => exact hi.elim
      | alternating n hn => exact hi.elim
      | sporadic sp => exact hi.elim
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        simp only [onLie, CharTwoOf] at hi
        obtain ⟨hiSuz, -⟩ := hi
        cases d1 with
        | suzuki k =>
          have hcatSuz : catalogIs S l154ExcSuz := ⟨.lie ⟨.suzuki k, hv⟩, trivial, ⟨e⟩⟩
          obtain ⟨f, hSzf⟩ := l154_suzukiModel_of_catalogIs hcatSuz
          exact shapeModel_suzuki p hp hp2 ⟨f, hSzf⟩ x hx1 hxp J hJ
        | tits =>
          exact shapeModel_tits p hp hp2 e x hx1 hxp J hJ
        | _ => exact hiSuz.elim

end CFSG.LocalAnalysis.GLTheoremA.F151

end
