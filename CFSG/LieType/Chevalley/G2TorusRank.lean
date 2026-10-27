module

public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

noncomputable def TorusG2 (F : Type) [Field F] :
    Subgroup (adjointGroup .G2 F) :=
  (torusGroup .G2 F).subgroupOf (adjointGroup .G2 F)

instance finite_adjointGroup_G2 (F : Type) [Field F] [Finite F] :
    Finite (adjointGroup .G2 F) := by
  have : Finite (Module.End F (RootModule .G2 F)) := Module.finite_of_finite F
  haveI : Finite (ModGL .G2 F) := inferInstance
  exact Subtype.finite

theorem two_le_pRank_torus_G2
    {F : Type} [Field F] [Finite F] {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank q (TorusG2 F) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd' : q ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hdvd'
  have hTle : torusGroup .G2 F ≤ adjointGroup .G2 F :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨⟨i, t⟩, rfl⟩
      exact torusElt_mem_adjointGroup i t)
  obtain ⟨eT, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) F
  let ι : (Fin Tag.G2.rank → Fˣ) →* TorusG2 F :=
    (Subgroup.subgroupOfEquivOfLe hTle).symm.toMonoidHom.comp eT.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.subgroupOfEquivOfLe hTle).symm.injective.comp eT.injective
  let i : Fin Tag.G2.rank := ⟨0, by decide⟩
  let j : Fin Tag.G2.rank := ⟨1, by decide⟩
  have hij : i ≠ j := by decide
  let x : TorusG2 F := ι (Pi.mulSingle i u)
  let y : TorusG2 F := ι (Pi.mulSingle j u)
  have hpi_i : orderOf (Pi.mulSingle (M := fun _ : Fin Tag.G2.rank => Fˣ) i u) = orderOf u :=
    orderOf_piMulSingle (M := fun _ : Fin Tag.G2.rank => Fˣ) i u
  have hpi_j : orderOf (Pi.mulSingle (M := fun _ : Fin Tag.G2.rank => Fˣ) j u) = orderOf u :=
    orderOf_piMulSingle (M := fun _ : Fin Tag.G2.rank => Fˣ) j u
  have hxp : orderOf x = q := by
    show orderOf (ι (Pi.mulSingle i u)) = q
    exact (orderOf_injective ι hι _).trans (hpi_i.trans hu)
  have hyp : orderOf y = q := by
    show orderOf (ι (Pi.mulSingle j u)) = q
    exact (orderOf_injective ι hι _).trans (hpi_j.trans hu)
  have hcomm : Commute x y := (Commute.all _ _).map ι
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : (Pi.mulSingle (M := fun _ : Fin Tag.G2.rank => Fˣ) i u) ^ n =
        Pi.mulSingle (M := fun _ : Fin Tag.G2.rank => Fˣ) j u := by
      apply hι
      rw [map_zpow]
      simpa [x, y] using hn
    have h1u : u = 1 := by
      have hval := congrFun h1 j
      rw [← Pi.mulSingle_zpow, Pi.mulSingle_eq_of_ne hij.symm,
        Pi.mulSingle_eq_same] at hval
      exact hval.symm
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hu
      exact hq.ne_one hu.symm
    exact hu1 h1u
  haveI : Finite (TorusG2 F) := Subtype.finite
  have h := CFSG.GroupTheory.two_le_pRank_of_commute (G := TorusG2 F) (H := ⊤)
    (x := x) (y := y) (Subgroup.mem_top x) (Subgroup.mem_top y) hxp hyp hcomm hyx
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) (TorusG2 F)] at h

theorem two_le_pRank_G2_of_dvd
    {F : Type} [Field F] [Finite F] {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (adjointGroup .G2 F)) :=
  (two_le_pRank_torus_G2 hq hdvd).trans
    (CFSG.SectionRank.pRank_mono hq.one_lt (le_top : TorusG2 F ≤ ⊤))

end CFSG.LieType.Chevalley
