module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameCone
public import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameFlag
public import CFSG.LieType.CurtisTits.TitsGeometryRetained

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open _root_.QuadraticMap
open CFSG.QuadraticMap
open CFSG.LieType.CurtisTits

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev genChamber (j : Fin 5) : FrameVert := stdVert j (![0, 1, 2, 3, 5] j)

private theorem genChamber_four : genChamber 4 = stdVert 4 5 := rfl

private theorem genChamber_of_ne_four {i : Fin 5} (hi : i ≠ 4) :
    genChamber i = stdVert i (Fin.castSucc i) := by
  have h : ![0, 1, 2, 3, 5] i = Fin.castSucc i := by
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd rfl hi
  change stdVert i (![0, 1, 2, 3, 5] i) = stdVert i (Fin.castSucc i)
  rw [h]

private theorem frameGraph_adj_genChamber {i j : Fin 5} (hij : i ≠ j) :
    frameGraph.Adj (genChamber i) (genChamber j) := by
  have hinj : Function.Injective (![0, 1, 2, 3, 5] : Fin 5 → Fin 6) := by decide
  exact frameGraph_adj_stdVert hij fun h => hij (hinj h)

private theorem parabolic_genChamber_four :
    parabolic ↥(Om 6) genChamber ({4} : Set (Fin 5)) =
      (supp 6 {5}ᶜ).subgroupOf (Om 6) := by
  rw [parabolic_singleton, genChamber_four]
  ext g
  simp only [Subgroup.mem_subgroupOf, mem_stabilizer_stdVert_iff]

private theorem parabolic_genChamber_single {i : Fin 5} (hi : i ≠ 4) :
    parabolic ↥(Om 6) genChamber ({i} : Set (Fin 5)) =
      (supp 6 {Fin.castSucc i}ᶜ).subgroupOf (Om 6) := by
  rw [parabolic_singleton, genChamber_of_ne_four hi]
  ext g
  simp only [Subgroup.mem_subgroupOf, mem_stabilizer_stdVert_iff]

private theorem parabolic_genChamber_pair {i : Fin 5} (hi : i ≠ 4) :
    parabolic ↥(Om 6) genChamber ({4, i} : Set (Fin 5)) =
      (supp 6 {5}ᶜ ⊓ supp 6 {Fin.castSucc i}ᶜ).subgroupOf (Om 6) := by
  have hpar : parabolic ↥(Om 6) genChamber ({4, i} : Set (Fin 5)) =
      parabolic ↥(Om 6) genChamber ({4} : Set (Fin 5)) ⊓
        parabolic ↥(Om 6) genChamber ({i} : Set (Fin 5)) := by
    refine le_antisymm
      (le_inf (parabolic_antitone (by simp)) (parabolic_antitone (by simp))) ?_
    intro g hg
    rw [Subgroup.mem_inf, mem_parabolic_iff, mem_parabolic_iff] at hg
    rw [mem_parabolic_iff]
    intro j hj
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    rcases hj with hj | hj
    · subst j
      exact hg.1 4 (by simp)
    · subst j
      exact hg.2 i (by simp)
  rw [hpar, parabolic_genChamber_four, parabolic_genChamber_single hi]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]

private theorem card_three_le_four (a b c : Fin 5) :
    ({a, b, c} : Finset (Fin 5)).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c} : Finset (Fin 5))
  have h2 := Finset.card_insert_le b ({c} : Finset (Fin 5))
  have h3 : ({c} : Finset (Fin 5)).card = 1 := Finset.card_singleton c
  omega

theorem preconnected_residueGraph_genChamber :
    (CFSG.LieType.CurtisTits.residueGraph frameGraph FrameVert.typ genChamber
      {4}).Preconnected := by
  intro u v
  let x := u.1
  let y := v.1
  have hxP : frameGraph.Adj x (genChamber 4) := u.2.2 4 (by simp)
  have hyP : frameGraph.Adj y (genChamber 4) := v.2.2 4 (by simp)
  have hxorth : (genChamber 4).plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane :=
    (FrameVert.orth_iff_plane_le_orthogonal (x := x) (y := genChamber 4)).1
      (frameGraph_adj_iff.1 hxP).2
  have hyorth : (genChamber 4).plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) y.plane :=
    (FrameVert.orth_iff_plane_le_orthogonal (x := y) (y := genChamber 4)).1
      (frameGraph_adj_iff.1 hyP).2
  have hPorth : (genChamber 4).plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (x.plane ⊔ y.plane) := by
    rw [orthogonal_sup (Q 6) x.plane y.plane]
    exact le_inf hxorth hyorth
  have hxyh : hullDim (Q 6) (x.plane ⊔ y.plane) ≤ 6 := by
    have h1 := hullDim_sup_plane_le x.plane y
    have h2 := hullDim_plane x
    omega
  have hUh : hullDim (Q 6) ((x.plane ⊔ y.plane) ⊔ (genChamber 4).plane) ≤ 9 := by
    have h := hullDim_sup_plane_le_of_le_orthogonal (x := genChamber 4) hPorth
    omega
  obtain ⟨z, hzT, hzorth⟩ :=
    exists_typ_not_mem_plane_le_orthogonal
      (U := (x.plane ⊔ y.plane) ⊔ (genChamber 4).plane) hUh
      (T := {4, x.typ, y.typ}) (card_three_le_four 4 x.typ y.typ)
  have hz4 : z.typ ≠ 4 := by
    intro h
    exact hzT (by simp [h])
  have hzx : z.typ ≠ x.typ := by
    intro h
    exact hzT (by simp [h])
  have hzy : z.typ ≠ y.typ := by
    intro h
    exact hzT (by simp [h])
  have hxz : frameGraph.Adj x z :=
    frameGraph_adj_of_le_orthogonal
      (U := (x.plane ⊔ y.plane) ⊔ (genChamber 4).plane)
      (le_trans le_sup_left le_sup_left) hzorth (Ne.symm hzx)
  have hyz : frameGraph.Adj y z :=
    frameGraph_adj_of_le_orthogonal
      (U := (x.plane ⊔ y.plane) ⊔ (genChamber 4).plane)
      (le_trans le_sup_right le_sup_left) hzorth (Ne.symm hzy)
  have hPz : frameGraph.Adj (genChamber 4) z :=
    frameGraph_adj_of_le_orthogonal
      (U := (x.plane ⊔ y.plane) ⊔ (genChamber 4).plane)
      le_sup_right hzorth (by simpa [genChamber] using (Ne.symm hz4))
  let z' : CFSG.LieType.CurtisTits.residueVertex frameGraph FrameVert.typ genChamber {4} :=
    ⟨z, by simpa using hz4, by
      intro j hj
      rw [Set.mem_singleton_iff] at hj
      subst j
      exact hPz.symm⟩
  have huz' : (CFSG.LieType.CurtisTits.residueGraph frameGraph FrameVert.typ genChamber
      {4}).Adj u z' := by
    change frameGraph.Adj x z
    exact hxz
  have hvz' : (CFSG.LieType.CurtisTits.residueGraph frameGraph FrameVert.typ genChamber
      {4}).Adj v z' := by
    change frameGraph.Adj y z
    exact hyz
  exact huz'.reachable.trans hvz'.symm.reachable

theorem iSup_supp_compl_five_inf_eq :
    (⨆ j : Fin 5, supp 6 {5}ᶜ ⊓ supp 6 {Fin.castSucc j}ᶜ) = supp 6 {5}ᶜ := by
  refine le_antisymm (iSup_le fun j => inf_le_left) ?_
  let J : Set (Fin 5) := {4}
  let G4 : Subgroup (V 6 ≃ₗ[ZMod 2] V 6) := supp 6 {5}ᶜ
  let P4 : Subgroup ↥(Om 6) := parabolic ↥(Om 6) genChamber J
  have hP4 : P4 = G4.subgroupOf (Om 6) := by
    simpa only [P4, J, G4] using parabolic_genChamber_four
  have hFtyp : ∀ i : Fin 5, FrameVert.typ (genChamber i) = i := fun i => typ_stdVert i _
  have hFadj : ∀ i j : Fin 5, i ≠ j → frameGraph.Adj (genChamber i) (genChamber j) :=
    fun _ _ hij => frameGraph_adj_genChamber hij
  have hflag : CFSG.LieType.CurtisTits.FlagTransitive ↥(Om 6) frameGraph genChamber :=
    flagTransitive_frameGraph (ι := ![0, 1, 2, 3, 5]) (by decide)
  let : MulAction P4 (CFSG.LieType.CurtisTits.residueVertex frameGraph FrameVert.typ
      genChamber J) :=
    CFSG.LieType.CurtisTits.residueMulAction typ_smul frameGraph_adj_smul J
  have : Nonempty {i : Fin 5 // i ∉ J} := ⟨⟨0, by simp [J]⟩⟩
  have hgen : (⨆ i : {i : Fin 5 // i ∉ J},
      MulAction.stabilizer P4
        (CFSG.LieType.CurtisTits.residueChamber hFtyp hFadj J i)) = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_stabilizer_eq_top_of_connected
      (CFSG.LieType.CurtisTits.residueTyp_residueChamber hFtyp hFadj J)
      (fun g x => CFSG.LieType.CurtisTits.residueTyp_smul typ_smul frameGraph_adj_smul J g x)
      (CFSG.LieType.CurtisTits.residue_flagTransitive typ_smul frameGraph_adj_smul hFtyp hFadj
        hflag J (by simp [J]))
      preconnected_residueGraph_genChamber
  have hstab (i : {i : Fin 5 // i ∉ J}) :
      MulAction.stabilizer P4 (CFSG.LieType.CurtisTits.residueChamber hFtyp hFadj J i) =
        (parabolic ↥(Om 6) genChamber ({4, i.1} : Set (Fin 5))).subgroupOf P4 := by
    have hset : J ∪ (fun k : {k : Fin 5 // k ∉ J} => k.1) '' ({i} : Set {k // k ∉ J}) =
        ({4, i.1} : Set (Fin 5)) := by
      ext k
      simp [J, Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
    rw [← parabolic_singleton (F := CFSG.LieType.CurtisTits.residueChamber hFtyp hFadj J)]
    rw [CFSG.LieType.CurtisTits.residueParabolic_eq typ_smul frameGraph_adj_smul hFtyp hFadj J {i}]
    rw [hset]
  have hmem (x : P4) :
      (((x : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6) ∈
        ⨆ j : Fin 5, G4 ⊓ supp 6 {Fin.castSucc j}ᶜ) := by
    have hx : x ∈ (⨆ i : {i : Fin 5 // i ∉ J},
        MulAction.stabilizer P4
          (CFSG.LieType.CurtisTits.residueChamber hFtyp hFadj J i)) := by
      rw [hgen]
      exact Subgroup.mem_top x
    refine Subgroup.iSup_induction
      (S := fun i : {i : Fin 5 // i ∉ J} =>
        MulAction.stabilizer P4
          (CFSG.LieType.CurtisTits.residueChamber hFtyp hFadj J i))
      (C := fun y : P4 => (((y : P4) : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6) ∈
        ⨆ j : Fin 5, G4 ⊓ supp 6 {Fin.castSucc j}ᶜ) hx ?_ ?_ ?_
    · intro i y hy
      have hy' : (y : ↥(Om 6)) ∈
          parabolic ↥(Om 6) genChamber ({4, i.1} : Set (Fin 5)) := by
        rw [hstab i] at hy
        exact Subgroup.mem_subgroupOf.mp hy
      have hy'' : (((y : P4) : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6) ∈
          G4 ⊓ supp 6 {Fin.castSucc i.1}ᶜ := by
        rw [parabolic_genChamber_pair (by simpa [J] using i.2)] at hy'
        exact Subgroup.mem_subgroupOf.mp hy'
      exact Subgroup.mem_iSup_of_mem i.1 hy''
    · exact Subgroup.one_mem _
    · intro a b ha hb
      simpa only [Subgroup.coe_mul] using Subgroup.mul_mem _ ha hb
  intro g hg
  have hgP : (⟨g, supp_le_Om 6 {5}ᶜ hg⟩ : ↥(Om 6)) ∈ P4 := by
    rw [hP4]
    exact Subgroup.mem_subgroupOf.mpr hg
  have hgmem := hmem ⟨⟨g, supp_le_Om 6 {5}ᶜ hg⟩, hgP⟩
  simpa [G4] using hgmem

end CFSG.ClassicalGroups.Orthogonal.SixPlane
