module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Align
import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameGeneration
import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameTriangulable
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Rigid

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open CFSG.LieType.CurtisTits

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

private abbrev frameChamber (j : Fin 5) : FrameVert := stdVert j (Fin.castSucc j)

private theorem card_compl_singleton (i : Fin 6) : ({i}ᶜ : Finset (Fin 6)).card = 5 := by
  rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

private theorem eq_compl_singleton_of_card_eq_five {A : Finset (Fin 6)} (hA : A.card = 5) :
    ∃ i : Fin 6, A = {i}ᶜ := by
  have hc : Aᶜ.card = 1 := by
    rw [Finset.card_compl, hA, Fintype.card_fin]
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  refine ⟨i, ?_⟩
  rw [← hi, compl_compl]

section Family

variable {H : Type u} [Group H]

variable (φ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)

private theorem mem_supp_of_mem_parabolic {J : Set (Fin 5)} (hJ : J.Nonempty)
    (a : parabolic ↥(Om 6) frameChamber J) :
    ((a : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6) ∈ supp 6 {Fin.castSucc hJ.some}ᶜ := by
  have hfix : (a : ↥(Om 6)) ∈ MulAction.stabilizer ↥(Om 6) (frameChamber hJ.some) := by
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_parabolic_iff.mp a.2) hJ.some hJ.some_mem
  exact mem_stabilizer_stdVert_iff.mp hfix

private noncomputable def frameFamily (J : Set (Fin 5)) (hJ : J.Nonempty) :
    parabolic ↥(Om 6) frameChamber J →* H where
  toFun a := φ {Fin.castSucc hJ.some}ᶜ (card_compl_singleton _)
    ⟨((a : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6), mem_supp_of_mem_parabolic hJ a⟩
  map_one' := by
    have h1 : (⟨(((1 : parabolic ↥(Om 6) frameChamber J) : ↥(Om 6)) :
        V 6 ≃ₗ[ZMod 2] V 6), mem_supp_of_mem_parabolic hJ 1⟩ :
        ↥(supp 6 {Fin.castSucc hJ.some}ᶜ)) = 1 := Subtype.ext rfl
    rw [h1, map_one]
  map_mul' a b := by
    have hm : (⟨(((a * b : parabolic ↥(Om 6) frameChamber J) : ↥(Om 6)) :
        V 6 ≃ₗ[ZMod 2] V 6), mem_supp_of_mem_parabolic hJ (a * b)⟩ :
        ↥(supp 6 {Fin.castSucc hJ.some}ᶜ)) =
        (⟨(((a : parabolic ↥(Om 6) frameChamber J) : ↥(Om 6)) :
          V 6 ≃ₗ[ZMod 2] V 6), mem_supp_of_mem_parabolic hJ a⟩ :
          ↥(supp 6 {Fin.castSucc hJ.some}ᶜ)) *
        (⟨(((b : parabolic ↥(Om 6) frameChamber J) : ↥(Om 6)) :
          V 6 ≃ₗ[ZMod 2] V 6), mem_supp_of_mem_parabolic hJ b⟩ :
          ↥(supp 6 {Fin.castSucc hJ.some}ᶜ)) := Subtype.ext rfl
    rw [hm, map_mul]

private theorem frameFamily_apply (J : Set (Fin 5)) (hJ : J.Nonempty)
    (a : parabolic ↥(Om 6) frameChamber J) :
    frameFamily φ J hJ a =
      φ {Fin.castSucc hJ.some}ᶜ (card_compl_singleton _)
        ⟨((a : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6), mem_supp_of_mem_parabolic hJ a⟩ := by
  simp only [frameFamily]
  rfl

private theorem frameFamily_eq_of_val_eq
    (hφ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        φ A hA ⟨g, hgA⟩ = φ B hB ⟨g, hgB⟩)
    {J K : Set (Fin 5)} (hJ : J.Nonempty) (hK : K.Nonempty)
    {a : parabolic ↥(Om 6) frameChamber J} {b : parabolic ↥(Om 6) frameChamber K}
    (h : ((a : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6) =
      ((b : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6)) :
    frameFamily φ J hJ a = frameFamily φ K hK b := by
  have hb' : (⟨((b : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6),
      mem_supp_of_mem_parabolic hK b⟩ : ↥(supp 6 {Fin.castSucc hK.some}ᶜ)) =
      ⟨((a : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6),
        by rw [h]; exact mem_supp_of_mem_parabolic hK b⟩ := Subtype.ext h.symm
  rw [frameFamily_apply, frameFamily_apply, hb']
  exact hφ _ _ _ _ _ (mem_supp_of_mem_parabolic hJ a)
    (by rw [h]; exact mem_supp_of_mem_parabolic hK b)

private noncomputable def parabolicFamily :
    ∀ i : ParabolicIndex (Fin 5),
      ↥(parabolic ↥(Om 6) frameChamber (OrderDual.ofDual i.1)) →* H :=
  fun i => frameFamily φ (OrderDual.ofDual i.1) i.2

private theorem parabolicFamily_compatible
    (hφ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        φ A hA ⟨g, hgA⟩ = φ B hB ⟨g, hgB⟩) :
    IsCompatible (fun i : ParabolicIndex (Fin 5) =>
      parabolic ↥(Om 6) frameChamber (OrderDual.ofDual i.1))
      (parabolicFamily (H := H) φ) := by
  unfold IsCompatible
  intro i j hij x y hxy
  exact frameFamily_eq_of_val_eq φ hφ i.2 j.2
    (congrArg (fun z : ↥(Om 6) => (z : V 6 ≃ₗ[ZMod 2] V 6)) hxy)

end Family

section Extension

variable {H : Type u} [Group H]

variable (φ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)

variable {ψ : ↥(Om 6) →* H}

private theorem psi_apply_parabolic
    (hψ : ∀ (i : ParabolicIndex (Fin 5))
      (x : ↥(parabolic ↥(Om 6) frameChamber (OrderDual.ofDual i.1))),
      ψ x = parabolicFamily (H := H) φ i x)
    {J : Set (Fin 5)} (hJ : J.Nonempty)
    (a : parabolic ↥(Om 6) frameChamber J) :
    ψ a = frameFamily (H := H) φ J hJ a :=
  hψ ⟨OrderDual.toDual J, hJ⟩ a

private theorem psi_inclusion_eq_of_last
    (hφ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        φ A hA ⟨g, hgA⟩ = φ B hB ⟨g, hgB⟩)
    (hψ : ∀ (i : ParabolicIndex (Fin 5))
      (x : ↥(parabolic ↥(Om 6) frameChamber (OrderDual.ofDual i.1))),
      ψ x = parabolicFamily (H := H) φ i x)
    (g : ↥(supp 6 (({5} : Finset (Fin 6))ᶜ))) :
    ψ (Subgroup.inclusion (supp_le_Om 6 (({5} : Finset (Fin 6))ᶜ)) g) =
      φ (({5} : Finset (Fin 6))ᶜ) (card_compl_singleton 5) g := by
  let A5 : Finset (Fin 6) := ({5} : Finset (Fin 6))ᶜ
  let P : Subgroup (V 6 ≃ₗ[ZMod 2] V 6) := supp 6 A5
  let F₁ : ↥P →* H := ψ.comp (Subgroup.inclusion (supp_le_Om 6 A5))
  let F₂ : ↥P →* H := φ A5 (card_compl_singleton 5)
  have hgen : (⨆ j : Fin 5, P ⊓ supp 6 {Fin.castSucc j}ᶜ) = P :=
    iSup_supp_compl_five_inf_eq
  have key : ∀ (y : V 6 ≃ₗ[ZMod 2] V 6) (hy : y ∈ P), F₁ ⟨y, hy⟩ = F₂ ⟨y, hy⟩ := by
    intro y hy
    have hy' : y ∈ ⨆ j : Fin 5, P ⊓ supp 6 {Fin.castSucc j}ᶜ := by
      rw [hgen]
      exact hy
    have h : ∀ hz : y ∈ P, F₁ ⟨y, hz⟩ = F₂ ⟨y, hz⟩ := by
      refine Subgroup.iSup_induction' (fun j : Fin 5 => P ⊓ supp 6 {Fin.castSucc j}ᶜ)
        (C := fun z _ => ∀ hz : z ∈ P, F₁ ⟨z, hz⟩ = F₂ ⟨z, hz⟩) ?_ ?_ ?_ hy'
      · intro j z hz hzP
        have hmem : Subgroup.inclusion (supp_le_Om 6 A5) ⟨z, hzP⟩ ∈
            parabolic ↥(Om 6) frameChamber {j} := by
          rw [parabolic_singleton]
          exact mem_stabilizer_stdVert_iff.mpr hz.2
        calc
          F₁ ⟨z, hzP⟩ = frameFamily (H := H) φ {j} (Set.singleton_nonempty j)
                ⟨_, hmem⟩ := psi_apply_parabolic φ hψ (Set.singleton_nonempty j) ⟨_, hmem⟩
          _ = φ {Fin.castSucc (Set.singleton_nonempty j).some}ᶜ (card_compl_singleton _)
                ⟨z, mem_supp_of_mem_parabolic (Set.singleton_nonempty j) ⟨_, hmem⟩⟩ :=
              frameFamily_apply φ {j} (Set.singleton_nonempty j) ⟨_, hmem⟩
          _ = F₂ ⟨z, hzP⟩ := (hφ A5 {Fin.castSucc (Set.singleton_nonempty j).some}ᶜ
                (card_compl_singleton 5) (card_compl_singleton _) z hzP
                (mem_supp_of_mem_parabolic _ ⟨_, hmem⟩)).symm
      · intro hzP
        rw [show (⟨1, hzP⟩ : ↥P) = 1 from Subtype.ext rfl, map_one, map_one]
      · intro a b ha hb hCa hCb hP
        have ha' : a ∈ P := hgen ▸ ha
        have hb' : b ∈ P := hgen ▸ hb
        have hsplit : (⟨a * b, hP⟩ : ↥P) = ⟨a, ha'⟩ * ⟨b, hb'⟩ := Subtype.ext rfl
        rw [hsplit, map_mul, map_mul, hCa ha', hCb hb']
    exact h hy
  have hEq : F₁ g = F₂ g := key g.val g.2
  calc
    ψ (Subgroup.inclusion (supp_le_Om 6 (({5} : Finset (Fin 6))ᶜ)) g) = F₁ g := rfl
    _ = F₂ g := hEq
    _ = φ (({5} : Finset (Fin 6))ᶜ) (card_compl_singleton 5) g := rfl

private theorem psi_inclusion_eq
    (hφ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        φ A hA ⟨g, hgA⟩ = φ B hB ⟨g, hgB⟩)
    (hψ : ∀ (i : ParabolicIndex (Fin 5))
      (x : ↥(parabolic ↥(Om 6) frameChamber (OrderDual.ofDual i.1))),
      ψ x = parabolicFamily (H := H) φ i x)
    {A : Finset (Fin 6)} (hA : A.card = 5) (g : ↥(supp 6 A)) :
    ψ (Subgroup.inclusion (supp_le_Om 6 A) g) = φ A hA g := by
  obtain ⟨i, rfl⟩ := eq_compl_singleton_of_card_eq_five hA
  by_cases hi : i = (5 : Fin 6)
  · subst i
    rw [psi_inclusion_eq_of_last φ hφ hψ g]
  · have hlast : (Fin.last 5 : Fin 6) = 5 := rfl
    obtain ⟨j, hj⟩ : ∃ j : Fin 5, i = Fin.castSucc j :=
      ⟨i.castPred (by rwa [hlast]),
        (Fin.castSucc_castPred i (by rwa [hlast])).symm⟩
    subst i
    have hmem : Subgroup.inclusion (supp_le_Om 6 {Fin.castSucc j}ᶜ) g ∈
        parabolic ↥(Om 6) frameChamber {j} := by
      rw [parabolic_singleton]
      exact mem_stabilizer_stdVert_iff.mpr g.2
    calc
      ψ (Subgroup.inclusion (supp_le_Om 6 {Fin.castSucc j}ᶜ) g)
          = frameFamily (H := H) φ {j} (Set.singleton_nonempty j) ⟨_, hmem⟩ :=
            psi_apply_parabolic φ hψ (Set.singleton_nonempty j) ⟨_, hmem⟩
      _ = φ {Fin.castSucc (Set.singleton_nonempty j).some}ᶜ (card_compl_singleton _)
            ⟨g.val, mem_supp_of_mem_parabolic (Set.singleton_nonempty j) ⟨_, hmem⟩⟩ :=
          frameFamily_apply φ {j} (Set.singleton_nonempty j) ⟨_, hmem⟩
      _ = φ {Fin.castSucc j}ᶜ hA g :=
          (hφ {Fin.castSucc j}ᶜ {Fin.castSucc (Set.singleton_nonempty j).some}ᶜ hA
            (card_compl_singleton _) g.val g.2
            (mem_supp_of_mem_parabolic _ ⟨_, hmem⟩)).symm

end Extension

theorem existsUnique_hom_of_compatible {H : Type u} [Group H]
    (φ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)
    (hφ : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        φ A hA ⟨g, hgA⟩ = φ B hB ⟨g, hgB⟩) :
    ∃! f : ↥(Om 6) →* H, ∀ (A : Finset (Fin 6)) (hA : A.card = 5) (g : ↥(supp 6 A)),
      f (Subgroup.inclusion (supp_le_Om 6 A) g) = φ A hA g := by
  have hflag : FlagTransitive ↥(Om 6) frameGraph frameChamber :=
    flagTransitive_frameGraph (Fin.castSucc_injective 5)
  have htype : ∀ (g : ↥(Om 6)) (x : FrameVert), FrameVert.typ (g • x) = FrameVert.typ x :=
    fun g x => typ_smul g x
  obtain ⟨ψ, hψ, huniq⟩ :=
    (tits_geometry_isUniversalCompletion (I := Fin 5) (X := FrameVert)
      (typ := FrameVert.typ) (Γ := frameGraph) (G := ↥(Om 6)) (F := frameChamber)
      (fun j => typ_stdVert j (Fin.castSucc j)) htype
      (fun h => (frameGraph_adj_iff.mp h).1)
      (fun g _ _ h => frameGraph_adj_smul g h)
      (fun i j hij => frameGraph_adj_stdVert hij (fun h => hij (Fin.castSucc_injective 5 h)))
      hflag frameGraph_connected triangulable_frameGraph)
      H (parabolicFamily (H := H) φ) (parabolicFamily_compatible φ hφ)
  refine ⟨ψ, ?_, ?_⟩
  · intro A hA g
    exact psi_inclusion_eq φ hφ hψ hA g
  · intro f hf
    apply huniq
    intro i x
    let J : Set (Fin 5) := OrderDual.ofDual i.1
    let hJ : J.Nonempty := i.2
    let A : Finset (Fin 6) := {Fin.castSucc hJ.some}ᶜ
    let g : ↥(supp 6 A) := ⟨((x : ↥(Om 6)) : V 6 ≃ₗ[ZMod 2] V 6),
      mem_supp_of_mem_parabolic hJ x⟩
    have hincl : Subgroup.inclusion (supp_le_Om 6 A) g = (x : ↥(Om 6)) := Subtype.ext rfl
    have hfa : f x = φ A (card_compl_singleton _) g := by
      rw [← hincl]
      exact hf A (card_compl_singleton _) g
    rw [hfa]
    exact (frameFamily_apply φ J hJ x).symm

private theorem exists_pair_discrepancy {H : Type u} [Group H]
    (ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)
    (hinj : ∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA))
    (himg : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
        ∃ (g' : V 6 ≃ₗ[ZMod 2] V 6) (hg'B : g' ∈ supp 6 B), g' ∈ supp 6 A ∧
          ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g', hg'B⟩)
    (htor : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        g ∈ torus 6 Finset.univ → ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g, hgB⟩)
    {A B : Finset (Fin 6)} (hA : A.card = 5) (hB : B.card = 5) :
    ∃ τ ∈ torus 6 (A ∩ B), ∀ (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
      ∀ hg : τ * g * τ⁻¹ ∈ supp 6 B, ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨τ * g * τ⁻¹, hg⟩ := by
  by_cases hAB : A = B
  · subst hAB
    exact ⟨1, (torus 6 _).one_mem, fun g hgA _ _ =>
      congrArg (ψ A hA) (Subtype.ext (by simp))⟩
  have hcard : (A ∩ B).card = 4 := by
    have h1 := Finset.card_union_add_card_inter A B
    have h2 : (A ∪ B).card ≤ 6 := by simpa using Finset.card_le_univ (A ∪ B)
    have h4 : A.card ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_left
    have h3 : (A ∪ B).card ≠ 5 := by
      intro h5
      have hA' : A = A ∪ B := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
      have hB' : B = A ∪ B := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
      exact hAB (hA'.trans hB'.symm)
    omega
  have hsA : supp 6 (A ∩ B) ≤ supp 6 A := supp_mono Finset.inter_subset_left
  have hsB : supp 6 (A ∩ B) ≤ supp 6 B := supp_mono Finset.inter_subset_right
  have hmem : ∀ {x : V 6 ≃ₗ[ZMod 2] V 6}, x ∈ supp 6 A → x ∈ supp 6 B → x ∈ supp 6 (A ∩ B) :=
    fun hxA hxB => by rw [← supp_inf]; exact ⟨hxA, hxB⟩
  have hfwd : ∀ g : ↥(supp 6 (A ∩ B)), ∃ g' : ↥(supp 6 (A ∩ B)),
      ψ A hA (Subgroup.inclusion hsA g) = ψ B hB (Subgroup.inclusion hsB g') := by
    intro g
    obtain ⟨g', hg'B, hg'A, he⟩ := himg A B hA hB g (hsA g.2) (hsB g.2)
    exact ⟨⟨g', hmem hg'A hg'B⟩, he⟩
  have hbwd : ∀ g : ↥(supp 6 (A ∩ B)), ∃ g' : ↥(supp 6 (A ∩ B)),
      ψ B hB (Subgroup.inclusion hsB g) = ψ A hA (Subgroup.inclusion hsA g') := by
    intro g
    obtain ⟨g', hg'A, hg'B, he⟩ := himg B A hB hA g (hsB g.2) (hsA g.2)
    exact ⟨⟨g', hmem hg'A hg'B⟩, he⟩
  choose f hf using hfwd
  choose f' hf' using hbwd
  have injA : Function.Injective fun g : ↥(supp 6 (A ∩ B)) => ψ A hA (Subgroup.inclusion hsA g) :=
    (hinj A hA).comp (Subgroup.inclusion_injective hsA)
  have injB : Function.Injective fun g : ↥(supp 6 (A ∩ B)) => ψ B hB (Subgroup.inclusion hsB g) :=
    (hinj B hB).comp (Subgroup.inclusion_injective hsB)
  have hff' : ∀ g, f (f' g) = g := fun g => injB (by
    change ψ B hB (Subgroup.inclusion hsB (f (f' g))) = ψ B hB (Subgroup.inclusion hsB g)
    rw [← hf (f' g), hf' g])
  have hf'f : ∀ g, f' (f g) = g := fun g => injA (by
    change ψ A hA (Subgroup.inclusion hsA (f' (f g))) = ψ A hA (Subgroup.inclusion hsA g)
    rw [← hf' (f g), hf g])
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => injB (by
    change ψ B hB (Subgroup.inclusion hsB (f (x * y))) =
      ψ B hB (Subgroup.inclusion hsB (f x * f y))
    rw [← hf, map_mul, map_mul, hf, hf, map_mul, map_mul])
  let θ : ↥(supp 6 (A ∩ B)) ≃* ↥(supp 6 (A ∩ B)) :=
    { toFun := f, invFun := f', left_inv := hf'f, right_inv := hff', map_mul' := hmul }
  have hθ : ∀ g : ↥(supp 6 (A ∩ B)), (g : V 6 ≃ₗ[ZMod 2] V 6) ∈ torus 6 (A ∩ B) → θ g = g :=
    fun g hg => injB (by
      change ψ B hB (Subgroup.inclusion hsB (f g)) = ψ B hB (Subgroup.inclusion hsB g)
      rw [← hf g]
      exact htor A B hA hB g (hsA g.2) (hsB g.2) (torus_mono (Finset.subset_univ _) hg))
  obtain ⟨t, ⟨ht, htθ⟩, -⟩ := existsUnique_torus_of_mulEquiv hcard θ hθ
  refine ⟨t, ht, fun g hgA hgB hg => ?_⟩
  have hval : ((f ⟨g, hmem hgA hgB⟩ : ↥(supp 6 (A ∩ B))) : V 6 ≃ₗ[ZMod 2] V 6) =
      t * g * (t : V 6 ≃ₗ[ZMod 2] V 6)⁻¹ :=
    congrArg Subtype.val (htθ ⟨g, hmem hgA hgB⟩)
  exact (hf ⟨g, hmem hgA hgB⟩).trans (congrArg (ψ B hB) (Subtype.ext hval))

theorem exists_hom_of_charts {H : Type u} [Group H]
    (ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)
    (hinj : ∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA))
    (himg : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
        ∃ (g' : V 6 ≃ₗ[ZMod 2] V 6) (hg'B : g' ∈ supp 6 B), g' ∈ supp 6 A ∧
          ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g', hg'B⟩)
    (htor : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        g ∈ torus 6 Finset.univ → ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g, hgB⟩) :
    ∃ (f : ↥(Om 6) →* H) (t : ∀ A : Finset (Fin 6), ↥(supp 6 A)),
      (∀ A, (t A : V 6 ≃ₗ[ZMod 2] V 6) ∈ torus 6 A) ∧
        ∀ (A : Finset (Fin 6)) (hA : A.card = 5) (g : ↥(supp 6 A)),
          f (Subgroup.inclusion (supp_le_Om 6 A) g) = ψ A hA (MulAut.conj (t A) g) := by
  classical
  have hpair : ∀ A B : Finset (Fin 6), ∃ τ ∈ torus 6 (A ∩ B), ∀ (hA : A.card = 5)
      (hB : B.card = 5) (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
        ∀ hg : τ * g * τ⁻¹ ∈ supp 6 B, ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨τ * g * τ⁻¹, hg⟩ := by
    intro A B
    by_cases h : A.card = 5 ∧ B.card = 5
    · obtain ⟨τ, hτ, hτψ⟩ := exists_pair_discrepancy ψ hinj himg htor h.1 h.2
      exact ⟨τ, hτ, fun _ _ => hτψ⟩
    · exact ⟨1, (torus 6 _).one_mem, fun hA hB => absurd ⟨hA, hB⟩ h⟩
  choose τ hτ hψ using hpair
  obtain ⟨t, ht, hcompat⟩ := exists_torus_twist_of_pairs ψ τ hinj hτ hψ
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_compatible
    (fun A hA => (ψ A hA).comp (MulAut.conj (t A)).toMonoidHom) hcompat
  exact ⟨f, t, ht, hf⟩

theorem commute_of_charts {H : Type u} [Group H]
    (ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H)
    (hinj : ∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA))
    (himg : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A), g ∈ supp 6 B →
        ∃ (g' : V 6 ≃ₗ[ZMod 2] V 6) (hg'B : g' ∈ supp 6 B), g' ∈ supp 6 A ∧
          ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g', hg'B⟩)
    (htor : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : V 6 ≃ₗ[ZMod 2] V 6) (hgA : g ∈ supp 6 A) (hgB : g ∈ supp 6 B),
        g ∈ torus 6 Finset.univ → ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g, hgB⟩)
    {A B T T' : Finset (Fin 6)} (hA : A.card = 5) (hB : B.card = 5) (hTA : T ⊆ A)
    (hTB : T' ⊆ B) (hTT : Disjoint T T') {x y : V 6 ≃ₗ[ZMod 2] V 6} (hx : x ∈ supp 6 T)
    (hy : y ∈ supp 6 T') :
    Commute (ψ A hA ⟨x, supp_mono hTA hx⟩) (ψ B hB ⟨y, supp_mono hTB hy⟩) := by
  obtain ⟨f, t, ht, hf⟩ := exists_hom_of_charts ψ hinj himg htor
  have key : ∀ (C S : Finset (Fin 6)) (hC : C.card = 5) (hSC : S ⊆ C)
      {z : V 6 ≃ₗ[ZMod 2] V 6} (hz : z ∈ supp 6 S), ∃ z' ∈ supp 6 S, ∃ hz' : z' ∈ supp 6 C,
        ψ C hC ⟨z, supp_mono hSC hz⟩ = f (Subgroup.inclusion (supp_le_Om 6 C) ⟨z', hz'⟩) := by
    intro C S hC hSC z hz
    have htC : ((t C : V 6 ≃ₗ[ZMod 2] V 6))⁻¹ ∈ torus 6 Finset.univ :=
      (torus 6 _).inv_mem (torus_mono (Finset.subset_univ C) (ht C))
    have hz' : (t C : V 6 ≃ₗ[ZMod 2] V 6)⁻¹ * z * (t C : V 6 ≃ₗ[ZMod 2] V 6) ∈ supp 6 S := by
      simpa using conj_mem_supp_of_mem_torus htC hz
    refine ⟨_, hz', supp_mono hSC hz', ?_⟩
    rw [hf C hC]
    congr 1
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨x', hx'T, hx'A, hxe⟩ := key A T hA hTA hx
  obtain ⟨y', hy'T, hy'B, hye⟩ := key B T' hB hTB hy
  rw [hxe, hye]
  refine Commute.map ?_ f
  exact Subtype.ext (commute_of_mem_supp_of_disjoint hTT hx'T hy'T).eq

end CFSG.ClassicalGroups.Orthogonal.SixPlane
