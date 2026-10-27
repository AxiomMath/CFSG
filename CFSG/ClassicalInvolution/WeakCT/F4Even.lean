module

public import CFSG.ClassicalInvolution.WeakCT.F4
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  linearBlockStandardPair_subgroupOf symplecticBlockStandardPair_subgroupOf
  linearBlockStandardPair_le_sup symplecticBlockStandardPair_le_sup iSup_subgroupOf_eq_top)

theorem weakCT_f4_even
    (f : ℕ) (hadm : StatedLieAdmissible .F4 0 2 f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F) {X : Type} [Group X]
    (U : Fin 4 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair F W (U 1) (U 2)) :
    ∃ Ψ : (adjointGroup .F4 (GaloisField 2 f)) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (adjointGroup .F4 (GaloisField 2 f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .F4 0 2 f ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 2 f)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField 2 f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField 2 f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card 2 f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Adjoint.f4Datum (GaloisField 2 f)).isFiniteType
    (Dv := (Steinberg.Adjoint.f4Datum (GaloisField 2 f)).divisible) rfl
  obtain ⟨C, -, hC⟩ := Steinberg.Adjoint.f4_commutatorFormula (GaloisField 2 f) O
  have hE := Steinberg.Adjoint.f4_chevalleyExtras (GaloisField 2 f) O C hC
  have hsq : ∀ k : Fin (Tag.rank .F4),
      Steinberg.weylElement (Steinberg.Adjoint.f4Par (GaloisField 2 f)) k 1 ^ 2 ∈
        Steinberg.Adjoint.torus (τ := .F4) (GaloisField 2 f) k := by
    intro k
    have h := (Steinberg.Adjoint.f4_isCTGroupDatum (GaloisField 2 f)).sq_mem k
    rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .F4) k] at h
    exact h
  have hroot : ∃ c : Fin (Tag.rank .F4),
      edgeUp (Tag.rank .F4) ⟨0, by decide⟩ c ∨ edgeUp (Tag.rank .F4) c ⟨0, by decide⟩ :=
    ⟨⟨1, by decide⟩, Or.inl rfl⟩
  have hpar : parentUp (Tag.rank .F4) ⟨2, by decide⟩ = ⟨1, by decide⟩ := rfl
  have hb0 : (⟨2, by decide⟩ : Fin (Tag.rank .F4)) ≠ ⟨0, by decide⟩ := by decide
  have hcomm' : ∀ i j : Fin (Tag.rank .F4), i ≠ j → ¬ edgeUp (Tag.rank .F4) i j →
      ¬ edgeUp (Tag.rank .F4) j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeUp] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hpair' : ∀ i j : Fin (Tag.rank .F4), edgeUp (Tag.rank .F4) i j →
      ¬ (i = (⟨1, by decide⟩ : Fin (Tag.rank .F4)) ∧ j = ⟨2, by decide⟩) →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hn
    simp only [edgeUp] at hij
    refine hpair i j hij fun hi => hn ⟨Fin.ext hi, Fin.ext (by simp only; omega)⟩
  exact CFSG.RankThree.PartOne.CTP.weakCT_doublyLaced_even e
    (CurtisTits.curtisTitsConclusion_f4 2 f hadm) (leviConePresented_f4 _) hE rfl hq
    doubleBondDiagram_f4
    (Steinberg.Adjoint.f4_steinbergExtras (GaloisField 2 f)).torus_iSupIndep hsq
    (rootedTree_edgeUp (n := Tag.rank .F4) (by decide)) hroot hpar hb0 hgen hcomm' hpair' hsp


theorem weakCT_f4_subgroup_even
    (f : ℕ) (hadm : StatedLieAdmissible .F4 0 2 f) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    (U : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair F W (U 1) (U 2)) :
    ∃ Ψ : adjointGroup .F4 (GaloisField 2 f) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 2 f)).rootGroup k).map Ψ =
        U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -, -, -, hblk⟩ := weakCT_f4_even f hadm
    hF hq (U := fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hi1 => by
      obtain ⟨W, hW⟩ := hpair i j hij hi1
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (by
      obtain ⟨W, hW⟩ := hsp
      exact ⟨W.subgroupOf Gs, symplecticBlockStandardPair_subgroupOf
        ((symplecticBlockStandardPair_le_sup hW).trans (sup_le (hUle 1) (hUle 2))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]


end CFSG.ClassicalInvolution.WeakCT

end
