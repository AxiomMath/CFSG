module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLines
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinComm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp
public import CFSG.GroupTheory.ElemAbelianPlaneAction

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace SpEngine

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_ordered_three_blocks (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) [Finite (V ≃ₗ[F] V)] {k : ℕ}
    (hk : Nat.card ↥A = p ^ k) {H : Subgroup (V ≃ₗ[F] V)} (hAH : A ≤ H)
    (hHH : CFSG.Open.pRank p H ≤ k)
    (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H) (hk3 : 3 ≤ k) :
    ∃ D E G : Hyperplane A p, D ≠ E ∧ D ≠ G ∧ E ≠ G ∧
      blockSpace A D.1 ≠ ⊥ ∧ blockSpace A E.1 ≠ ⊥ ∧ blockSpace A G.1 ≠ ⊥ ∧
      Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A E.1) ∧
      Module.finrank F ↥(blockSpace A E.1) ≤ Module.finrank F ↥(blockSpace A G.1) := by
  obtain ⟨D₁, D₂, D₃, h12, h13, h23, hD1, hD2, hD3⟩ :=
    exists_three_ne_bot_blockSpace A hp hpF hA t ht hk hAH hHH htH hk3
  set d₁ := Module.finrank F ↥(blockSpace A D₁.1) with hd1
  set d₂ := Module.finrank F ↥(blockSpace A D₂.1) with hd2
  set d₃ := Module.finrank F ↥(blockSpace A D₃.1) with hd3
  rcases le_total d₁ d₂ with h12' | h21'
  · rcases le_total d₂ d₃ with h23' | h32'
    · exact ⟨D₁, D₂, D₃, h12, h13, h23, hD1, hD2, hD3, h12', h23'⟩
    · rcases le_total d₁ d₃ with h13' | h31'
      · exact ⟨D₁, D₃, D₂, h13, h12, Ne.symm h23, hD1, hD3, hD2, h13', h32'⟩
      · exact ⟨D₃, D₁, D₂, Ne.symm h13, Ne.symm h23, h12, hD3, hD1, hD2, h31', h12'⟩
  · rcases le_total d₁ d₃ with h13' | h31'
    · exact ⟨D₂, D₁, D₃, Ne.symm h12, h23, h13, hD2, hD1, hD3, h21', h13'⟩
    · rcases le_total d₂ d₃ with h23' | h32'
      · exact ⟨D₂, D₃, D₁, h23, Ne.symm h12, Ne.symm h13, hD2, hD3, hD1,
          h23', h31'⟩
      · exact ⟨D₃, D₂, D₁, Ne.symm h23, Ne.symm h13, Ne.symm h12, hD3, hD2, hD1, h32',
          h21'⟩

theorem exists_elemAbelian_qTorus_pointwiseStab {F V : Type} [Field F] [Finite F]
    [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {B : LinearMap.BilinForm F V}
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (h6 : 6 ≤ Module.finrank F ↥(B.orthogonal U))
    {n q : ℕ} (hq : q.Prime) (hcard : Nat.card F = 2 ^ n)
    (hsplit : q ∣ Nat.card F - 1 ∨ n = 1 ∧ q = 3) :
    ∃ Q : Subgroup (linIsometryGroup B), Q ≤ pointwiseStab (linIsometryGroup B) U ∧
      IsElemAbelian q Q ∧ 3 ≤ CFSG.Open.pRank q Q := by
  classical
  have hU' : (B.restrict (B.orthogonal U)).Nondegenerate :=
    orthogonal_nondegenerate hB hBn hU
  have halt' : (B.restrict (B.orthogonal U)).IsAlt := fun z => hB.self_eq_zero z
  obtain ⟨s, hs, ⟨eSp⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.mclt_exists_bilinIsometryGroup_equiv_statedSp hU' halt'
  have hs3 : 3 ≤ s := by omega
  let e : pointwiseStab (linIsometryGroup B) U ≃* StatedSp s F :=
    (pointwiseStabEquiv hB hU).trans eSp
  have hQ : ∃ Q : Subgroup (pointwiseStab (linIsometryGroup B) U),
      IsElemAbelian q Q ∧ 3 ≤ CFSG.Open.pRank q Q := by
    rcases hsplit with hdvd | ⟨hn1, hq3⟩
    · exact exists_elemAbelian_qTorus_of_mulEquiv hq hs3 e hdvd
    · subst hq3
      subst hn1
      exact exists_elemAbelian_three_of_mulEquiv_card_two (by simpa using hcard) hs3 e
  obtain ⟨Q, hQe, hQ3⟩ := hQ
  refine ⟨Q.map (pointwiseStab (linIsometryGroup B) U).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact CFSG.SectionRank.isElemAbelian_map hQe _
  · have htop : (⊤ : Subgroup Q).map
        ((pointwiseStab (linIsometryGroup B) U).subtype.comp Q.subtype) =
        Q.map (pointwiseStab (linIsometryGroup B) U).subtype := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have hrank : CFSG.Open.pRank q (Q.map (pointwiseStab (linIsometryGroup B) U).subtype) =
        CFSG.Open.pRank q Q := by
      rw [← htop, CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q]
      exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt _
        (fun x y h => Subtype.ext (Subtype.ext h)) ⊤
    rwa [hrank]

theorem spModel165At_holds : SpModel165At := by
  intro ℓ n p q F hField hFinite hChar hcard hm0 h2l hp hp2 hq hq2 hqp hqsplit
  intro A hAe hmax hA3
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdimV : Module.finrank F (Fin ℓ ⊕ Fin ℓ → F) = 2 * ℓ :=
    CFSG.ClassicalGroups.Symplectic.finrank_spSpace
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      subst h0
      simp [CFSG.LocalAnalysis.GLTheoremA.rk2Ord] at hm0
    · exact h0
  have h9 : 9 ≤ Module.finrank F (Fin ℓ ⊕ Fin ℓ → F) := by omega
  have h10 : 10 ≤ Module.finrank F (Fin ℓ ⊕ Fin ℓ → F) := by omega
  have hpF : (p : F) ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h0
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · omega
    · exact hp2 h.symm
  let B : LinearMap.BilinForm F (Fin ℓ ⊕ Fin ℓ → F) :=
    CFSG.RankThree.SubgroupLists.spForm ℓ F
  let H : Subgroup ((Fin ℓ ⊕ Fin ℓ → F) ≃ₗ[F] (Fin ℓ ⊕ Fin ℓ → F)) := linIsometryGroup B
  have hBalt : B.IsAlt := CFSG.RankThree.SubgroupLists.spForm_isAlt
  have hBnd : B.Nondegenerate := CFSG.RankThree.SubgroupLists.spForm_nondegenerate
  let e : StatedSp ℓ F ≃* H := statedSpEquivLinIsometryGroup ℓ F
  let Ã : Subgroup H := A.map e.toMonoidHom
  haveI : Finite ((Fin ℓ ⊕ Fin ℓ → F) ≃ₗ[F] (Fin ℓ ⊕ Fin ℓ → F)) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.finite_linearEquiv_self
  haveI : Finite ↥H := Subtype.finite
  haveI : Fintype ↥Ã := Fintype.ofFinite _
  have hÃe : IsElemAbelian p Ã := CFSG.SectionRank.isElemAbelian_map hAe e.toMonoidHom
  have hÃrank : CFSG.Open.pRank p Ã = CFSG.Open.pRank p A := by
    have htop : (⊤ : Subgroup A).map (e.toMonoidHom.comp A.subtype) = Ã := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, CFSG.SectionRank.pRank_eq_pRank_top_subgroup A]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (e.toMonoidHom.comp A.subtype) (fun x y h => Subtype.ext (e.injective h)) ⊤
  have hÃmax : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p Ã := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H,
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e, hÃrank]
    exact hmax
  have hÃ3 : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [hÃrank]
    exact hA3
  let Ã' : Subgroup ((Fin ℓ ⊕ Fin ℓ → F) ≃ₗ[F] (Fin ℓ ⊕ Fin ℓ → F)) := Ã.map H.subtype
  haveI : Fintype ↥Ã' := Fintype.ofFinite _
  have hÃ'e : IsElemAbelian p Ã' := CFSG.SectionRank.isElemAbelian_map hÃe H.subtype
  have hÃ'rank : CFSG.Open.pRank p Ã' = CFSG.Open.pRank p Ã := by
    have htop : (⊤ : Subgroup Ã).map (H.subtype.comp Ã.subtype) = Ã' := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ã]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (H.subtype.comp Ã.subtype) (fun x y h => Subtype.ext (H.subtype_injective h)) ⊤
  have hÃ'max : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p Ã' := by
    rw [hÃ'rank]
    exact hÃmax
  have hÃ'3 : 3 ≤ CFSG.Open.pRank p Ã' := by
    rw [hÃ'rank]
    exact hÃ3
  obtain ⟨t, ht⟩ := exists_blockRep Ã' hp
  have hÃ'H : Ã' ≤ H := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hBinv : InvariantBilin Ã' B := fun a u v => mem_linIsometryGroup.mp (hÃ'H a.2) u v
  have htH : ∀ D, blockEnd Ã' hp hpF hÃ'e t ht D ∈ H := fun D =>
    mem_linIsometryGroup.mpr (blockEnd_bilinear Ã' hp hpF hÃ'e B hBinv t ht D)
  have hk : Nat.card ↥Ã' = p ^ CFSG.Open.pRank p Ã' :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hÃ'e
  obtain ⟨D, E, G, hDE, hDG, hEG, hD, hE, hG, hDE', hEG'⟩ :=
    exists_ordered_three_blocks (H := H) Ã' hp hpF hÃ'e t ht hk hÃ'H hÃ'max htH hÃ'3
  let data := spBlockLayerData hp hpF hBalt hBnd hÃ'e hBinv hÃ'H hÃ'max rfl ht htH
    hDE hDG hEG hD hE hG hDE' hEG' h9 h10 hn1 hcard hm0
  have hqsplit' : q ∣ Nat.card F - 1 ∨ n = 1 ∧ q = 3 := by
    rcases hqsplit with h | h
    · left; rwa [hcard]
    · exact Or.inr h
  obtain ⟨Fq, hFqle, hFqe, hFq3⟩ :=
    exists_elemAbelian_qTorus_pointwiseStab hBalt hBnd data.hD data.h6D hq hcard hqsplit'
  exact concl165_of_mulEquiv hp hq e
    (concl165_of_spBlockLayerData hBalt hBnd hp hp2 hÃe hn1 hcard hm0 data
      ⟨Fq, hFqle, hFqe, hFq3⟩)

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
