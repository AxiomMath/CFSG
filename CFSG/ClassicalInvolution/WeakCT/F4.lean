module

public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

section Diagram

theorem doubleBondDiagram_f4 :
    DoubleBondDiagram (Tag.cartan .F4) (edgeUp (Tag.rank .F4)) ⟨1, by decide⟩ ⟨2, by decide⟩ where
  adj_ab := by decide
  cartan_ba := by decide
  cartan_ab := by decide
  cartan_adj := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  cartan_nadj := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  neighbour := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide

end Diagram

section Recognition

variable (p f : ℕ) [Fact p.Prime]

theorem weakCT_f4 (hadm : StatedLieAdmissible .F4 0 p f) (hp2 : p ≠ 2) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {X : Type} [Group X]
    (U : Fin 4 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair F W (U 1) (U 2)) :
    ∃ Ψ : (adjointGroup .F4 (GaloisField p f)) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (adjointGroup .F4 (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .F4 0 p f ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField p f)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p f) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Adjoint.f4Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Adjoint.f4Datum (GaloisField p f)).divisible) rfl
  obtain ⟨C, -, hC⟩ := Steinberg.Adjoint.f4_commutatorFormula (GaloisField p f) O
  have hE := Steinberg.Adjoint.f4_chevalleyExtras (GaloisField p f) O C hC
  have hsq : ∀ k : Fin (Tag.rank .F4),
      Steinberg.weylElement (Steinberg.Adjoint.f4Par (GaloisField p f)) k 1 ^ 2 ∈
        Steinberg.Adjoint.torus (τ := .F4) (GaloisField p f) k := by
    intro k
    have h := (Steinberg.Adjoint.f4_isCTGroupDatum (GaloisField p f)).sq_mem k
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
  exact weakCT_doublyLaced e (CurtisTits.curtisTitsConclusion_f4 p f hadm)
    (leviConePresented_f4 _) hE rfl hq h2 doubleBondDiagram_f4
    (Steinberg.Adjoint.f4_steinbergExtras (GaloisField p f)).torus_iSupIndep hsq
    (rootedTree_edgeUp (n := Tag.rank .F4) (by decide)) hroot hpar hb0 hgen hcomm' hpair' hsp

end Recognition

end CFSG.ClassicalInvolution.WeakCT
