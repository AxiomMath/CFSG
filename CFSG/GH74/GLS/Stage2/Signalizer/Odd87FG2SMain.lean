module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SChar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Ree (ReeTag)


section Certs


theorem fg2_noPNorm_model {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ r ^ f) (hm : LieModel Y .G2 0 r f) :
    ∀ g : Y, g * g = 1 → g ≠ 1 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup Y,
      IsPGroup p ↥X → X ≠ ⊥ → centralizer ({g} : Set Y) ≤ normalizer (X : Set Y) → False := by
  intro g hg hg1 p _ hp2 X hX hX1 hN
  by_cases hpr : p = r
  · subst hpr
    exact g2_noPNorm_char hr hr2 hm hg hg1 hX hX1 hN
  · exact g2_noPNorm_cross hr hr2 hf h5 hm hg hg1 hp2 hpr hX hX1 hN

theorem fg2_invol_S (hG3 : G2ThreeMax) {Y : Type} [Group Y] [Finite Y] (h : FG2 Y) (α : MulAut Y)
    (hα2 : α * α = 1) (hα1 : α ≠ 1) : InvolFactS α := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := h
  by_cases h3 : p = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h3
    exact Or.inl (Or.inl ⟨hG3 Y hm α hα2 hα1, g2_three_fixOddFree hm α hα2 hα1⟩)
  · have hq5 := five_le_pow_of_ne_three_one hp hp2 hf h3
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
    by_cases hin : α ∈ (MulAut.conj : Y →* MulAut Y).range
    · have hZ : center Y = ⊥ :=
        center_eq_bot_of_mulEquiv_target e CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
      exact Or.inr (noPNorm_of_inner hZ (fg2_noPNorm_model hp hp2 hf hq5 hm) hin hα2 hα1)
    · refine Or.inl (Or.inr ?_)
      have hodd : Odd (Nat.card F) := by
        rw [hcard]
        exact (hp.odd_of_ne_two hp2).pow
      have h5 : 5 ≤ Nat.card F := by rw [hcard]; exact hq5
      let α' : MulAut (Ivk47ab.G2g F) := MulAut.congr e α
      have hα'2 : α' ^ 2 = 1 := by
        rw [sq, ← map_mul, hα2, map_one]
      have hnot : α' ∉ (MulAut.conj : Ivk47ab.G2g F →* MulAut (Ivk47ab.G2g F)).range := by
        rintro ⟨g', hg'⟩
        apply hin
        refine ⟨e.symm g', ?_⟩
        ext y
        have h1 : α' (e y) = g' * e y * g'⁻¹ := by
          have := congrArg (fun σ : MulAut (Ivk47ab.G2g F) => σ (e y)) hg'
          simpa [MulAut.conj_apply] using this.symm
        have h2 : α y = e.symm (α' (e y)) := by
          show α y = e.symm (e (α (e.symm (e y))))
          simp
        rw [MulAut.conj_apply, h2, h1]
        simp [map_mul, map_inv]
      obtain ⟨K, hKle, hKs, hKn, hbad⟩ := g2_outer_involution_bad hodd h5 hα'2 hnot
      let T : Subgroup Y := K.map e.symm.toMonoidHom
      let eT : ↥K ≃* ↥T := K.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
      refine ⟨T, ?_, (MulEquiv.isSimpleGroup_congr eT).1 hKs, ?_,
        fun k hk => hbad k (KindFactor.of_equiv eT hk)⟩
      · rintro _ ⟨k, hk, rfl⟩
        have h2 : e (α (e.symm k)) = k := hKle hk
        show α (e.symm k) = e.symm k
        calc α (e.symm k) = e.symm (e (α (e.symm k))) := by simp
          _ = e.symm k := by rw [h2]
      · obtain ⟨a, b, hab⟩ := hKn
        exact ⟨eT a, eT b, fun h => hab (eT.injective (by simpa [map_mul] using h))⟩

theorem cellFacts_FG2_S (hG3 : G2ThreeMax) (hMult3 : G2ThreeMult) : CellFactsS FG2 where
  iso := fun e h => fg2_iso e h
  mult := fun _ _ _ hL hZ2 hF => fg2_mult hMult3 hL hZ2 hF
  outAbel := fun _ _ _ h => fg2_outAbel h
  invol := fun _ _ _ h α hα2 hα1 => fg2_invol_S hG3 h α hα2 hα1

theorem cell87_FG2_S (hG3 : G2ThreeMax) (hMult3 : G2ThreeMult) :
    Cell87 FG2 :=
  cell87_of_factsS (cellFacts_FG2_S hG3 hMult3)

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
