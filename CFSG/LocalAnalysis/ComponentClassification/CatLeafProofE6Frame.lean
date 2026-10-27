module

public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLeviFrame

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem e6_frame_subgroup
    {p f : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .E6 0 p f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ f) {G : Type} [Group G] {U : Fin 6 → Subgroup G}
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin 6 → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 6, edgeE 6 i j → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →* G,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .E6 0 p f := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e6Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E6) (Or.inl rfl)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Minuscule.e6_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField p f)
        Steinberg.Minuscule.posDef_cartan_E6 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e6Data_valid.commC_natAbs (GaloisField p f) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e6Datum_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 6) => by
      have h := (Steinberg.Minuscule.e6Datum_isCTGroupDatum (GaloisField p f)).sq_mem k
      have e := Steinberg.Minuscule.e6Data_valid.weylElement_xm (GaloisField p f) k 1
      rw [e]
      exact h)
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_subgroup e
    (CurtisTits.curtisTitsConclusion_e6 p f hadm) (leviConePresented_e6 _) hD
    (⟨0, by norm_num⟩ : Fin 6) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

end CFSG.ComponentClassification.CatLeafProof
