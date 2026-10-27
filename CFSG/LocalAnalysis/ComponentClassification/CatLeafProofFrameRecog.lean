module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLeviFrame
public import CFSG.ClassicalInvolution.WeakCT.Spin
public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.Timmesfeld.ARS.LinearLevis

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem specialLinear_frame_subgroup {m p f : ℕ} (hadm : StatedLieAdmissible .PSL (m + 1) p f)
    (hm : 3 ≤ m) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {G : Type} [Group G]
    {U : Fin m → Subgroup G}
    (hcomm : ∀ i j : Fin m, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin m → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin m, j.val = i.val + 1 → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : SL(m + 1, F) →* G, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSL (m + 1) p f := by
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_subgroup (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_specialLinear hadm hF hm)
    (leviConePresented_specialLinear m F) (ARS.simplyLacedLevis_specialLinear m F)
    (⟨0, by omega⟩ : Fin m) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

theorem spinPlus_frame_subgroup {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hn3 : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {G : Type} [Group G]
    {U : Fin n → Subgroup G}
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin n → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin n, edgeD n i j → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .POmegaPlus n p f := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum n F hn3).isFiniteType
    (Dv := (Spin.plusDatum n F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin n) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := F) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_subgroup (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_spinPlus hadm hF hn3) (leviConePresented_spinPlus F hn3) hD
    (⟨0, by omega⟩ : Fin n) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

theorem e7_frame_subgroup
    {p f : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .E7 0 p f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ f) {G : Type} [Group G] {U : Fin 7 → Subgroup G}
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin 7 → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 7, edgeE 7 i j → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f)) →* G,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .E7 0 p f := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e7Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Minuscule.e7_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField p f)
        Steinberg.Minuscule.posDef_cartan_E7 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e7Data_valid.commC_natAbs (GaloisField p f) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e7Datum_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 7) => by
      have h := (Steinberg.Minuscule.e7Datum_isCTGroupDatum (GaloisField p f)).sq_mem k
      have e := Steinberg.Minuscule.e7Data_valid.weylElement_xm (GaloisField p f) k 1
      rw [e]
      exact h)
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_subgroup e
    (CurtisTits.curtisTitsConclusion_e7 p f hadm) (leviConePresented_e7 _) hD
    (⟨0, by norm_num⟩ : Fin 7) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

end CFSG.ComponentClassification.CatLeafProof
